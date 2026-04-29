# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""z4 dependency pin validation: workspace manifest, lock-file rev consistency."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python 3.11+ in normal use
    import tomli as tomllib

from system_health_check_support.common import Check


def _normalize_github_repo_identity(url: str) -> str | None:
    """Normalize common GitHub git URL forms to host/org/repo identity."""
    base = re.split(r"[?#]", url.removeprefix("git+"), maxsplit=1)[0]
    patterns = (
        r"^https://github\.com/([^/]+)/([^/]+?)(?:\.git)?$",
        r"^ssh://git@github\.com/([^/]+)/([^/]+?)(?:\.git)?$",
        r"^git@github\.com:([^/]+)/([^/]+?)(?:\.git)?$",
    )
    for pattern in patterns:
        match = re.match(pattern, base)
        if match:
            owner, repo = match.groups()
            return f"github.com/{owner}/{repo}"
    return None


def _parse_toml_file(path: Path) -> dict[str, Any]:
    return tomllib.loads(path.read_text())


def _parse_lock_source_rev(source: str) -> str | None:
    match = re.search(r"[?&]rev=([0-9a-f]{40})", source)
    return match.group(1) if match else None


def _load_z4_pin_manifests(
    project_root: Path,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None, str | None]:
    cargo_toml_path = project_root / "Cargo.toml"
    if not cargo_toml_path.exists():
        return None, None, "missing Cargo.toml"

    tla_z4_manifest_path = project_root / "crates" / "tla-z4" / "Cargo.toml"
    if not tla_z4_manifest_path.exists():
        return None, None, "missing crates/tla-z4/Cargo.toml"

    try:
        return (
            _parse_toml_file(cargo_toml_path),
            _parse_toml_file(tla_z4_manifest_path),
            None,
        )
    except Exception as exc:  # noqa: BLE001 - health check should report parse failures
        return None, None, f"invalid toml: {exc}"


def _is_z4_workspace_dep(name: str, spec: Any) -> bool:
    return (name == "z4" or name.startswith("z4-")) and isinstance(spec, dict) and spec.get("workspace") is True


def _manifest_workspace_z4_deps(
    manifest: dict[str, Any],
    dep_section_names: tuple[str, ...],
) -> set[str]:
    required: set[str] = set()

    def collect(section: Any) -> None:
        if not isinstance(section, dict):
            return
        for name, spec in section.items():
            if _is_z4_workspace_dep(name, spec):
                required.add(name)

    for section_name in dep_section_names:
        collect(manifest.get(section_name, {}))

    targets = manifest.get("target", {})
    if isinstance(targets, dict):
        for target_manifest in targets.values():
            if not isinstance(target_manifest, dict):
                continue
            for section_name in dep_section_names:
                collect(target_manifest.get(section_name, {}))

    return required


def _workspace_member_manifest_paths(
    cargo_toml: dict[str, Any],
    project_root: Path,
) -> tuple[list[Path] | None, str | None]:
    workspace = cargo_toml.get("workspace", {})
    if not isinstance(workspace, dict):
        return None, "workspace table missing"

    members = workspace.get("members", [])
    if not isinstance(members, list):
        return None, "workspace.members missing"

    manifests: set[Path] = set()
    for member in members:
        if not isinstance(member, str):
            return None, f"invalid workspace member: {member!r}"

        matches = sorted(project_root.glob(member))
        if not matches:
            return None, f"workspace member matched nothing: {member}"

        for match in matches:
            manifest_path = match if match.name == "Cargo.toml" else match / "Cargo.toml"
            if not manifest_path.exists():
                try:
                    rel_path = manifest_path.relative_to(project_root)
                except ValueError:
                    rel_path = manifest_path
                return None, f"missing workspace member manifest: {rel_path}"
            manifests.add(manifest_path)

    return sorted(manifests), None


def _required_workspace_z4_deps(
    cargo_toml: dict[str, Any],
    project_root: Path,
    dep_section_names: tuple[str, ...],
) -> tuple[set[str] | None, str | None]:
    manifest_paths, error = _workspace_member_manifest_paths(cargo_toml, project_root)
    if error is not None:
        return None, error

    assert manifest_paths is not None
    required: set[str] = set()
    for manifest_path in manifest_paths:
        try:
            manifest = _parse_toml_file(manifest_path)
        except Exception as exc:  # noqa: BLE001 - health check should report parse failures
            rel_path = manifest_path.relative_to(project_root)
            return None, f"invalid {rel_path}: {exc}"
        required.update(_manifest_workspace_z4_deps(manifest, dep_section_names))

    return required, None


def _workspace_z4_specs(
    cargo_toml: dict[str, Any], required: set[str]
) -> tuple[dict[str, dict[str, Any]] | None, str | None]:
    workspace_deps = cargo_toml.get("workspace", {}).get("dependencies", {})
    if not isinstance(workspace_deps, dict):
        return None, "workspace.dependencies missing"

    missing = sorted(name for name in required if name not in workspace_deps)
    if missing:
        return None, f"missing deps: {', '.join(missing)}"

    z4_specs: dict[str, dict[str, Any]] = {}
    for name in sorted(required):
        spec = workspace_deps.get(name)
        if not isinstance(spec, dict):
            return None, f"{name} is not a git dependency table"
        z4_specs[name] = spec
    return z4_specs, None


def _validate_workspace_z4_specs(
    z4_specs: dict[str, dict[str, Any]],
    canonical_repo_id: str,
) -> tuple[str | None, str | None]:
    bad_urls = []
    invalid_revs = []
    for name, spec in z4_specs.items():
        git_url = spec.get("git")
        rev = spec.get("rev")
        if not isinstance(git_url, str) or _normalize_github_repo_identity(git_url) != canonical_repo_id:
            bad_urls.append(f"{name}={git_url!r}")
        if not isinstance(rev, str) or re.fullmatch(r"[0-9a-f]{40}", rev) is None:
            invalid_revs.append(f"{name}={rev!r}")

    if bad_urls:
        return None, f"non-canonical z4 url(s): {', '.join(bad_urls)}"
    if invalid_revs:
        return None, f"invalid z4 rev(s): {', '.join(invalid_revs)}"

    revs = {spec["rev"] for spec in z4_specs.values()}
    if len(revs) != 1:
        detail = ", ".join(f"{name}={spec['rev'][:8]}" for name, spec in z4_specs.items())
        return None, f"mismatched revs ({detail})"

    return next(iter(revs)), None


def _load_required_z4_lock_sources(
    project_root: Path,
    required: set[str],
) -> tuple[dict[str, str] | None, str | None]:
    lock_path = project_root / "Cargo.lock"
    if not lock_path.exists():
        return None, "missing Cargo.lock"

    try:
        lock = _parse_toml_file(lock_path)
    except Exception as exc:  # noqa: BLE001 - health check should report parse failures
        return None, f"invalid Cargo.lock: {exc}"

    packages = lock.get("package", [])
    if not isinstance(packages, list):
        return None, "Cargo.lock missing package list"

    lock_sources: dict[str, str] = {}
    for package in packages:
        if not isinstance(package, dict):
            continue
        name = package.get("name")
        source = package.get("source")
        if name in required and isinstance(source, str):
            lock_sources[name] = source

    missing_lock = sorted(name for name in required if name not in lock_sources)
    if missing_lock:
        return None, f"Cargo.lock missing z4 package(s): {', '.join(missing_lock)}"

    return lock_sources, None


def _validate_required_z4_lock_sources(
    lock_sources: dict[str, str],
    expected_rev: str,
    canonical_repo_id: str,
) -> str | None:
    bad_lock_urls = []
    lock_revs = set()
    for name, source in lock_sources.items():
        if _normalize_github_repo_identity(source) != canonical_repo_id:
            bad_lock_urls.append(f"{name}={source!r}")
            continue
        lock_rev = _parse_lock_source_rev(source)
        if lock_rev is None:
            return f"Cargo.lock missing z4 rev for {name}"
        lock_revs.add(lock_rev)

    if bad_lock_urls:
        return f"Cargo.lock has non-canonical z4 source(s): {', '.join(bad_lock_urls)}"
    if len(lock_revs) != 1:
        lock_detail = ", ".join(sorted(r[:8] for r in lock_revs))
        return f"Cargo.lock has multiple z4 revs ({lock_detail})"

    actual_rev = next(iter(lock_revs))
    if expected_rev != actual_rev:
        return f"Cargo.lock rev {actual_rev[:12]} != workspace {expected_rev[:12]}"

    return None


def check_z4_pins(
    project_root: Path,
    *,
    canonical_repo_id: str,
    dep_section_names: tuple[str, ...],
) -> Check:
    cargo_toml, tla_z4_manifest, error = _load_z4_pin_manifests(project_root)
    if error is not None:
        return Check(name="z4_pin:workspace", ok=False, detail=error)

    assert cargo_toml is not None
    assert tla_z4_manifest is not None

    required, error = _required_workspace_z4_deps(cargo_toml, project_root, dep_section_names)
    if error is not None:
        return Check(name="z4_pin:workspace", ok=False, detail=error)

    assert required is not None
    if not required:
        return Check(name="z4_pin:workspace", ok=False, detail="no workspace z4 deps found")

    z4_specs, error = _workspace_z4_specs(cargo_toml, required)
    if error is not None:
        return Check(name="z4_pin:workspace", ok=False, detail=error)

    assert z4_specs is not None
    rev, error = _validate_workspace_z4_specs(z4_specs, canonical_repo_id)
    if error is not None:
        return Check(name="z4_pin:workspace", ok=False, detail=error)

    assert rev is not None
    lock_sources, error = _load_required_z4_lock_sources(project_root, required)
    if error is not None:
        return Check(name="z4_pin:workspace", ok=False, detail=error)

    assert lock_sources is not None
    error = _validate_required_z4_lock_sources(lock_sources, rev, canonical_repo_id)
    if error is not None:
        return Check(name="z4_pin:workspace", ok=False, detail=error)

    return Check(name="z4_pin:workspace", ok=True, detail=f"rev={rev[:12]} ({len(required)} deps)")
