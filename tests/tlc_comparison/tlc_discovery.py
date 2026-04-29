# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import os
import shutil
from dataclasses import dataclass
from pathlib import Path

ENV_TLC_BIN = "TLC_BIN"
ENV_TLA2TOOLS_JAR = "TLA2TOOLS_JAR"
ENV_COMMUNITY_MODULES = "COMMUNITY_MODULES"

# Deprecated alias (older tla2 scripts used this name). Prefer `TLA2TOOLS_JAR`.
ENV_TLC_JAR_ALIAS = "TLC_JAR"


@dataclass(frozen=True)
class TlcBackend:
    """How to invoke TLC.

    - kind="cli": run `tlc` (or a wrapper) directly.
    - kind="java": run `java -cp <jar> tlc2.TLC ...`.
    """

    kind: str
    tlc_bin: Path | None
    tla2tools_jar: Path | None
    community_modules_jar: Path | None = None

    def describe(self) -> str:
        if self.kind == "cli":
            return f"cli:{self.tlc_bin}"
        return f"java:{self.tla2tools_jar}"

    def build_classpath(self) -> str:
        """Build classpath string including CommunityModules if available."""
        if self.tla2tools_jar is None:
            return ""
        cp = str(self.tla2tools_jar)
        if self.community_modules_jar is not None and self.community_modules_jar.exists():
            cp += os.pathsep + str(self.community_modules_jar)
        return cp


def _env_path(name: str) -> Path | None:
    raw = os.environ.get(name)
    if not raw:
        return None
    return Path(raw).expanduser()


def _default_tlaplus_jar() -> Path | None:
    jar = Path.home() / "tlaplus" / "tla2tools.jar"
    return jar if jar.exists() else None


def _default_community_modules() -> Path | None:
    """Discover CommunityModules.jar in standard location."""
    cm = Path.home() / "tlaplus" / "CommunityModules.jar"
    return cm if cm.exists() else None


def _discover_community_modules() -> Path | None:
    """Discover CommunityModules.jar from env var or default location."""
    return _env_path(ENV_COMMUNITY_MODULES) or _default_community_modules()


def discover_tlc_backend(*, allow_default_tlaplus: bool = True) -> TlcBackend:
    """Discover a TLC backend.

    Priority (matching z4-tla-bridge):
    1) `TLC_BIN` env var
    2) `tlc` on PATH
    3) `TLA2TOOLS_JAR` env var

    Compatibility:
    - `TLC_JAR` is supported as an alias for `TLA2TOOLS_JAR`.
    - If no env vars are set, `~/tlaplus/tla2tools.jar` is used when present.

    CommunityModules:
    - `COMMUNITY_MODULES` env var overrides the default location.
    - Default: `~/tlaplus/CommunityModules.jar` if it exists.
    - For Java mode, use `build_classpath()` to get classpath with CommunityModules.
    - For CLI mode, CommunityModules must be configured in the wrapper script.
    """

    community_modules = _discover_community_modules()

    tlc_bin = _env_path(ENV_TLC_BIN)
    if tlc_bin is not None:
        return TlcBackend(
            kind="cli", tlc_bin=tlc_bin, tla2tools_jar=None,
            community_modules_jar=community_modules
        )

    which_tlc = shutil.which("tlc")
    if which_tlc is not None:
        return TlcBackend(
            kind="cli", tlc_bin=Path(which_tlc), tla2tools_jar=None,
            community_modules_jar=community_modules
        )

    jar = _env_path(ENV_TLA2TOOLS_JAR) or _env_path(ENV_TLC_JAR_ALIAS)
    if jar is None and allow_default_tlaplus:
        jar = _default_tlaplus_jar()

    if jar is not None:
        return TlcBackend(
            kind="java", tlc_bin=None, tla2tools_jar=jar,
            community_modules_jar=community_modules
        )

    raise RuntimeError(
        "failed to discover a TLC runner; set `TLC_BIN` or `TLA2TOOLS_JAR` "
        "(compat: `TLC_JAR`), or install `tlc` on PATH"
    )

