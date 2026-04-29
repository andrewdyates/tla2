# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Focused tests for scripts/profile_spec.py worker-aware profiling metadata."""

from __future__ import annotations

import sys
from argparse import Namespace
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))

import benchmark_readonly_value_cache_matrix as readonly_matrix
import perf_harness
import perf_harness_scaling as scaling
import profile_spec
import profile_spec_workflow as workflow


def test_profile_spec_parser_defaults_workers_to_one() -> None:
    parser = profile_spec.create_parser()

    args = parser.parse_args(["MCKVSSafetySmall"])

    assert args.workers == 1, f"expected default workers=1, got {args.workers!r}"


def test_profile_spec_validate_cli_args_rejects_non_positive_workers() -> None:
    parser = profile_spec.create_parser()
    args = Namespace(
        workers=0,
        extra_flags="",
        sample_seconds=None,
        sample_interval_ms=1,
        warmup_seconds=0.0,
    )

    with pytest.raises(SystemExit):
        profile_spec.validate_cli_args(args, parser)


@pytest.mark.parametrize("extra_flags", ["--workers 9", "--workers=9", "-w 9", "-w9"])
def test_profile_spec_validate_cli_args_rejects_worker_override_in_extra_flags(
    extra_flags: str,
) -> None:
    parser = profile_spec.create_parser()
    args = Namespace(
        workers=4,
        extra_flags=extra_flags,
        sample_seconds=None,
        sample_interval_ms=1,
        warmup_seconds=0.0,
    )

    with pytest.raises(SystemExit):
        profile_spec.validate_cli_args(args, parser)


def test_profile_spec_build_commands_use_requested_workers(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    spec = perf_harness.require_spec("MCKVSSafetySmall")
    monkeypatch.setattr(
        perf_harness,
        "validate_spec_files",
        lambda _spec: (
            Path("/tmp/KeyValueStore/MCKVS.tla"),
            Path("/tmp/KeyValueStore/MCKVSSafetySmall.cfg"),
        ),
    )

    _build_command, run_command, _target_dir, _binary_path = profile_spec.build_commands(
        spec,
        cargo_profile="profiling",
        target_dir=str(tmp_path / "manual-target"),
        extra_flags="--max-states 100",
        detailed=True,
        workers=4,
    )

    assert "--workers" in run_command.argv, f"missing --workers in {run_command.argv!r}"
    worker_index = run_command.argv.index("--workers")
    assert run_command.argv[worker_index + 1] == "4", (
        f"expected workers=4 in {run_command.argv!r}"
    )


def test_build_cargo_build_command_targets_tla_cli_package(tmp_path: Path) -> None:
    command = perf_harness.build_cargo_build_command(
        "profiling",
        tmp_path / "target",
    )

    assert "-p" in command.argv, command.argv
    package_index = command.argv.index("-p")
    assert command.argv[package_index + 1] == "tla-cli", command.argv


def test_build_tla2_check_command_records_env_overrides(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec = perf_harness.require_spec("MCKVSSafetySmall")
    monkeypatch.setattr(
        perf_harness,
        "validate_spec_files",
        lambda _spec: (
            Path("/tmp/KeyValueStore/MCKVS.tla"),
            Path("/tmp/KeyValueStore/MCKVSSafetySmall.cfg"),
        ),
    )

    command = perf_harness.build_tla2_check_command(
        spec,
        binary_path=Path("/tmp/tla2"),
        workers=8,
        extra_env={"TLA2_PARALLEL_READONLY_VALUE_CACHES": "1"},
    )

    assert command.env == {"TLA2_PARALLEL_READONLY_VALUE_CACHES": "1"}, (
        f"expected env override to be recorded, got {command.env!r}"
    )
    assert command.argv[:2] == ["/tmp/tla2", "check"], command.argv


def test_run_command_applies_env_overrides(tmp_path: Path) -> None:
    command = perf_harness.CommandSpec(
        argv=[
            sys.executable,
            "-c",
            "import os; print(os.environ.get('TLA2_PARALLEL_READONLY_VALUE_CACHES', 'unset'))",
        ],
        cwd=tmp_path,
        env={"TLA2_PARALLEL_READONLY_VALUE_CACHES": "1"},
    )

    result = perf_harness.run_command(command, timeout=5)

    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "1", result.stdout
    assert result.env_overrides == {"TLA2_PARALLEL_READONLY_VALUE_CACHES": "1"}, (
        f"expected env override to round-trip, got {result.env_overrides!r}"
    )


def test_readonly_matrix_summary_pairs_control_and_treatment() -> None:
    rows = [
        {
            "workers": 1,
            "mode": "control",
            "elapsed_seconds": 12.0,
            "states_found": 3409605,
            "exact_state_parity": True,
            "artifact_dir": "control-1",
        },
        {
            "workers": 1,
            "mode": "treatment",
            "elapsed_seconds": 9.0,
            "states_found": 3409605,
            "exact_state_parity": True,
            "artifact_dir": "treatment-1",
        },
        {
            "workers": 8,
            "mode": "control",
            "elapsed_seconds": 100.0,
            "states_found": 3409605,
            "exact_state_parity": True,
            "artifact_dir": "control-8",
        },
        {
            "workers": 8,
            "mode": "treatment",
            "elapsed_seconds": 102.0,
            "states_found": 3409605,
            "exact_state_parity": True,
            "artifact_dir": "treatment-8",
        },
    ]

    summary = readonly_matrix.summarize_rows(rows)

    assert summary["worker_pairs"] == 2, f"expected 2 worker pairs, got {summary!r}"
    assert summary["parity_fail"] == 0, f"expected no parity failures, got {summary!r}"
    assert summary["pair_rows"][0]["delta_seconds"] == -3.0, summary["pair_rows"]
    assert summary["pair_rows"][1]["treatment_over_control"] == pytest.approx(1.02), (
        f"expected treatment/control ratio near 1.02, got {summary['pair_rows']!r}"
    )


def test_run_tla2_check_forwards_env_override(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    spec = perf_harness.require_spec("MCKVSSafetySmall")
    captured: dict[str, object] = {}

    def fake_build_tla2_check_command(
        _spec,
        *,
        binary_path: Path,
        extra_env: dict[str, str] | None,
        workers: int,
        profile_enum: bool,
        profile_eval: bool,
    ) -> perf_harness.CommandSpec:
        captured["binary_path"] = binary_path
        captured["extra_env"] = extra_env
        captured["workers"] = workers
        captured["profile_enum"] = profile_enum
        captured["profile_eval"] = profile_eval
        return perf_harness.CommandSpec(
            argv=["/tmp/tla2", "check"],
            cwd=tmp_path,
            env=extra_env,
        )

    monkeypatch.setattr(
        perf_harness,
        "build_tla2_check_command",
        fake_build_tla2_check_command,
    )
    monkeypatch.setattr(
        perf_harness,
        "run_command",
        lambda _command, timeout=None: perf_harness.CommandResult(
            argv=["/tmp/tla2", "check"],
            cwd=str(tmp_path),
            returncode=0,
            elapsed_seconds=1.25,
            stdout="States found: 3409605\nTime: 1.250s\n",
            stderr="",
            env_overrides={"TLA2_PARALLEL_READONLY_VALUE_CACHES": "1"},
        ),
    )

    result = scaling.run_tla2_check(
        spec,
        workers=8,
        timeout=60,
        output_dir=tmp_path / "artifacts",
        tla2_bin=Path("/tmp/tla2"),
        extra_env={"TLA2_PARALLEL_READONLY_VALUE_CACHES": "1"},
    )

    assert captured["binary_path"] == Path("/tmp/tla2"), (
        f"expected binary path to round-trip, got {captured!r}"
    )
    assert captured["extra_env"] == {"TLA2_PARALLEL_READONLY_VALUE_CACHES": "1"}, (
        f"expected extra_env to be forwarded, got {captured!r}"
    )
    assert captured["workers"] == 8, f"expected workers=8, got {captured!r}"
    assert captured["profile_enum"] is False, (
        f"expected profile_enum=False for scaling runs, got {captured!r}"
    )
    assert captured["profile_eval"] is False, (
        f"expected profile_eval=False for scaling runs, got {captured!r}"
    )
    assert result.states_found == 3409605, result


def test_build_summary_records_worker_count() -> None:
    spec = perf_harness.require_spec("MCKVSSafetySmall")
    build_result = perf_harness.CommandResult(
        argv=["cargo", "build"],
        cwd=str(perf_harness.REPO_ROOT),
        returncode=0,
        elapsed_seconds=1.5,
        stdout="",
        stderr="",
    )
    run_result = perf_harness.CommandResult(
        argv=["/tmp/profile/tla2", "check", "--workers", "4"],
        cwd=str(perf_harness.REPO_ROOT),
        returncode=0,
        elapsed_seconds=2.25,
        stdout="States found: 8\nTransitions: 13\nTime: 2.250s\n",
        stderr="",
    )

    summary = profile_spec.build_summary(
        spec,
        workers=4,
        timestamp="2026-03-16T123456",
        timeout=60,
        extra_flags="",
        cargo_profile="profiling",
        target_dir=Path("/tmp/target"),
        binary_path=Path("/tmp/target/profiling/tla2"),
        build_result=build_result,
        run_result=run_result,
        sample_meta={"artifact": "reports/perf/sample.txt"},
    )

    assert summary["workers"] == 4, f"expected workers=4, got {summary['workers']!r}"


def test_parse_profiling_output_preserves_zero_transitions() -> None:
    summary = perf_harness.parse_profiling_output(
        "States found: 8\nTransitions: 0\nTime: 2.250s\n",
        "",
    )

    assert summary["states_found"] == 8, summary
    assert summary["transitions"] == 0, summary


def test_parse_profiling_output_uses_final_transition_line() -> None:
    summary = perf_harness.parse_profiling_output(
        "States found: 8\nTransitions: 13\nTime: 2.250s\nTransitions: 0\n",
        "",
    )

    assert summary["transitions"] == 0, summary


def test_parse_profiling_output_uses_final_states_found_line() -> None:
    summary = perf_harness.parse_profiling_output(
        "States found: 999\nTransitions: 13\nTime: 2.250s\nStates found: 8\n",
        "",
    )

    assert summary["states_found"] == 8, summary


def test_parse_tlc_states_uses_final_full_summary_line() -> None:
    generated, distinct = scaling.parse_tlc_states(
        "\n".join(
            [
                "10 states generated, 8 distinct states found, 0 states left on queue.",
                "999 states generated, 123 distinct states found, 0 states left on queue.",
            ]
        )
    )

    assert generated == 999
    assert distinct == 123


def test_parse_tlc_states_ignores_embedded_summary_text() -> None:
    generated, distinct = scaling.parse_tlc_states(
        "prefix 10 states generated, 8 distinct states found, 0 states left on queue."
    )

    assert generated is None
    assert distinct is None


def test_parse_tlc_states_accepts_commas_and_leading_whitespace() -> None:
    generated, distinct = scaling.parse_tlc_states(
        "  1,000 states generated, 999 distinct states found, 0 states left"
    )

    assert generated == 1000
    assert distinct == 999


def test_run_tlc_check_records_generation_count_without_transition_count(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    spec = perf_harness.require_spec("MCKVSSafetySmall")
    fake_jar = tmp_path / "tla2tools.jar"
    fake_jar.write_text("fake jar", encoding="utf-8")
    captured: dict[str, object] = {}

    monkeypatch.setattr(scaling, "TLC_JAR", fake_jar)
    monkeypatch.setattr(
        perf_harness,
        "validate_spec_files",
        lambda _spec: (
            Path("/tmp/KeyValueStore/MCKVS.tla"),
            Path("/tmp/KeyValueStore/MCKVSSafetySmall.cfg"),
        ),
    )

    def fake_run_command(
        command: perf_harness.CommandSpec,
        timeout: int | float | None = None,
    ) -> perf_harness.CommandResult:
        captured["command"] = command
        captured["timeout"] = timeout
        return perf_harness.CommandResult(
            argv=command.argv,
            cwd=str(command.cwd),
            returncode=0,
            elapsed_seconds=2.5,
            stdout=(
                "999 states generated, 123 distinct states found, "
                "0 states left on queue.\n"
            ),
            stderr="",
        )

    monkeypatch.setattr(perf_harness, "run_command", fake_run_command)

    result = scaling.run_tlc_check(
        spec,
        workers=1,
        timeout=60,
        output_dir=tmp_path / "artifacts" / "tlc-run7",
    )
    result_dict = result.to_dict()

    assert captured["timeout"] == 60
    assert result.states_found == 123, result
    assert result.distinct_states == 123, result
    assert result.transitions is None, result
    assert result.states_generated == 999, result
    assert result_dict["run_index"] == 7, result_dict
    assert result_dict["transitions"] is None, result_dict
    assert result_dict["states_generated"] == 999, result_dict


def test_build_metadata_records_worker_count(tmp_path: Path) -> None:
    config = workflow.RunConfig(
        spec=perf_harness.require_spec("MCKVSSafetySmall"),
        workers=4,
        timeout=60,
        extra_flags="",
        cargo_profile="profiling",
        output_dir=tmp_path / "out",
        target_dir=tmp_path / "target",
        binary_path=tmp_path / "target" / "profiling" / "tla2",
        build_command=perf_harness.CommandSpec(
            argv=["cargo", "build", "--profile", "profiling"],
            cwd=perf_harness.REPO_ROOT,
        ),
        run_command=perf_harness.CommandSpec(
            argv=["/tmp/tla2", "check", "--workers", "4"],
            cwd=perf_harness.REPO_ROOT,
        ),
        sample_seconds=None,
        sample_interval_ms=1,
        warmup_seconds=0.0,
        timestamp="2026-03-16T123456",
    )
    build_result = perf_harness.CommandResult(
        argv=["cargo", "build"],
        cwd=str(perf_harness.REPO_ROOT),
        returncode=0,
        elapsed_seconds=1.5,
        stdout="",
        stderr="",
    )

    build_json = workflow.build_metadata(config, build_result)

    assert build_json["workers"] == 4, f"expected workers=4, got {build_json['workers']!r}"


def test_write_command_log_records_configured_worker_count(tmp_path: Path) -> None:
    workflow.write_command_log(
        tmp_path,
        workers=4,
        build_command=perf_harness.CommandSpec(
            argv=["cargo", "build", "--profile", "profiling"],
            cwd=perf_harness.REPO_ROOT,
        ),
        run_command=perf_harness.CommandSpec(
            argv=["/tmp/tla2", "check", "--workers", "4", "--force", "--workers", "9"],
            cwd=perf_harness.REPO_ROOT,
        ),
        sample_meta=None,
    )

    command_log = (tmp_path / "command.txt").read_text(encoding="utf-8")

    assert command_log.splitlines()[0] == "workers: 4", command_log
