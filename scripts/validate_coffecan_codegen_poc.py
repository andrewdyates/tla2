#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Validate CoffeeCan codegen/AOT against interpreter and TLC."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent
COFFEECAN_DIR = Path.home() / "tlaplus-examples" / "specifications" / "CoffeeCan"
COFFEECAN_TLA = COFFEECAN_DIR / "CoffeeCan.tla"
TLA2TOOLS_JAR = Path.home() / "tlaplus" / "tla2tools.jar"
COMMUNITY_MODULES_JAR = Path.home() / "tlaplus" / "CommunityModules.jar"
DESCRIPTION = """Validate CoffeeCan codegen/AOT against interpreter and TLC.

This stages a temporary wrapper module around the upstream CoffeeCan example to:
- bind `MaxBeanCount` via INSTANCE substitution
- expose `Init`, `Next`, and an optional type invariant
- drive TLC/tla2 via a generated `.cfg`
- run `tla2 codegen` on the wrapper
- build a standalone Rust BFS harness for the generated state machine

The goal is a like-for-like throughput comparison on the same reachable-state
slice, without the original spec's temporal properties/fairness which the
current AOT path does not model.
"""


@dataclass
class CommandResult:
    command: list[str]
    cwd: str
    elapsed_seconds: float
    returncode: int
    stdout: str
    stderr: str


def run(
    command: list[str],
    *,
    cwd: Path | None = None,
    timeout: int | None = None,
    env: dict[str, str] | None = None,
) -> CommandResult:
    start = time.perf_counter()
    proc = subprocess.run(
        command,
        cwd=str(cwd) if cwd else None,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    elapsed = time.perf_counter() - start
    return CommandResult(
        command=command,
        cwd=str(cwd or Path.cwd()),
        elapsed_seconds=elapsed,
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
    )


def ensure_ok(result: CommandResult, context: str) -> None:
    if result.returncode == 0:
        return
    raise RuntimeError(
        f"{context} failed with exit code {result.returncode}\n"
        f"cwd: {result.cwd}\n"
        f"command: {' '.join(result.command)}\n"
        f"stdout:\n{result.stdout}\n"
        f"stderr:\n{result.stderr}"
    )


def expected_states(bean_count: int) -> int:
    # Sum_{k=1..N} (k + 1) = N(N + 3)/2
    return bean_count * (bean_count + 3) // 2


def parse_tlc_states(output: str) -> int | None:
    match = re.search(
        r"^\s*([0-9,]+) states generated, ([0-9,]+) distinct states found, ([0-9,]+) states left",
        output,
        re.MULTILINE,
    )
    if match:
        return int(match.group(2).replace(",", ""))
    match = re.search(r"([0-9,]+) distinct states found", output)
    if match:
        return int(match.group(1).replace(",", ""))
    return None


def create_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=DESCRIPTION,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--beans", type=int, default=3000)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--skip-interpreter", action="store_true")
    parser.add_argument("--skip-tlc", action="store_true")
    parser.add_argument("--with-invariants", action="store_true")
    parser.add_argument("--keep-temp", action="store_true")
    parser.add_argument("--output-json", type=Path)
    return parser


def stage_wrapper(
    temp_root: Path,
    bean_count: int,
    *,
    with_invariants: bool,
) -> tuple[Path, Path]:
    spec_dir = temp_root / "spec"
    spec_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(COFFEECAN_TLA, spec_dir / "CoffeeCan.tla")

    wrapper_tla = spec_dir / "CoffeeCanCodegenBench.tla"
    wrapper_cfg = spec_dir / "CoffeeCanCodegenBench.cfg"

    invariant_def = ""
    invariant_cfg = ""
    if with_invariants:
        invariant_def = f"\nInvType == can \\in [black : 0..{bean_count}, white : 0..{bean_count}]"
        invariant_cfg = "\nINVARIANTS\n    InvType"

    wrapper_tla.write_text(
        textwrap.dedent(
            f"""\
            ---- MODULE CoffeeCanCodegenBench ----
            VARIABLE can

            INSTANCE CoffeeCan WITH MaxBeanCount <- {bean_count}
            {invariant_def}
            ====
            """
        ),
        encoding="utf-8",
    )
    wrapper_cfg.write_text(
        textwrap.dedent(
            f"""\
            INIT
                Init

            NEXT
                Next
            {invariant_cfg}
            """
        ),
        encoding="utf-8",
    )
    return wrapper_tla, wrapper_cfg


def build_tla2() -> dict[str, Any]:
    cmd = ["cargo", "build", "--profile", "release-canary", "--bin", "tla2"]
    result = run(cmd, cwd=REPO_ROOT)
    ensure_ok(result, "cargo build --profile release-canary --bin tla2")
    return {
        "command": result.command,
        "cwd": result.cwd,
        "elapsed_seconds": round(result.elapsed_seconds, 3),
        "returncode": result.returncode,
    }


def resolve_tla2_bin() -> Path:
    candidates = [
        REPO_ROOT / "target" / "user" / "release-canary" / "tla2",
        REPO_ROOT / "target" / "release-canary" / "tla2",
        REPO_ROOT / "target" / "user" / "release" / "tla2",
        REPO_ROOT / "target" / "release" / "tla2",
    ]
    for path in candidates:
        if path.exists():
            return path
    raise FileNotFoundError(
        "tla2 binary not found; checked: "
        + ", ".join(str(path) for path in candidates)
    )


def generate_rust(tla2_bin: Path, wrapper_tla: Path, generated_rs: Path) -> dict[str, Any]:
    result = run(
        [str(tla2_bin), "codegen", str(wrapper_tla), "--output", str(generated_rs)],
        cwd=REPO_ROOT,
    )
    ensure_ok(result, "tla2 codegen")
    return {
        "command": result.command,
        "cwd": result.cwd,
        "elapsed_seconds": round(result.elapsed_seconds, 3),
        "returncode": result.returncode,
        "stderr": result.stderr.strip(),
    }


def write_aot_project(
    project_dir: Path,
    generated_rs: Path,
    *,
    check_invariants: bool,
) -> None:
    src_dir = project_dir / "src"
    src_dir.mkdir(parents=True, exist_ok=True)
    runtime_path = (REPO_ROOT / "crates" / "tla-runtime").resolve()

    cargo_toml = textwrap.dedent(
        f"""\
        [package]
        name = "coffecan_codegen_bench"
        version = "0.1.0"
        edition = "2021"

        [workspace]

        [dependencies]
        tla-runtime = {{ path = "{runtime_path}" }}
        """
    )
    (project_dir / "Cargo.toml").write_text(cargo_toml, encoding="utf-8")
    shutil.copy2(generated_rs, src_dir / "coffecancodegenbench.rs")

    main_rs = textwrap.dedent(
        """\
        use std::collections::{HashSet, VecDeque};
        use std::ops::ControlFlow;
        use std::time::Instant;

        use tla_runtime::StateMachine;

        mod coffeetcodegenbench_placeholder;
        """
    )
    main_rs = main_rs.replace("coffeetcodegenbench_placeholder", "coffecancodegenbench")
    main_rs += textwrap.dedent(
        """\
        use coffecancodegenbench::CoffeeCanCodegenBench;

        fn main() {
            let machine = CoffeeCanCodegenBench;
            let start = Instant::now();

            let mut seen = HashSet::new();
            let mut queue = VecDeque::new();
            let mut transitions = 0usize;

            let _ = machine.for_each_init(|state| {
                if seen.insert(state.clone()) {
                    queue.push_back(state);
                }
                ControlFlow::Continue(())
            });

            let initial_states = seen.len();
            let mut states_explored = 0usize;

            while let Some(state) = queue.pop_front() {
                states_explored += 1;

                let mut had_successor = false;
                let _ = machine.for_each_next(&state, |succ| {
                    had_successor = true;
                    transitions += 1;
                    if seen.insert(succ.clone()) {
                        queue.push_back(succ);
                    }
                    ControlFlow::Continue(())
                });

                if !had_successor {
                    eprintln!("status=deadlock");
                    eprintln!("state={:?}", state);
                    std::process::exit(3);
                }
            }

            let elapsed = start.elapsed().as_secs_f64();
            println!("status=ok");
            println!("states_explored={states_explored}");
            println!("states_initial={initial_states}");
            println!("states_distinct={}", seen.len());
            println!("transitions={transitions}");
            println!("elapsed_seconds={elapsed:.6}");
            if elapsed > 0.0 {
                println!(
                    "states_per_second={:.3}",
                    states_explored as f64 / elapsed
                );
            }
        }
        """
    )
    if check_invariants:
        main_rs = main_rs.replace(
            "                let mut had_successor = false;\n",
            textwrap.dedent(
                """\
                        if let Some(false) = machine.check_invariant(&state) {
                            eprintln!("status=invariant_violation");
                            eprintln!("state={:?}", state);
                            std::process::exit(2);
                        }

                        let mut had_successor = false;
                """
            ),
        )
    (src_dir / "main.rs").write_text(main_rs, encoding="utf-8")


def parse_key_value_lines(output: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in output.splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        result[key.strip()] = value.strip()
    return result


def validate_summary_counts(summary: dict[str, Any]) -> None:
    expected = summary["expected_states"]
    aot = summary["aot"]
    if aot["states_distinct"] != expected:
        raise RuntimeError(
            f"AOT distinct state count mismatch: expected {expected}, "
            f"got {aot['states_distinct']}"
        )

    interpreter = summary.get("interpreter")
    if interpreter is not None:
        if interpreter["states_found"] != expected:
            raise RuntimeError(
                f"Interpreter state count mismatch: expected {expected}, "
                f"got {interpreter['states_found']}"
            )
        states_distinct = interpreter.get("states_distinct")
        if states_distinct is not None and states_distinct != expected:
            raise RuntimeError(
                f"Interpreter distinct state count mismatch: expected {expected}, "
                f"got {states_distinct}"
            )

    tlc = summary.get("tlc")
    if tlc is not None and tlc["states_found"] != expected:
        raise RuntimeError(
            f"TLC state count mismatch: expected {expected}, "
            f"got {tlc['states_found']}"
        )


def run_aot(project_dir: Path) -> dict[str, Any]:
    build_result = run(["cargo", "build", "--release"], cwd=project_dir)
    ensure_ok(build_result, "AOT cargo build --release")

    run_result = run(["cargo", "run", "--release"], cwd=project_dir)
    ensure_ok(run_result, "AOT cargo run --release")
    parsed = parse_key_value_lines(run_result.stdout)
    return {
        "build_elapsed_seconds": round(build_result.elapsed_seconds, 3),
        "run_elapsed_seconds": round(run_result.elapsed_seconds, 3),
        "status": parsed.get("status"),
        "states_explored": int(parsed["states_explored"]),
        "states_initial": int(parsed["states_initial"]),
        "states_distinct": int(parsed["states_distinct"]),
        "transitions": int(parsed["transitions"]),
        "elapsed_seconds_internal": float(parsed["elapsed_seconds"]),
        "states_per_second": float(parsed["states_per_second"]),
    }


def run_interpreter(
    tla2_bin: Path,
    wrapper_tla: Path,
    wrapper_cfg: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    result = run(
        [
            str(tla2_bin),
            "check",
            str(wrapper_tla),
            "--config",
            str(wrapper_cfg),
            "--workers",
            "1",
            "--force",
            "--output",
            "json",
        ],
        cwd=REPO_ROOT,
        timeout=timeout_seconds,
    )
    ensure_ok(result, "tla2 check wrapper")
    payload = json.loads(result.stdout)
    return {
        "elapsed_seconds_wall": round(result.elapsed_seconds, 3),
        "status": payload["result"]["status"],
        "states_found": payload["statistics"]["states_found"],
        "states_initial": payload["statistics"]["states_initial"],
        "states_distinct": payload["statistics"].get("states_distinct"),
        "transitions": payload["statistics"]["transitions"],
        "time_seconds_reported": payload["statistics"]["time_seconds"],
        "states_per_second": payload["statistics"].get("states_per_second"),
    }


def run_tlc(wrapper_tla: Path, wrapper_cfg: Path, timeout_seconds: int) -> dict[str, Any]:
    classpath = str(TLA2TOOLS_JAR)
    if COMMUNITY_MODULES_JAR.exists():
        classpath += os.pathsep + str(COMMUNITY_MODULES_JAR)

    result = run(
        [
            "java",
            "-Xmx4g",
            "-cp",
            classpath,
            "tlc2.TLC",
            "-config",
            str(wrapper_cfg),
            "-workers",
            "1",
            str(wrapper_tla),
        ],
        cwd=wrapper_tla.parent,
        timeout=timeout_seconds,
    )
    ensure_ok(result, "TLC wrapper run")
    combined = result.stdout + "\n" + result.stderr
    states = parse_tlc_states(combined)
    if states is None:
        raise RuntimeError(
            "Could not parse TLC state count\n"
            f"stdout:\n{result.stdout}\n"
            f"stderr:\n{result.stderr}"
        )
    return {
        "elapsed_seconds_wall": round(result.elapsed_seconds, 3),
        "states_found": states,
    }


def main() -> int:
    parser = create_parser()
    args = parser.parse_args()

    if args.beans <= 0:
        raise SystemExit("--beans must be positive")
    if not COFFEECAN_TLA.exists():
        raise SystemExit(f"CoffeeCan spec not found at {COFFEECAN_TLA}")
    if not TLA2TOOLS_JAR.exists():
        raise SystemExit(f"TLC jar not found at {TLA2TOOLS_JAR}")

    temp_root_path = Path(
        tempfile.mkdtemp(prefix=f"coffecan_codegen_poc_{args.beans}_", dir=REPO_ROOT / "target")
    )
    try:
        wrapper_tla, wrapper_cfg = stage_wrapper(
            temp_root_path,
            args.beans,
            with_invariants=args.with_invariants,
        )
        tla2_build = None
        if not args.skip_build:
            tla2_build = build_tla2()
        tla2_bin = resolve_tla2_bin()

        generated_rs = temp_root_path / "CoffeeCanCodegenBench.rs"
        codegen = generate_rust(tla2_bin, wrapper_tla, generated_rs)

        project_dir = temp_root_path / "aot_project"
        write_aot_project(
            project_dir,
            generated_rs,
            check_invariants=args.with_invariants,
        )
        aot = run_aot(project_dir)

        interpreter = None
        if not args.skip_interpreter:
            interpreter = run_interpreter(
                tla2_bin, wrapper_tla, wrapper_cfg, timeout_seconds=args.timeout
            )

        tlc = None
        if not args.skip_tlc:
            tlc = run_tlc(wrapper_tla, wrapper_cfg, timeout_seconds=args.timeout)

        summary: dict[str, Any] = {
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
            "bean_count": args.beans,
            "expected_states": expected_states(args.beans),
            "with_invariants": args.with_invariants,
            "temp_root": str(temp_root_path),
            "wrapper_tla": str(wrapper_tla),
            "wrapper_cfg": str(wrapper_cfg),
            "tla2_build": tla2_build,
            "codegen": codegen,
            "aot": aot,
            "interpreter": interpreter,
            "tlc": tlc,
        }

        validate_summary_counts(summary)

        if args.output_json:
            args.output_json.write_text(
                json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )

        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0
    finally:
        if args.keep_temp:
            print(f"kept temp dir: {temp_root_path}", file=sys.stderr)
        else:
            shutil.rmtree(temp_root_path, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
