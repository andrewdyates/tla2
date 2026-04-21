# z4-bench — Competition-Standard Benchmarking for Z4

Single CLI for running benchmarks and producing scores using the exact
scoring methods from SAT Competition, SMT-COMP, and CHC-COMP.

## Build

```bash
cargo build --release -p z4-bench
# Also build the solver:
cargo build --release -p z4
```

## Quick Start

```bash
# List all registered evals
z4-bench list

# Run a specific eval (dev timeout, fast)
z4-bench run sat-par2-dev

# Run all evals for one competition domain
z4-bench run --domain chc
z4-bench run --domain smt
z4-bench run --domain sat

# Run all evals with competition-standard timeouts
z4-bench run --all --competition

# Run with median-of-3 for statistical reliability
z4-bench run sat-par2-dev --runs 3

# Compare Z4 against z3 on every benchmark
z4-bench run sat-par2-dev --reference-solver z3

# Score an existing results.json
z4-bench score results.json --scoring sat-comp
z4-bench score results.json --scoring smt-comp --division QF_LIA
z4-bench score results.json --scoring chc-comp --track LIA-Lin

# Print scoring methodology reference
z4-bench standards
```

## Competition Scoring

| Competition | Metric | Standard Timeout |
|-------------|--------|-----------------|
| SAT-COMP | PAR-2 (penalized avg runtime, factor 2) | 5000s |
| SMT-COMP | Lexicographic `<errors, solved, wall-clock, cpu-time>` | 1200s |
| CHC-COMP | Solved count, CPU time tiebreaker | 1800s |

The scoring formula is always competition-standard. The `--competition` flag
only changes the timeout from dev (short) to official.

## Two Modes

- **dev** (default) — short timeouts from eval YAML specs for fast iteration
- **--competition** — official competition timeouts (SAT: 5000s, SMT: 1200s, CHC: 1800s)

## Results Output

Each run writes `results.json` to:

```
evals/results/<eval_id>/<timestamp>/results.json
```

The JSON includes:
- **environment** — timestamp, git commit, z4 version, hostname, OS, arch,
  CPU model, CPU count, memory, load average
- **items** — per-benchmark verdict, wall time, CPU time, expected result
- **settings** — benchmarks directory, timeout, domain, count

Use `--output scorecard.json` to write a combined scorecard across multiple evals.

## Reference Solver Comparison

Compare Z4 against a reference solver (e.g., z3) on the same benchmarks:

```bash
# CLI flag (overrides YAML spec):
z4-bench run sat-par2-dev --reference-solver /usr/local/bin/z3

# Or in eval spec YAML:
# inputs:
#   reference_solver: z3
```

When a `reference_solver` is specified, z4-bench runs the reference solver
on every benchmark after z4 and reports:

- **agree** — both return the same definitive result (sat/unsat)
- **disagree** — both return definitive but different results (potential bug)
- **z4_only** — z4 solved it, reference did not
- **ref_only** — reference solved it, z4 did not

The comparison summary and per-benchmark details are included in `results.json`.

## Eval Registry

Eval specs live in evals/registry/*.yaml. Each spec declares:

```yaml
id: sat-par2-dev
inputs:
  benchmarks_dir: benchmarks/sat/satcomp2024-sample
  timeout_sec: 20
  runs: 3                    # optional: median-of-N runs
  reference_solver: z3       # optional: compare against z3
  suite_dirs:                # optional: restrict to subdirectories
    - QF_BV
    - QF_LIA
```

The domain (`sat`/`smt`/`chc`) and competition scoring method are inferred
from the eval ID prefix. The runner discovers benchmarks recursively from
`benchmarks_dir` and matches file extensions by domain (`.cnf` for SAT,
`.smt2` for SMT/CHC). Optional fields `list_file` and `set_file` restrict
discovery to an explicit benchmark list.

## CLI Reference

```
z4-bench run [EVAL_IDS...] [OPTIONS]
  --all                        Run all registered evals
  --domain <DOMAIN>            Run evals for one domain: sat, smt, chc
  --competition                Use competition-standard timeouts
  --z4 <PATH>                  Path to Z4 binary [default: target/release/z4]
  --timeout <SECS>             Override timeout for all evals
  --runs <N>                   Runs per benchmark, median selected [default: 1]
  --reference-solver <PATH>    Reference solver for comparison (e.g., z3)
  -o, --output <PATH>          Write combined scorecard JSON
  -q, --quiet                  Minimal output

z4-bench score <RESULTS_FILE> --scoring <METHOD> [OPTIONS]
  --scoring <METHOD>   sat-comp | smt-comp | chc-comp
  --timeout <SECS>     Timeout used during the run
  --division <NAME>    SMT-COMP division (e.g., QF_LIA)
  --track <NAME>       CHC-COMP track (e.g., LIA-Lin)
  --standard           Assert competition-standard timeout was used
  --json               Output full score as JSON

z4-bench list        List all registered evals
z4-bench standards   Print scoring methodology reference
```
