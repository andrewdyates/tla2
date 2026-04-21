# Proposal: TLA2 Connectivity Prover

**Date:** 2026-01-06
**Status:** Draft
**Author:** AI Worker (with human direction)

---

## Executive Summary

A compile-time verification system that **mathematically proves** software integration completeness. Uses TLA2's model checking engine to verify that all user-facing functionality is reachable from program entry points, with explicit modeling of external service dependencies.

**Primary Use Case:** Detecting incomplete integration in AI-generated code that passes unit tests but fails at runtime due to disconnected code paths.

---

## Problem Statement

### The AI Integration Testing Problem

AI coding assistants produce code that:
- Has thousands of passing unit tests
- Has high code coverage metrics
- **Fails immediately when launched**

Root cause: Tests verify components in isolation. Nothing verifies that components are actually connected into a working system.

```
AI: "Done! 2,847 tests passing!"
Human: ./app
App: Error: MCP not configured. Crash.

The path from main() to the feature was never wired up.
Tests can't catch this. Tests can be gamed.
```

### What We Need

A **mathematical proof** that:
1. Every public API function is reachable from entry points
2. External dependencies are explicitly declared and accounted for
3. The system works under specified service availability conditions

**Tests can lie. Proofs cannot.**

---

## Prior Art Analysis

### Existing Tools

| Tool | Approach | Gap |
|------|----------|-----|
| **SLAM** (Microsoft) | Model checking for driver API compliance | Focused on API behavioral properties, not integration completeness |
| **SPIN** | LTL model checking for concurrent systems | Requires manual Promela models, not auto-extracted |
| **CBMC** | Bounded model checking for C/C++ | Memory safety focus, not connectivity |
| **Facebook Infer** | Static analysis for bugs | Bug detection, not integration verification |
| **CPAchecker** | Configurable reachability analysis | Research tool, not integration-focused |

### Academic Literature

1. **"Interpolation and SAT-Based Model Checking Revisited: Adoption to Software Verification"** (arXiv)
   - SAT-based model checking for software safety properties
   - Competitive performance on verification tasks
   - *Gap: Safety properties, not integration completeness*

2. **"Petri Nets-based Methods on Automatically Detecting for Concurrency Bugs in Rust Programs"** (arXiv)
   - Petri net reachability analysis for Rust
   - *Gap: Concurrency bugs, not integration paths*

3. **"CPAchecker: A Tool for Configurable Software Verification"** (arXiv)
   - Reachability analysis framework
   - *Gap: General framework, needs specialization for integration*

4. **"A Quantitative Flavour of Robust Reachability"** (arXiv)
   - Quantitative reachability from attacker perspective
   - *Relevant: Introduces quantitative reachability metrics*

### What's Novel

Our proposal combines known techniques in a novel application:

| Aspect | Existing Work | Our Contribution |
|--------|---------------|------------------|
| Model checking | Well-established | Application to integration verification |
| Call graph analysis | Standard compiler technique | Automatic TLA+ model generation |
| Reachability | Graph algorithms | User-goal oriented with service modeling |
| Service dependencies | Ad-hoc analysis | First-class state variables in model |
| Build integration | Separate tools | Compile-time proof requirement |

**The novelty is the APPLICATION, not the technique.** We're applying TLA+ model checking specifically to solve the "AI produces disconnected code" problem.

---

## Design

### Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                     TLA2 Connectivity Prover                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────┐     ┌────────────┐     ┌────────────┐               │
│  │  Rust     │     │   Call     │     │   TLA+     │               │
│  │  Source   │────▶│   Graph    │────▶│   Model    │               │
│  │           │     │ Extraction │     │ Generation │               │
│  └───────────┘     └────────────┘     └────────────┘               │
│        │                                     │                      │
│        │ MIR/HIR                             │ Auto-generated       │
│        ▼                                     ▼                      │
│  ┌───────────┐                        ┌────────────┐               │
│  │  tRust /  │                        │  tla-check │               │
│  │  rustc    │                        │   Engine   │               │
│  └───────────┘                        └────────────┘               │
│                                              │                      │
│                                              ▼                      │
│                                       ┌────────────┐               │
│                                       │   Proof    │               │
│                                       │ Certificate│               │
│                                       └────────────┘               │
│                                              │                      │
│                            ┌─────────────────┼─────────────────┐   │
│                            ▼                 ▼                 ▼   │
│                       ┌────────┐       ┌──────────┐     ┌───────┐ │
│                       │ PASSED │       │  FAILED  │     │ Report│ │
│                       │ Build  │       │  Build   │     │       │ │
│                       │ continues      │  stops   │     │       │ │
│                       └────────┘       └──────────┘     └───────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### Crate Structure

```
crates/
├── tla-extract/              # Call graph extraction
│   ├── src/
│   │   ├── lib.rs
│   │   ├── rustc_plugin.rs   # Hook into rustc MIR
│   │   ├── trust_bridge.rs   # Integration with tRust compiler
│   │   ├── callgraph.rs      # Call graph data structure
│   │   └── patterns.rs       # External dependency detection
│
├── tla-connect/              # Connectivity analysis (NEW)
│   ├── src/
│   │   ├── lib.rs
│   │   ├── model.rs          # Call graph → TLA+ state machine
│   │   ├── properties.rs     # Auto-generated reachability properties
│   │   ├── services.rs       # External service state modeling
│   │   ├── prover.rs         # TLA2 engine integration
│   │   ├── certificate.rs    # Proof certificate generation
│   │   └── report.rs         # Human-readable reports
│
├── tla-check/                # Existing model checker (enhanced)
│   └── src/
│       └── graph_mode.rs     # Optimizations for graph problems
│
└── tla-cli/
    └── src/
        └── commands/
            └── prove_connectivity.rs
```

### The Model

**Input:** Call graph G = (V, E) from compiler

**TLA+ State Machine (auto-generated):**

```tla
---- MODULE Connectivity ----
CONSTANT
    Functions,      \* Set of all functions
    EntryPoints,    \* {main, lib::init, ...}
    Goals,          \* Public API functions
    Services        \* {mcp, postgres, redis, ...}

VARIABLE
    pc,             \* Current function (program counter)
    available       \* Service availability: [Services -> BOOLEAN]

TypeOK ==
    /\ pc \in Functions
    /\ available \in [Services -> BOOLEAN]

Init ==
    /\ pc \in EntryPoints
    /\ available \in [Services -> BOOLEAN]  \* All combinations explored

\* Transitions = call edges from call graph
\* Guarded by service availability where detected
Next ==
    \/ (pc = "main" /\ pc' = "init_services" /\ UNCHANGED available)
    \/ (pc = "init_services" /\ available["mcp"] /\ pc' = "connect_mcp" /\ UNCHANGED available)
    \/ (pc = "connect_mcp" /\ pc' = "start_server" /\ UNCHANGED available)
    \/ ... \* Auto-generated from call graph

\* ═══════════════════════════════════════════════════════════
\* PROPERTIES TO PROVE
\* ═══════════════════════════════════════════════════════════

\* 1. All goals reachable (under some service configuration)
AllGoalsReachable == \A g \in Goals: <>(pc = g)

\* 2. Critical goals reachable even with services down
RobustGoals ==
    \A g \in CriticalGoals:
        () => <>(pc = g)

\* 3. Health check doesn't need external services
HealthCheckIndependent ==
      \* Reachable regardless of service state

\* 4. No dead code
NoDeadCode == \A f \in Functions: <>(pc = f)

====
```

### Service Dependency Modeling

The key insight: **model service availability as state variables**.

```
┌─────────────────────────────────────────────────────────────┐
│ State Space Exploration                                     │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Initial states (all combinations):                        │
│    {mcp: up,   postgres: up,   redis: up  }               │
│    {mcp: up,   postgres: up,   redis: down}               │
│    {mcp: up,   postgres: down, redis: up  }               │
│    {mcp: up,   postgres: down, redis: down}               │
│    {mcp: down, postgres: up,   redis: up  }               │
│    {mcp: down, postgres: up,   redis: down}               │
│    {mcp: down, postgres: down, redis: up  }               │
│    {mcp: down, postgres: down, redis: down}               │
│                                                             │
│  For EACH configuration, check:                            │
│    - Which goals are reachable?                            │
│    - What paths exist?                                     │
│                                                             │
│  Result matrix:                                             │
│    Goal           | mcp | postgres | redis | Reachable?   │
│    ───────────────┼─────┼──────────┼───────┼────────────  │
│    query_data     |  ✓  |    ✓     |   -   |     ✓        │
│    query_data     |  ✗  |    ✓     |   -   |     ✗        │
│    health_check   |  -  |    -     |   -   |     ✓        │
│    export_csv     |  ✓  |    ✓     |   -   |     ✓        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Proof Certificate

```json
{
  "version": "1.0",
  "timestamp": "2026-01-06T14:32:07Z",
  "binary": "target/debug/myapp",
  "commit": "abc123",

  "summary": {
    "functions": 1247,
    "reachable": 1198,
    "connectivity_percent": 96.1,
    "goals_proven": 47,
    "goals_failed": 3,
    "verdict": "FAILED"
  },

  "proofs": [
    {
      "property": "Reachable(main, query_data)",
      "status": "PROVED",
      "witness_path": ["main", "init", "start_server", "handle_request", "query_data"],
      "required_services": ["mcp", "postgres"]
    },
    {
      "property": "Reachable(main, export_csv)",
      "status": "FAILED",
      "reason": "No path exists",
      "nearest_reachable": "handle_request",
      "missing_link": "handle_request → route_export"
    }
  ],

  "service_analysis": {
    "mcp": {
      "gates_functions": 8,
      "critical": true,
      "fallback_detected": false
    },
    "postgres": {
      "gates_functions": 5,
      "critical": true,
      "fallback_detected": true,
      "fallback_location": "src/db/fallback.rs:18"
    }
  }
}
```

### CLI Interface

```bash
# Prove connectivity (build fails if proof fails)
tla prove-connectivity ./target/debug/myapp

# Report only, don't fail build
tla prove-connectivity ./target/debug/myapp --report-only

# Output proof certificate
tla prove-connectivity ./target/debug/myapp --certificate proof.json

# Specify configuration
tla prove-connectivity ./target/debug/myapp --config connectivity.toml

# CI mode with threshold
tla prove-connectivity ./target/debug/myapp --ci --require 100%

# Integration with cargo (via tRust)
cargo build --features tla-connectivity
```

### Configuration

```toml
# connectivity.toml

[proof]
require_all_public_api_reachable = true
require_critical_paths = true
max_dead_code_percent = 5.0

[entry_points]
auto_detect = true
additional = ["lib::init", "lib::run_cli"]

[goals]
auto_detect_pub = true
critical = [
    "serve_request",
    "handle_query",
    "authenticate_user",
]

[services]
# Declare known external dependencies
[services.mcp]
pattern = "mcp::*"
critical = true

[services.postgres]
pattern = "sqlx::*"
critical = true

[services.redis]
pattern = "redis::*"
critical = false  # graceful degradation OK

[pure_functions]
# These should have NO external dependencies
patterns = ["health_check", "format_*", "parse_*"]

[ignore]
# Intentionally unreachable code
functions = ["debug_*", "test_*", "bench_*"]
```

---

## Report Format

```
══════════════════════════════════════════════════════════════════════
 TLA2 CONNECTIVITY PROOF
 Binary: target/debug/myapp
 Functions: 1,247 | Entry points: 3 | Goals: 50
══════════════════════════════════════════════════════════════════════

THEOREM: AllGoalsReachable
  Status: FAILED

  Unreachable goals:
    ✗ export_csv         src/export.rs:45
    ✗ generate_report    src/reports.rs:12
    ✗ admin_dashboard    src/admin.rs:1

  Counterexample for 'export_csv':
    No path exists from any entry point.
    Nearest reachable: handle_request (src/api.rs:89)
    Missing: handle_request never calls route_export()

    Suggested fix:
      Add: handle_request() → route_export() for "/export" routes

──────────────────────────────────────────────────────────────────────

THEOREM: CriticalPathsExist
  Status: PROVED ✓

  Witness for serve_request:
    main → init_server → start_listener → accept → handle_request → serve_request

──────────────────────────────────────────────────────────────────────

SERVICE DEPENDENCY ANALYSIS

  ┌─────────────────┬──────────┬─────────────┬───────────────────────┐
  │ Service         │ Type     │ Gates       │ If Unavailable        │
  ├─────────────────┼──────────┼─────────────┼───────────────────────┤
  │ mcp             │ CRITICAL │ 8 functions │ Core features blocked │
  │ postgres        │ CRITICAL │ 5 functions │ Persistence disabled  │
  │ redis           │ optional │ 3 functions │ Caching disabled      │
  └─────────────────┴──────────┴─────────────┴───────────────────────┘

  ⚠️  health_check requires mcp (UNEXPECTED - should be independent)

──────────────────────────────────────────────────────────────────────

METRICS
  Connectivity:    96.1% (1198/1247 functions reachable)
  Public API:      94.0% (47/50 goals proven)
  Dead code:       49 functions (3.9%)

══════════════════════════════════════════════════════════════════════
BUILD FAILED: 3 public APIs unreachable
══════════════════════════════════════════════════════════════════════
```

---

## Why This Solves the AI Problem

| AI Behavior | Without Proof | With Proof |
|-------------|---------------|------------|
| "2000 tests pass!" | App crashes on start | **PROOF FAILS**: main() can't reach start_server() |
| "All units tested!" | Components disconnected | **PROOF FAILS**: 12 APIs unreachable |
| "Integration test passes!" | Test used mocks | **PROOF FAILS**: real path needs uninitialized service |
| "Bug fixed!" | Broke another path | **PROOF FAILS**: previously reachable goal now unreachable |

**Mathematical proof cannot be gamed.** Either the theorem holds or it doesn't.

---

## Integration with tRust

```
┌─────────────────────────────────────────────────────────────────┐
│  tRust Compilation Pipeline                                     │
│                                                                 │
│  Source → Parse → HIR → MIR ──┬──→ Codegen → Binary            │
│                               │                                 │
│                               ▼                                 │
│                        ┌─────────────┐                         │
│                        │ tla-extract │                         │
│                        └──────┬──────┘                         │
│                               │                                 │
│                               ▼                                 │
│                        ┌─────────────┐                         │
│                        │ tla-connect │                         │
│                        └──────┬──────┘                         │
│                               │                                 │
│                    ┌──────────┴──────────┐                     │
│                    ▼                     ▼                      │
│               PROOF PASSED          PROOF FAILED               │
│               Continue build        Stop compilation           │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Implementation Phases

### Phase 1: Call Graph Extraction (2-3 AI commits)
- [ ] Implement rustc plugin or MIR analysis
- [ ] Extract function → function call edges
- [ ] Detect external dependency patterns (network, file, database)
- [ ] Output call graph in standard format

### Phase 2: TLA+ Model Generation (3-4 AI commits)
- [ ] Convert call graph to TLA+ state machine
- [ ] Model service availability as state variables
- [ ] Generate reachability properties automatically
- [ ] Handle conditional calls (guards)

### Phase 3: Engine Integration (2-3 AI commits)
- [ ] Optimize tla-check for graph reachability problems
- [ ] Implement proof certificate generation
- [ ] Create human-readable report formatter
- [ ] Add CLI commands

### Phase 4: tRust Integration (2-3 AI commits)
- [ ] Embed in tRust compilation pipeline
- [ ] Implement build-fail-on-proof-fail
- [ ] Add configuration file support
- [ ] Integration tests with real codebases

### Total Estimate: 9-13 AI commits (~2-3 hours AI time)

---

## Open Questions

1. **Granularity**: Functions, basic blocks, or statements as states?
2. **Async handling**: How to model async/await call graphs?
3. **Generics**: How to handle monomorphization in call graph?
4. **Dynamic dispatch**: How to handle trait objects and vtables?
5. **Macros**: Analyze before or after macro expansion?

---

## Success Criteria

1. **Correctness**: If proof passes, the app starts and all public APIs are callable
2. **Completeness**: Detects all missing integration paths
3. **Performance**: Proof completes in < 10 seconds for typical codebase
4. **Usability**: Clear error messages with suggested fixes
5. **Integration**: Works seamlessly with cargo/tRust build

---

## References

### Tools
- Microsoft SLAM: https://www.microsoft.com/en-us/research/project/slam/
- SPIN Model Checker: https://spinroot.com/spin/whatispin.html
- CBMC: https://www.cprover.org/cbmc/
- Facebook Infer: https://fbinfer.com/
- CPAchecker: https://cpachecker.sosy-lab.org/

### Academic Papers
- "Interpolation and SAT-Based Model Checking Revisited" (arXiv)
- "Petri Nets-based Methods on Automatically Detecting for Concurrency Bugs in Rust Programs" (arXiv)
- "CPAchecker: A Tool for Configurable Software Verification" (arXiv)
- "A Quantitative Flavour of Robust Reachability" (arXiv)

### Background
- TLA+ and model checking: Leslie Lamport, "Specifying Systems"
- Call graph construction: Grove & Chambers, "A Framework for Call Graph Construction Algorithms" (TOPLAS 2001)

---

## Conclusion

This proposal describes a novel application of TLA+ model checking to solve a real problem: AI-generated code that tests well but doesn't integrate. By proving connectivity at compile time, we can guarantee that if the build passes, the software is actually connected into a working system.

The technique is not new. The application is.
