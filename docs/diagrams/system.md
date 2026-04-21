# TLA2 System Architecture

Last updated: 2026-03-21
Covers: All crates in `crates/`

## High-Level Architecture

```mermaid
flowchart TB
    subgraph Input["Input Layer"]
        TLA[".tla files"]
        CFG[".cfg files"]
    end

    subgraph CLI["CLI Layer"]
        CLI_BIN["tla-cli<br/>Command line interface"]
    end

    subgraph Core["Front End (tla-core)"]
        PARSER["Parser<br/>TLA+ → AST"]
        AST["AST<br/>Spanned expressions"]
        SEMANTIC["Semantic Analysis<br/>Name resolution"]
    end

    subgraph Value["Runtime Values (tla-value)"]
        VALUE["Value types<br/>Sets, functions, fingerprint inputs"]
    end

    subgraph TIR["Typed IR (tla-tir)"]
        TIR_LOWER["TIR lowering<br/>Typed, INSTANCE-resolved IR"]
    end

    subgraph Eval["Evaluation (tla-eval)"]
        EVAL["EvalCtx + builtins<br/>TIR expression interpreter"]
    end

    subgraph Check["Model Checking (tla-check)"]
        MC["ModelChecker<br/>BFS exploration"]
        STATE["State storage<br/>ArrayState, checkpoint/resume"]
        FP["Fingerprinting<br/>Seen-set deduplication"]
        ENUM["Enumeration<br/>Successor generation"]
        LIVE["Liveness<br/>Temporal properties"]
        Z4["tla-z4<br/>Symbolic checking (z4)"]
    end

    subgraph Prove["Proof System"]
        PROVE["tla-prove<br/>Proof manager"]
        ZENON["tla-zenon<br/>Tableau prover"]
        CERT["tla-cert<br/>Certificate checker"]
        SMT["tla-smt<br/>Z3 integration"]
    end

    subgraph Generate["Code Generation"]
        CODEGEN["tla-codegen<br/>Rust generation"]
        RUNTIME["tla-runtime<br/>Runtime support"]
    end

    subgraph Tools["Tools"]
        LSP["tla-lsp<br/>Language server"]
        WIRE["tla-wire<br/>Connectivity / wiring verifier"]
    end

    subgraph Accel["Acceleration"]
        JIT["tla-jit<br/>JIT compilation (Cranelift)"]
    end

    TLA --> PARSER
    CFG --> MC
    PARSER --> AST
    AST --> SEMANTIC
    SEMANTIC --> TIR_LOWER
    SEMANTIC --> EVAL
    TIR_LOWER --> EVAL
    EVAL --> VALUE

    CLI_BIN --> MC
    CLI_BIN --> PROVE
    CLI_BIN --> CODEGEN
    CLI_BIN --> JIT

    MC --> ENUM
    ENUM --> EVAL
    ENUM --> STATE
    VALUE --> STATE
    STATE --> FP
    MC --> FP
    MC --> LIVE
    MC --> Z4
    EVAL --> JIT

    PROVE --> ZENON
    PROVE --> SMT
    ZENON --> CERT
    SMT --> CERT

    CODEGEN --> RUNTIME

    LSP --> PARSER
    WIRE --> PARSER
```

## Crate Dependencies

```mermaid
flowchart LR
    subgraph Foundation
        CORE["tla-core"]
        VALUE["tla-value"]
        TIR["tla-tir"]
        EVAL["tla-eval"]
    end

    subgraph Verification
        CHECK["tla-check"]
        Z4["tla-z4"]
        PROVE["tla-prove"]
        ZENON["tla-zenon"]
        CERT["tla-cert"]
        SMT["tla-smt"]
    end

    subgraph Generation
        CODEGEN["tla-codegen"]
        RUNTIME["tla-runtime"]
    end

    subgraph Interface
        CLI["tla-cli"]
        LSP["tla-lsp"]
        WIRE["tla-wire"]
    end

    subgraph Acceleration
        JIT["tla-jit"]
    end

    CORE --> VALUE
    CORE --> TIR
    CORE --> EVAL
    CORE --> CHECK
    VALUE --> TIR
    VALUE --> EVAL
    VALUE --> CHECK
    TIR --> EVAL
    EVAL --> CHECK
    CORE --> Z4
    CORE --> JIT
    CORE --> PROVE
    CORE --> ZENON
    CORE --> CERT
    CORE --> SMT
    CORE --> CODEGEN
    CORE --> LSP
    CORE --> WIRE

    CHECK --> CLI
    Z4 --> CHECK
    PROVE --> CLI
    CODEGEN --> CLI
    JIT --> CLI

    CODEGEN --> RUNTIME
```

## Data Flow: Model Checking

```mermaid
sequenceDiagram
    participant User
    participant CLI as tla-cli
    participant MC as ModelChecker
    participant Enum as Enumerator
    participant State as ArrayState
    participant FP as Fingerprinting

    User->>CLI: tla check spec.tla --config spec.cfg
    CLI->>MC: new(spec, config)
    MC->>Enum: enumerate_init()
    Enum->>State: Create initial states
    State->>FP: Compute fingerprint
    FP-->>MC: Add to seen set

    loop BFS Exploration
        MC->>MC: Pop state from queue
        MC->>Enum: enumerate_successors(state)
        Enum->>State: Generate successor states
        State->>FP: Compute fingerprints
        FP->>MC: Check seen set
        alt New state
            MC->>MC: Add to queue
            MC->>MC: Check invariants
        else Already seen
            MC->>MC: Skip (deduplication)
        end
    end

    MC-->>CLI: CheckResult
    CLI-->>User: Report
```

## Key Components

### tla-core
- **Parser**: Pest-based TLA+ parser
- **AST**: Spanned expression tree with source locations
- **Semantic analysis**: Name resolution, module wiring, and front-end checks

### tla-value / tla-tir / tla-eval
- **tla-value**: Runtime value types, hashing/fingerprinting support, and shared closure/value machinery
- **tla-tir**: Typed, INSTANCE-resolved IR used as the current expression-lowering boundary
- **tla-eval**: `EvalCtx`, builtins, LET/cache logic, and the active `eval_tir(...)` interpreter path

### tla-check
- **ModelChecker**: BFS/parallel state exploration
- **State storage**: `ArrayState`, sparse overlays, and checkpoint/resume state materialization
- **Fingerprinting**: TLC-compatible state fingerprinting for deduplication
- **Enumeration**: Successor generation for explicit-state checking
- **Liveness**: Temporal property checking via tableau + SCC detection

### tla-prove / tla-zenon / tla-cert
- **tla-prove**: High-level proof management
- **tla-zenon**: First-order tableau prover (Zenon algorithm)
- **tla-cert**: Proof certificate verification
- **tla-smt**: SMT-LIB translation for Z3

## Citations

- Workspace crate list: `Cargo.toml:3-19`
- `tla-eval` dependency split: `crates/tla-eval/Cargo.toml:9-11`
- `tla-check` dependency split: `crates/tla-check/Cargo.toml:10-14`
- `tla-cli` dependency on `tla-check`: `crates/tla-cli/Cargo.toml:18-33`
- Current evaluation-stack status: `README.md:572-575`

## Change Log

- 2026-01-14: Initial diagram created by RESEARCHER
- 2026-01-28: Add `tla-jit` and `tla-z4` to diagrams; remove static commit pin
- 2026-03-21: Refresh current-state value / TIR / evaluator layers; remove stale `CompiledGuard` architecture node
