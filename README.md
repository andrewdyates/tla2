# TLA2

**Author:** Andrew Yates (andrewyates.name@gmail.com)
**Version:** 0.9.0
**License:** Apache-2.0

TLA2 is a ground-up Rust reimplementation of the TLA+ formal verification toolchain. It targets full parity with TLC (the standard model checker) and adds symbolic verification, JIT compilation, code generation, and hardware model checking in a single binary. No JVM required.

Every state count matches TLC exactly across all applicable specs from the [tlaplus/Examples](https://github.com/tlaplus/Examples) suite. TLA2 prefers crashing over producing an incorrect verification result.

## Installation and Quick Start

```bash
cargo build --release -p tla-cli

# Model check a spec
./target/release/tla2 check MySpec.tla

# Parallel BFS (4 workers)
./target/release/tla2 check MySpec.tla --workers 4

# Install globally
cargo install --path crates/tla-cli
```

## Usage

```bash
# Model checking
tla2 check MySpec.tla                      # Explicit-state BFS
tla2 check MySpec.tla --workers 4           # Parallel BFS with work stealing
tla2 check MySpec.tla --bmc 20             # Bounded model checking (symbolic, via z4)
tla2 check MySpec.tla --output json         # Structured output

# Other tools
tla2 simulate MySpec.tla                    # Random simulation
tla2 parse MySpec.tla                       # Parse and type-check
tla2 codegen MySpec.tla -o spec.rs          # Generate Rust from TLA+
tla2 lsp                                    # Language server
tla2 diagnose                               # Compare against TLC baselines

# Hardware model checking
tla2 aiger circuit.aig --timeout 60         # AIGER (IC3/PDR + BMC + k-induction)
tla2 btor2 design.btor2 --timeout 60        # BTOR2 (CHC translation via z4)
```

### Library

```toml
[dependencies]
tla-check = { git = "https://github.com/andrewdyates/tla2" }
```

`tla-core` provides parsing and AST. `tla-eval` provides the expression evaluator. `tla-z4` provides symbolic verification via [z4](https://github.com/andrewdyates/z4).

## Why TLA2

**No JVM.** TLC requires a JVM, ships as a 100MB jar, and takes ~2s to start. TLA2 is a single binary with ~10ms startup. This matters for CI pipelines, editor integrations, and embedded use.

**Symbolic + explicit-state.** TLA2 is the only TLA+ tool that combines explicit-state BFS and symbolic model checking (BMC, IC3/PDR via z4) in a single run. The fused orchestrator dynamically routes actions to the best engine based on branching factor.

**Hardware verification.** AIGER and BTOR2 frontends bring IC3/PDR to hardware model checking, targeting [HWMCC](http://fmv.jku.at/hwmcc/). The AIGER engine implements a 16-config IC3/PDR portfolio with domain-restricted SAT, drawing from [rIC3](https://github.com/gipsyh/rIC3) (HWMCC'25 #2, 274/330 safety). Backed by z4-sat (pure Rust CDCL).

**Code generation.** `tla2 codegen` translates TLA+ specs to Rust with INSTANCE expansion, optional Kani verification harnesses, and proptest property tests.

## Architecture

~760K lines of Rust across 21 crates:

| Layer | Crates | Purpose |
|-------|--------|---------|
| Frontend | `tla-core`, `tla-tir`, `tla-value` | Parser, typed IR, value types |
| Evaluation | `tla-eval` | TIR tree-walking interpreter |
| Model checking | `tla-check`, `tla-mc-core` | BFS, liveness (tableau + SCC), symmetry, CDEMC orchestrator |
| Symbolic | `tla-z4` | BMC, IC3/PDR, k-induction via z4 |
| Compilation | `tla-jit`, `tla-llvm`, `tla-codegen`, `tla-runtime` | Cranelift JIT, LLVM AOT, TLA+ to Rust codegen |
| Proofs | `tla-zenon`, `tla-cert` | First-order tableau prover, proof certificates |
| Hardware | `tla-aiger`, `tla-btor2` | AIGER/BTOR2 model checking (HWMCC) |
| Analysis | `tla-concurrent`, `tla-petri`, `pnml-tools`, `tla-gpu` | Concurrency analysis, Petri nets, GPU fingerprinting |
| Tooling | `tla-lsp`, `tla-cli` | Language server, CLI |

## Acknowledgments

TLA2 builds on decades of research in model checking, temporal logic, and formal verification:

[TLC](https://github.com/tlaplus/tlaplus) (Yu, Manolios, Lamport; MIT) — Reference model checker.
[TLAPM](https://github.com/tlaplus/tlapm) (Chaudhuri, Doligez, Lamport, Merz; BSD) — TLA+ proof system architecture.
[Zenon](https://github.com/zenon-prover/zenon) (Bonichon, Delahaye, Doligez; BSD) — First-order tableau prover; `tla-zenon` is a Rust port.
[rIC3](https://github.com/gipsyh/rIC3) (Yuheng Su; GPL-3.0) — Primary reference for `tla-aiger`.
[IC3ref](https://github.com/arbrad/IC3ref) (Aaron Bradley; MIT) — Original IC3 reference.
[ABC](https://github.com/berkeley-abc/abc) (Brayton, Mishchenko) — AIG preprocessing.
[Apalache](https://github.com/informalsystems/apalache) (Konnov, Kukovec, Tran) — Symbolic model checking for TLA+.
[z4](https://github.com/andrewdyates/z4) (Yates; Apache-2.0) — SAT/SMT/CHC backend.
[Cranelift](https://github.com/bytecodealliance/wasmtime/tree/main/cranelift) (Bytecode Alliance; Apache-2.0) — JIT backend.

For the complete bibliography, see [`docs/REFERENCES.md`](docs/REFERENCES.md).

## Citation

```bibtex
@software{tla2,
  author = {Yates, Andrew},
  title = {TLA2: TLA+ Formal Verification Toolchain in Rust},
  url = {https://github.com/andrewdyates/tla2},
  version = {0.9.0},
  year = {2025--2026}
}
```

## Development

```bash
cargo test --workspace                        # Run all tests
cargo check --all-targets                     # Compile check
cargo clippy --all-targets                    # Lint
cargo build --release --features z4           # With symbolic checking (z4)
cargo build --release --features jit          # With Cranelift JIT
```

## License

Apache License 2.0. See [`LICENSE`](LICENSE).

## Author

Andrew Yates
