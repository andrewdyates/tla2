# TLA2

TLA2 is a Rust workspace for TLA+ parsing, checking, simulation, code generation, language-server tooling, and hardware-oriented checking frontends.

- **Author:** Andrew Yates
- **Version:** 0.9.1
- **License:** Apache-2.0

<!-- dscan:template public_readme_v1 -->
<!--
cite:
- Cargo.toml
- Cargo.lock
- crates/tla-cli/Cargo.toml
- crates/tla-core/Cargo.toml
- crates/tla-check/Cargo.toml
- crates/tla-aiger/Cargo.toml
- crates/tla-btor2/Cargo.toml
- LICENSE
- docs/REFERENCES.md
- docs/diagrams/system.md
-->

The repository publishes the `tla2` and `tla` command-line binaries from `crates/tla-cli` and library crates for parsing, values, model checking, symbolic integration, code generation, and runtime support. The workspace uses public git dependencies for sibling projects such as `z4` and records upstream research and software attributions in `docs/REFERENCES.md`.

## Installation

TLA2 builds with the Rust toolchain declared in `Cargo.toml`. Clone the public repository and build the CLI from the workspace root:

```bash
git clone https://github.com/andrewdyates/tla2
cd tla2
cargo build --release -p tla-cli
```

The built binaries are written under `target/release/`:

```bash
./target/release/tla2 --help
./target/release/tla --help
```

To install from a local checkout:

```bash
cargo install --path crates/tla-cli
```

## Quick Start

Run the checker against a TLA+ module:

```bash
tla2 check MySpec.tla
```

Run the same checker with explicit worker count and JSON output:

```bash
tla2 check MySpec.tla --workers 4 --output json
```

Use simulation when random exploration is more appropriate than exhaustive checking:

```bash
tla2 simulate MySpec.tla --traces 100 --max-depth 50
```

Parse a module, start the language server, or generate Rust scaffolding from a specification:

```bash
tla2 parse MySpec.tla
tla2 lsp
tla2 codegen MySpec.tla -o generated_spec.rs
```

## Supported Formats

| Format or input | Command surface | Workspace source |
|-----------------|-----------------|------------------|
| TLA+ modules (`.tla`) | `tla2 check`, `tla2 simulate`, `tla2 parse`, `tla2 codegen` | `crates/tla-cli`, `crates/tla-core`, `crates/tla-check` |
| TLA+ model-checking configuration | `tla2 check --config <file>` | `crates/tla-cli`, `crates/tla-check` |
| AIGER hardware models (`.aig`, `.aag`) | `tla2 aiger <file>` | `crates/tla-cli`, `crates/tla-aiger` |
| BTOR2 hardware models (`.btor2`) | `tla2 btor2 <file>` | `crates/tla-cli`, `crates/tla-btor2` |
| VMT export | `tla2 vmt <file>` | `crates/tla-cli` |

Symbolic and hardware-oriented commands use crates in this workspace and the public `z4` dependency recorded in `Cargo.toml` and `Cargo.lock`.

## Repository Layout

| Path | Purpose |
|------|---------|
| `crates/tla-cli` | Command-line interface, binary entry points, and command dispatch. |
| `crates/tla-core` | Core TLA+ parsing, AST, semantic analysis, and evaluation support. |
| `crates/tla-check` | Model-checking orchestration and checker-facing execution paths. |
| `crates/tla-value` | Runtime value representation shared by parser, evaluator, and checker crates. |
| `crates/tla-z4` | Symbolic verification integration through the public `z4` dependency. |
| `crates/tla-aiger` and `crates/tla-btor2` | Hardware-model checking frontends and related checking logic. |
| `crates/tla-lsp` | Language Server Protocol support used by `tla2 lsp`. |
| `docs/` | Published reference material, attribution notes, and design documentation. |

## Reference Docs

- [`docs/REFERENCES.md`](docs/REFERENCES.md) - Bibliography and upstream software attributions for the verification, SAT/SMT, and hardware-model-checking work referenced by TLA2.
- [`docs/diagrams/system.md`](docs/diagrams/system.md) - Architecture map for the CLI, parser, typed IR, checker, code generation, and supporting workspace crates that are published with this release.

## Development

Use Cargo from the repository root:

```bash
cargo build
cargo test --workspace
cargo check --all-targets
```

Feature-gated builds are available through the crate features declared in the workspace manifests:

```bash
cargo build --release -p tla-cli --features z4
cargo build --release -p tla-cli --features llvm2
```

Before changing public documentation, keep factual claims tied to the manifest, lockfile, source files, or `docs/REFERENCES.md`, and keep links pointed at files that remain in the published tree.

## License

TLA2 is licensed under Apache-2.0. See [`LICENSE`](LICENSE).

Copyright 2026 Dropbox
