# API Consumer Compatibility Canaries

Part of #1325. These are lightweight crates that import stable public API paths
from core library crates. They are compile-only — the imports ARE the test. If
`cargo check` fails on a canary, a public API contract was broken.

## Canary Crates

| Canary | Tests | Contract Surface |
|--------|-------|------------------|
| `core_translate_canary` | `tla-core` | Parsing, lowering, resolution, AST, name interning, substitution, translation |
| `check_fingerprint_canary` | `tla-check` | Checker entry points, config, state/fingerprint types, results, liveness, evaluation re-exports |
| `eval_value_canary` | `tla-eval`, `tla-value` | Evaluation context, Value types, constructors, fingerprinting, cache lifecycle |

## Running

```bash
# Run all canaries via the gate script
scripts/check_api_canary_gate.sh

# Run with verbose output on failure
scripts/check_api_canary_gate.sh --verbose

# Run a single canary
cargo check -p check_fingerprint_canary
```

The gate is also integrated as Check 9 in the code quality gate script.

## When a Canary Fails

A canary failure means a public API item was removed, renamed, or had its type
signature changed. This is either:

1. **Intentional API change** — update the canary to match the new API, then
   commit the canary update in the SAME commit as the API change. This makes
   the break visible and deliberate in git history.

2. **Accidental regression** — revert the breaking change or restore the
   removed re-export.

## Adding a New Canary

1. Create a directory under `tests/api_canaries/<crate>_canary/`
2. Add a Cargo manifest in that directory with `publish = false` and path deps to target crates
3. Add a lib source file in that directory with `#![allow(unused_imports, dead_code)]` and imports
   exercising the stable API surface
4. Add the canary name to the `CANARIES` array in the API canary gate script
5. Add the crate to workspace `members` in the root Cargo manifest

## Updating a Canary for Intentional API Changes

When making an intentional API change (rename, remove, retype):

1. Make the API change
2. Run the API canary gate script — it will fail
3. Update the affected canary's lib source to use the new API paths
4. Run the gate again to confirm it passes
5. Commit both changes together with a note explaining the intentional break

## What Belongs in a Canary

- Crate-root re-exports (`use tla_check::Foo`) — these are the stable contract
- Type constructors and method signatures users depend on
- Public trait imports

## What Does NOT Belong

- Internal submodule paths (`use tla_check::compiled_guard::core::Foo`)
- Test-only exports (`#[cfg(test)]` items)
- Items marked `pub(crate)` — these are explicitly internal
