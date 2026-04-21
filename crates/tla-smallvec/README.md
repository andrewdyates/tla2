tla-smallvec
============

TLA2 fork of the [`smallvec`](https://github.com/servo/rust-smallvec) crate.

"Small vector" optimization for Rust: store up to a small number of items on the
stack.

## Why a fork?

TLA2 is moving toward a zero-external-dependency posture (Tier 3 of the
supremacy plan). `smallvec` is small, stable, and touches many hot paths
(`tla-value`, `tla-eval`, `tla-check`, the vendored Cranelift/regalloc2
crates). Forking it lets us own the full stack without giving up the SSO
(small-size optimization) pattern.

## Relationship to upstream

Verbatim copy of `smallvec = "1.15.1"` at the time of the fork. The crate is
re-exported under the name `tla_smallvec` but preserves every public API path
(`tla_smallvec::SmallVec`, `tla_smallvec::smallvec!`, etc.) so migration is a
dep-name swap and nothing more.

Upstream authors retain original copyright (see `LICENSE-MIT`,
`LICENSE-APACHE`). TLA2 modifications (if any) are licensed under the same
dual MIT/Apache-2.0 terms.

## Consumer migration

Consumer crates inside this workspace continue to write `use smallvec::*;` and
`smallvec.workspace = true`. The workspace `smallvec` dependency is an alias
that resolves to this fork via `package = "tla-smallvec"`. No consumer source
changes are required.

## Example

```rust
use smallvec::{SmallVec, smallvec};

// This SmallVec can hold up to 4 items on the stack:
let mut v: SmallVec<[i32; 4]> = smallvec![1, 2, 3, 4];

// It will automatically move its contents to the heap if
// contains more than four items:
v.push(5);
```

## Supported features

- `const_generics`, `const_new`
- `union` (in-workspace use: `tla-codegen-frontend`, `tla-regalloc`,
  `tla-codegen-backend`)
- `specialization`, `may_dangle`, `write`, `drain_filter`, `drain_keep_rest`
- `serde` (optional)
- `arbitrary` (optional)

Features dropped vs upstream (not used in TLA2):

- `malloc_size_of` (Servo-specific)
- `impl_bincode` (pulls `bincode`/`unty`)
