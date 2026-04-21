# tla-bignum

Verbatim fork of the `rust-num` stack for TLA2's zero-external-dep posture
(Tier 2). Owns the big-integer arithmetic hot path: every TLA+ integer
operation routes through `tla_bignum::bigint::BigInt`.

## Upstream sources

| Crate | Upstream | Version | Path |
|-------|----------|---------|------|
| `num-traits` | https://github.com/rust-num/num-traits | 0.2.19 | `traits/` |
| `num-integer` | https://github.com/rust-num/num-integer | 0.1.46 | `integer/` |
| `num-bigint` | https://github.com/rust-num/num-bigint | 0.4.6 | `bigint/` |

Each sub-crate is a stand-alone library named after its upstream (`lib.name = "num_traits"` etc.) so source files inside the fork need no rewriting —
cross-crate paths like `use num_traits::Zero` inside `num-bigint` keep working.

## Licensing

Upstream license is **MIT OR Apache-2.0**. Both license files are preserved
verbatim at the crate root and in every sub-crate. The `authors` list in
each sub-crate's `Cargo.toml` credits "The Rust Project Developers" and
"rust-num project contributors" alongside the TLA2 maintainer.

## Layout

```
crates/tla-bignum/
├── Cargo.toml          # facade crate (re-exports three namespaces)
├── src/lib.rs          # tla_bignum::{traits, integer, bigint}
├── LICENSE-APACHE
├── LICENSE-MIT
├── README.md
├── traits/             # tla-bignum-traits (lib name: num_traits)
├── integer/            # tla-bignum-integer (lib name: num_integer)
└── bigint/             # tla-bignum-bigint  (lib name: num_bigint)
```

## Why not just use crates.io?

TLA2 is migrating to zero-external-dep so the verification toolchain can be
audited end-to-end. Vendoring arithmetic lets us:

1. Guarantee no supply-chain surprise on the hot path.
2. Later specialize `BigInt` for TLA+ semantics (small-int fast path, Kani
   proofs, JIT-visible representation) without upstream coordination.
3. Pin exact behavior across the workspace — no accidental semver drifts.

## Upgrading from upstream

1. `cd ~/.cargo/registry/src/index.crates.io-*` or fetch from
   https://github.com/rust-num/ at the target tag.
2. Replace `traits/src/`, `integer/src/`, `bigint/src/` with upstream `src/`.
3. Replace `traits/tests/`, `integer/tests/`, `bigint/tests/` similarly.
4. Re-run `cargo test -p tla-bignum-bigint` etc. — the sub-crate Cargo.toml
   files pin `package = "tla-bignum-..."` so internal `path` deps stay valid.
5. Bump the version in the root workspace `Cargo.toml` if the upstream
   version moved and update the table above.

## Public API

```rust
use tla_bignum::{BigInt, BigUint, Sign, Integer, Zero, One, Num, Signed};
// or
use tla_bignum::bigint::BigInt;
use tla_bignum::integer::Integer;
use tla_bignum::traits::{Zero, One};
```

Downstream `tla-value` / `tla-eval` / `tla-check` / `tla-z4` / `tla-jit`
depend on tla-bignum via the workspace dep table and keep their legacy
`use num_bigint::...` imports working — the workspace aliases rename the
tla-bignum sub-crates back to `num_bigint` / `num_integer` / `num_traits`.
