# tla-im

Verbatim fork of Bodil Stokke's [`im`](https://github.com/bodil/im-rs) 15.1.0
into the tla2 workspace. Part of #4250 (Tier 2 zero-external-dep posture).

## Why fork?

`im::HashMap`, `im::OrdMap`, `im::Vector`, `im::HashSet`, and `im::OrdSet`
back `tla_value::Value::{Function, Record, Seq, Set}`. This is a hot path for
the TLA+ model checker and the interpreter. Owning the source lets us:

- Pin the implementation at a known-good version.
- Apply targeted optimizations without upstream coordination.
- Drop the external git/crates.io dependency.

## License

`MPL-2.0+`, matching upstream. MPL-2.0 is a **per-file copyleft** license:
every source file in `src/` retains its upstream MPL-2.0 header. We add
authorship notes in `Cargo.toml` and in this README, but do NOT remove or
rewrite the per-file license notices.

The full license text lives in [`LICENSE`](./LICENSE).

## Fork origin

- Upstream: <https://github.com/bodil/im-rs>
- Version forked: `im 15.1.0` (crates.io)
- Fork date: 2026-04-18

## Consumer usage

In the tla2 workspace, consumers depend on `im` (workspace alias) which
resolves to this crate via `package = "tla-im"`:

```toml
[dependencies]
im = { workspace = true, optional = true }
```

No source-level changes are required — `use im::HashMap` continues to work.

## Features

- `debug` — upstream debug assertions.
- Optional dependencies (auto-enable a feature of the same name when
  selected): `arbitrary`, `proptest`, `quickcheck`, `rayon`, `serde`.
- `pool` is **not supported** in the threadsafe build (tla-im is
  threadsafe).

## Tests

The upstream proptest suite is the verification gate for any change to
this fork:

```bash
cargo test -p tla-im --lib
```
