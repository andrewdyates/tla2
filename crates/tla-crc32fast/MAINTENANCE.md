# tla-crc32fast Maintenance Notes

Andrew Yates <ayates@dropbox.com>

## Provenance

Verbatim fork of [crc32fast 1.5.0](https://crates.io/crates/crc32fast/1.5.0)
(`https://github.com/srijs/rust-crc32fast`), dual-licensed under
`MIT OR Apache-2.0`. Imported 2026-04-19 from the local cargo registry cache at
`~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/crc32fast-1.5.0/`.

## Why

Part of #4250 (Wave 21) — TLA2's zero-external-dep posture. crc32fast is a leaf
library (pure-Rust CRC-32 IEEE checksum, SIMD-accelerated on x86_64/aarch64)
consumed transitively by flate2 (png/zip/gzip integrity checks). Forking it
into the workspace keeps only one copy of the `crc32fast::Hasher` type
graph-wide and eliminates another crates.io dependency.

## Patch-by-name

The fork's `[package] name = "crc32fast"` is preserved verbatim so the
workspace root `[patch.crates-io]` entry redirects every transitive consumer
(flate2 + anything else that pulls crc32fast) to this single in-workspace
copy. Same pattern as tla-indexmap, tla-rand, tla-rayon, etc.

## Scope

Only the umbrella `crc32fast` 1.5.0 crate is forked. Its lone runtime
dependency `cfg-if` remains an external leaf dep (tiny, widely-used macro
crate — not worth forking). `build.rs` is preserved; it only sets a cfg flag
based on the detected rustc minor version.

## Updating

This is a verbatim fork. Do not drift the sources. To refresh from upstream:

1. `cargo update crc32fast` against a sandbox workspace to pick a new version.
2. `cp -R ~/.cargo/registry/src/index.crates.io-*/crc32fast-<ver>/{src,build.rs,LICENSE-*,README.md}` into this directory.
3. Re-apply the trimmed `Cargo.toml` header above (stripping `[workspace]`,
   `[[bench]]`, `[[test]]`, and dev-dependencies).
4. `cargo check --workspace` to ensure the API still lines up for flate2.

No TLA2-specific patches are applied to the source tree.
