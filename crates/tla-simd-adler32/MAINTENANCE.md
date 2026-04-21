# tla-simd-adler32 maintenance

Author: Andrew Yates <ayates@dropbox.com>

This crate is a **verbatim fork** of upstream `simd-adler32` 0.3.9 (MIT, by
Marvin Countryman), imported into the tla2 workspace as part of the Wave 21
"zero external runtime dependency" push tracked by GitHub issue **#4250**.

## Why the fork

- simd-adler32 is an optional SIMD-accelerated Adler-32 checksum backend for
  `miniz_oxide` (already Wave 18 forked into the workspace).
- By keeping the upstream `[package] name = "simd-adler32"` unchanged we can
  redirect every transitive consumer via `[patch.crates-io]` in the workspace
  root — "patch-by-name".
- The library is no-std-compatible and has zero external runtime dependencies,
  so this fork is umbrella-only: it exists purely so the workspace owns the
  source.

## What was trimmed

The upstream `Cargo.toml` was reduced to the minimum needed to build the
library:

- Dropped `[workspace]` inheritance, `[[bench]]` blocks, and all
  `[dev-dependencies]` (rand, criterion, adler, adler32).
- Kept `[package]` identity (`name = "simd-adler32"`, `version = "0.3.9"`) and
  the default feature set (`std`, `const-generics`, with optional `nightly`).

No source files under `src/` were modified.

## Updating the fork

If we ever need to bump this to a newer upstream release, copy the new
`src/`, `LICENSE.md`, and `README.md` into this directory verbatim and rebuild
the trimmed `Cargo.toml` using the same rules above. Keep the `[package]
name`, version, license, and authors fields identical to upstream so the
patch-by-name redirection stays sound.
