# tla-regex — Wave 21 Zero-Dep Fork of `regex` 1.12.3

Andrew Yates <ayates@dropbox.com>

## Origin

Verbatim fork of upstream [regex 1.12.3](https://crates.io/crates/regex/1.12.3)
from `~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/regex-1.12.3/`.
Filed as **Part of #4250** during the tla2 zero-external-dep push (Wave 21).

## What Was Copied

- `src/` — the full upstream source tree, unchanged.
- `LICENSE-APACHE`, `LICENSE-MIT` — dual-license text preserved.
- `README.md` — upstream README preserved.
- `Cargo.toml` — trimmed locally: `[workspace]`, `[dev-dependencies]`,
  `[[test]]`, `[[bench]]`, `[[example]]`, and `[profile.*]` blocks removed
  (the workspace owns profiles). Nothing else was touched: `[package] name`
  remains exactly `regex`, `[features]`, `[dependencies]`, `[lib]`, and
  `[lints]` are byte-for-byte identical to upstream.

## Why the Package Name Is `regex`

The workspace root applies `[patch.crates-io] regex = { path = "crates/tla-regex" }`.
For this redirect to resolve for every transitive crates.io consumer the
fork's `[package] name` must match the published crate name exactly —
"patch-by-name". The directory is named `tla-regex/` by convention; the
Cargo package inside stays `regex`.

## Dependency Resolution

`regex` depends on `regex-automata`, `regex-syntax`, `memchr`, and
`aho-corasick`. Each is forked (or will be) under the same patch-by-name
pattern in the workspace `[patch.crates-io]` table. Resolution is automatic:
whichever of those deps already has a workspace patch entry is used; others
fall through to crates.io with no change in behavior.

## Updating the Fork

1. Bump the upstream source tarball to the desired version.
2. Re-run `cp -R $REGEX_SRC/src crates/tla-regex/src`.
3. Re-apply the `Cargo.toml` trim (strip dev-deps, test/bench/example
   targets, profile blocks).
4. `CARGO_TARGET_DIR=/tmp/tla2-fork-regex cargo check --profile agent -p regex`.
5. `CARGO_TARGET_DIR=/tmp/tla2-fork-regex cargo check --profile agent --workspace`.

Do not hand-edit files under `src/` except to track upstream.
