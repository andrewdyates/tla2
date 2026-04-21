# tla-logos

Verbatim fork of [logos](https://github.com/maciejhirsz/logos) 0.14.4, maintained
as part of the TLA2 Tier 2 zero-external-dep posture (Part of #4250).

- Upstream: https://github.com/maciejhirsz/logos
- Upstream license: MIT OR Apache-2.0 (preserved in `LICENSE-MIT` / `LICENSE-APACHE`)
- Forked rev: v0.14.4 (commit `196c8c0`)

The package `name` stays `logos` so `[patch.crates-io]` at the workspace root
redirects all graph consumers to this fork. Consumer code (`tla-core`) continues
to `use logos::Logos` with no source changes.

The fork consists of three crates:
- `tla-logos` (this crate) — runtime `Logos` trait + `Lexer`.
- `tla-logos-derive` — proc-macro shim.
- `tla-logos-codegen` — code-generation engine.
