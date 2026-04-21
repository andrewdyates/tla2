# tla-tinyvec-macros

Verbatim fork of [`tinyvec_macros` 0.1.1](https://crates.io/crates/tinyvec_macros)
(`github.com/Soveu/tinyvec_macros`, MIT OR Apache-2.0 OR Zlib) into the TLA2
workspace as part of the zero-external-dep effort (Part of #4250).

The forked crate exposes a single macro (`impl_mirrored!`) used by `tinyvec`
to generate mirrored fn bodies across its `Inline`/`Heap` variants. The fork
is umbrella-only scope — no transitive deps are brought in because the
upstream crate has none.

Upstream package name `tinyvec_macros` is preserved so that
`[patch.crates-io]` redirects any transitive consumer (notably `tinyvec`)
to this in-tree fork graph-wide.

## License

Tri-licensed MIT / Apache-2.0 / Zlib. See `LICENSE-MIT.md`, `LICENSE-APACHE.md`,
`LICENSE-ZLIB.md`.
