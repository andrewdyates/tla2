# tla-syn — TLA2 fork of syn 2.0.117

**Upstream:** https://github.com/dtolnay/syn (tag 2.0.117)
**License:** MIT OR Apache-2.0 (preserved in `LICENSE-MIT` and `LICENSE-APACHE`)
**Fork tracked by:** #4250 (TLA2 zero-external-dep posture, Wave 30)

## Scope (umbrella-only)

Only the top-level `syn` crate is forked. Its runtime dependencies
(`proc-macro2`, `quote`, `unicode-ident`) are already forked in earlier
waves and are consumed via workspace-level `[patch.crates-io]`
redirection.

## What is verbatim vs what changed

- `src/` — verbatim upstream source (only the mandatory
  `Copyright 2026 Dropbox, Inc.` header added at the top of every file
  by the repo hook; no code changes).
- `Cargo.toml` — rewritten to drop dev-dependencies and upstream test /
  bench targets. These pull in anyhow, automod, insta, ref-cast,
  rustversion, syn-test-suite, termcolor, flate2, rayon, reqwest, tar,
  and walkdir — all external, which would defeat the zero-dep goal.
  The `[package] name` is preserved as `syn` so that
  `[patch.crates-io]` redirects every transitive consumer in the graph
  to this single in-workspace copy.
- `LICENSE-APACHE`, `LICENSE-MIT`, `README.md` — verbatim from upstream.
- `tests/`, `benches/`, `Cargo.toml.orig`, `Cargo.lock` — dropped (not
  needed for downstream consumption).

## Consumers (graph-wide)

Every proc-macro in the graph uses `syn`. Known consumers include:

- `thiserror_impl` (via `thiserror`)
- `serde_derive` (via `serde`)
- `clap_derive` (via `clap`)
- `tracing-attributes` (via `tracing`)
- `zerocopy-derive` (via `zerocopy`)
- `futures-macro`, `tokio-macros`, `async-trait`, `pin-project-internal`,
  and many others

All of these resolve to this fork through the workspace
`[patch.crates-io] syn = { path = "crates/tla-syn" }` entry. No
consumer code changes are required.

## Verification

`CARGO_TARGET_DIR=/tmp/tla2-agent-syn cargo check --profile agent --workspace`
builds the whole graph with this fork as the single `syn` copy.
