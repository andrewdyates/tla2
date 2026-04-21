# tla-redox-syscall

TLA2 verbatim fork of `redox_syscall` 0.5.18.

This crate contains the Redox OS system call numbers and Rust wrappers. It is
an OS-binding crate pulled transitively by `parking_lot_core` and `libredox`
when building for Redox targets. On non-Redox hosts (macOS, Linux, Windows)
the code is conditionally compiled out — the fork exists so that when the
workspace *is* built on Redox, every graph consumer resolves to a single
in-tree copy of the crate.

## Source

- Upstream: https://gitlab.redox-os.org/redox-os/syscall (v0.5.18)
- Original author: Jeremy Soller <jackpot51@gmail.com>
- Original license: MIT (preserved in LICENSE)

## Scope

Umbrella-only. Only the top-level `redox_syscall` crate is forked here.
Other Redox-ecosystem deps (e.g. `redox_termios`) remain external leaf deps.

Version coexistence: the workspace graph also pulls `redox_syscall` 0.1.57
(via `thread-id`) and 0.7.4 (via `libredox`). Cargo's `[patch.crates-io]` is
version-aware, so this 0.5.18 fork substitutes only for consumers matching
the `^0.5` requirement; the 0.1 and 0.7 lines continue to resolve through
crates.io unchanged. Same multi-major coexistence pattern used by
`hashbrown` / `unicode-width` / `thiserror` / `getrandom` forks in prior
waves (Part of #4250).

## License

MIT, preserved verbatim from the upstream. See `LICENSE`.

[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)
