// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under Apache-2.0 OR MIT.
//
// Verbatim fork of the rust-num stack (num-traits 0.2.19, num-integer 0.1.46,
// num-bigint 0.4.6). Upstream: https://github.com/rust-num.
// Upstream license: MIT OR Apache-2.0, preserved in LICENSE-MIT and
// LICENSE-APACHE (both at the tla-bignum root and in each sub-crate).
//
// This facade crate re-exports the three forked libraries at stable namespaces:
//   - `tla_bignum::traits`  -> num-traits source
//   - `tla_bignum::integer` -> num-integer source
//   - `tla_bignum::bigint`  -> num-bigint source
//
// Hot path: TLA+ integer arithmetic in `tla-value` / `tla-eval` backs onto
// `tla_bignum::bigint::BigInt` via `Value::Int`. Every `+`, `-`, `*`, `\div`,
// `%` on TLA+ integers runs through this fork.

#![cfg_attr(not(feature = "std"), no_std)]

pub use num_bigint as bigint;
pub use num_integer as integer;
pub use num_traits as traits;

// Flat re-exports for the most common consumer types so callers can write
// `use tla_bignum::{BigInt, BigUint, Sign, Zero, One, Integer};` if they
// prefer the flat surface over the namespaced one.
pub use num_bigint::{BigInt, BigUint, Sign, ToBigInt, ToBigUint};
pub use num_integer::{ExtendedGcd, Integer};
pub use num_traits::{Bounded, Num, One, Signed, ToPrimitive, Unsigned, Zero};
