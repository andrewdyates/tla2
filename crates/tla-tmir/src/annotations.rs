// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable `ProofTag` constants used by tla-tmir lowering to attach custom
//! `ProofAnnotation::Custom(tag)` markers onto specific tMIR instructions
//! and functions.
//!
//! These tags express TLA+-specific proof obligations that upstream tMIR
//! does not yet have native instructions for. The low 16 bits of each tag
//! encode an optional parameter (e.g. the compile-time bound `N` for a
//! `bounded_loop`). The high 16 bits form a stable namespace so an external
//! tool can recognize the tag family regardless of parameter.
//!
//! Upstream ask (see tMIR#30): replace `Custom(BOUNDED_LOOP_*)` with a
//! native `tmir.bounded_loop(n)` annotation, and `Custom(PARALLEL_MAP)`
//! with a native `tmir.parallel_map` annotation.
//!
//! The caller runtime (tla-check, tla-eval) interprets these tags during
//! scheduling:
//! - `PARALLEL_MAP` on a loop header → eligible for `rayon::par_iter`-style
//!   parallel execution of the loop body.
//! - `BOUNDED_LOOP` on a loop header → the domain size is compile-time
//!   known, so loop-unrolling and termination proofs are trivial.
//!
//! These annotations are hints, not hard contracts — correctness of the
//! lowered IR does not depend on them. A downstream consumer that ignores
//! them produces semantically-equivalent (just slower) code.

use tmir::value::ProofTag;

/// Namespace: `tmir.parallel_map`. Per-iteration body is independent of all
/// other iterations, so the loop can be parallelized.
///
/// Emitted by `lower_func_def_begin` on the loop's header `CondBr`. Each
/// key's body evaluation writes to a distinct slot (slot `2 + 2*i`) in the
/// function aggregate and reads only from its own binding register, so
/// iterations are race-free.
///
/// Stable value: `0x504D_0000` (`"PM"` | namespace).
pub const PARALLEL_MAP: ProofTag = ProofTag::new(0x504D_0000);

/// Namespace: `tmir.bounded_loop`. The loop's domain cardinality is known
/// at compile time.
///
/// Emitted by `lower_forall_begin` / `lower_exists_begin` / `lower_choose_begin`
/// on the loop's header `CondBr` when the `r_domain` register was populated
/// by a `SetEnum { count }` or a `Range { lo, hi }` with constant operands.
///
/// The low 16 bits encode `N` (saturating to `u16::MAX`) so consumers can
/// recover the bound without scanning back through the IR:
/// - `BOUNDED_LOOP_BASE | (n as u16 as u32)` → tag for bound `n`
///
/// Use [`bounded_loop_with_n`] to build a tagged value.
///
/// Stable base: `0x424C_0000` (`"BL"` | namespace).
pub const BOUNDED_LOOP_BASE: u32 = 0x424C_0000;

/// Build a `Custom(ProofTag)` for a bounded loop with compile-time bound `n`.
///
/// The bound is saturated to `u16::MAX`; loops larger than 65535 elements
/// are still marked bounded but lose precise encoding.
#[must_use]
pub const fn bounded_loop_with_n(n: u32) -> ProofTag {
    let enc = if n > u16::MAX as u32 {
        u16::MAX as u32
    } else {
        n
    };
    ProofTag::new(BOUNDED_LOOP_BASE | enc)
}

/// Classifier: is this tag any flavor of `tmir.bounded_loop`?
#[must_use]
pub const fn is_bounded_loop(tag: ProofTag) -> bool {
    (tag.0 & 0xFFFF_0000) == BOUNDED_LOOP_BASE
}

/// Classifier: is this tag `tmir.parallel_map`?
#[must_use]
pub const fn is_parallel_map(tag: ProofTag) -> bool {
    (tag.0 & 0xFFFF_0000) == 0x504D_0000
}

/// Extract the compile-time bound `n` encoded in a bounded-loop tag.
/// Returns `None` if the tag is not a bounded-loop tag.
#[must_use]
pub const fn bounded_loop_n(tag: ProofTag) -> Option<u32> {
    if is_bounded_loop(tag) {
        Some(tag.0 & 0x0000_FFFF)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parallel_map_is_classified() {
        assert!(is_parallel_map(PARALLEL_MAP));
        assert!(!is_bounded_loop(PARALLEL_MAP));
    }

    #[test]
    fn bounded_loop_roundtrip_small_n() {
        let tag = bounded_loop_with_n(42);
        assert!(is_bounded_loop(tag));
        assert!(!is_parallel_map(tag));
        assert_eq!(bounded_loop_n(tag), Some(42));
    }

    #[test]
    fn bounded_loop_zero_is_still_bounded() {
        let tag = bounded_loop_with_n(0);
        assert!(is_bounded_loop(tag));
        assert_eq!(bounded_loop_n(tag), Some(0));
    }

    #[test]
    fn bounded_loop_saturates_above_u16() {
        let tag = bounded_loop_with_n(100_000);
        assert!(is_bounded_loop(tag));
        assert_eq!(bounded_loop_n(tag), Some(u16::MAX as u32));
    }

    #[test]
    fn parallel_map_and_bounded_loop_disjoint() {
        assert_ne!(PARALLEL_MAP, bounded_loop_with_n(0));
        assert_ne!(PARALLEL_MAP, bounded_loop_with_n(1));
    }

    #[test]
    fn unknown_tag_is_neither() {
        let unknown = ProofTag::new(0xDEAD_BEEF);
        assert!(!is_bounded_loop(unknown));
        assert!(!is_parallel_map(unknown));
        assert_eq!(bounded_loop_n(unknown), None);
    }
}
