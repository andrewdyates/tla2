// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Speculative type-specialization planning and Cranelift helpers.
//!
//! Tier 2 compilation can speculate that some state variables remain
//! monomorphic across the hot part of the search. This module turns a
//! runtime [`TypeProfile`] into a small specialization plan and provides
//! helpers for emitting guarded Cranelift loads for the currently supported
//! scalar fast paths (`Int` and `Bool`).

use crate::type_profile::TypeProfile;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::Value as CraneValue;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use tla_jit_abi::SpecType;

// Re-export the pure-data descriptors from `tla-jit-abi`. The structs
// moved there in Wave 11b-redo of epic #4251 Stage 2d so `tla-check` can
// hold `TierPromotion { specialization_plan: Option<SpecializationPlan> }`
// fields without pulling `tla-jit` into its dep graph. The impl block
// below (which depends on `TypeProfile`) stays here.
pub use tla_jit_abi::{SpecializationPlan, SpecializedVarInfo};

const I64_SLOT_BYTES: usize = std::mem::size_of::<i64>();

/// Crate-local extension trait that carries `TypeProfile`-dependent
/// constructors for [`SpecializationPlan`]. The struct definition lives in
/// `tla-jit-abi` (moved there in Wave 11b-redo of epic #4251 Stage 2d) —
/// Rust's orphan rule forces us to attach this method via a trait defined in
/// the owning crate.
///
/// The read-only query methods (`int_var_count`, `bool_var_count`,
/// `specialized_var_count`, `has_specializable_vars`) are inherent on
/// `SpecializationPlan` in `tla-jit-abi` as of Wave 16 Gate 1 Batch A
/// (Part of #4267 / #4291) so `tla-check` no longer needs to import this
/// trait.
pub trait SpecializationPlanExt {
    /// Build a specialization plan from a completed type profile.
    fn from_profile(profile: &TypeProfile) -> Self;
}

impl SpecializationPlanExt for SpecializationPlan {
    #[must_use]
    fn from_profile(profile: &TypeProfile) -> Self {
        let monomorphic_types = profile.monomorphic_types();
        let var_specializations: Vec<SpecializedVarInfo> = monomorphic_types
            .into_iter()
            .enumerate()
            .filter_map(|(var_idx, spec_type)| {
                spec_type.map(|spec_type| SpecializedVarInfo {
                    var_idx,
                    spec_type,
                    slot_offset: var_idx.checked_mul(I64_SLOT_BYTES),
                })
            })
            .collect();

        let guard_needed = !var_specializations.is_empty();
        let mut plan = Self {
            var_specializations,
            guard_needed,
            expected_speedup_factor: 1.0,
        };
        plan.expected_speedup_factor = estimate_speedup(&plan);
        plan
    }
}

/// Emits runtime guards that validate speculative scalar type assumptions.
///
/// When full state-layout metadata is unavailable, the current implementation
/// uses conservative scalar checks directly on the raw state slots:
/// - `Bool` slots must be exactly `0` or `1`
/// - `Int` slots are range-checked against the i64 domain
///
/// The integer range check is intentionally weak for the legacy flat state
/// representation, but it preserves a uniform guard structure and gives the
/// caller a single fallback edge for all speculative assumptions.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct TypeGuardEmitter;

impl TypeGuardEmitter {
    /// Create a new guard emitter.
    #[must_use]
    pub(crate) const fn new() -> Self {
        Self
    }

    /// Emit the runtime guard chain for the provided specialization plan.
    ///
    /// The current block must be the insertion point when this method is
    /// called. Control branches to `fallback_block` on guard failure and to
    /// `pass_block` when all supported guards succeed.
    pub(crate) fn emit_guard(
        builder: &mut FunctionBuilder,
        state_ptr: CraneValue,
        plan: &SpecializationPlan,
        fallback_block: cranelift_codegen::ir::Block,
        pass_block: cranelift_codegen::ir::Block,
    ) {
        if !plan.guard_needed {
            builder.ins().jump(pass_block, &[]);
            return;
        }

        let guarded: Vec<&SpecializedVarInfo> = plan
            .var_specializations
            .iter()
            .filter(|info| matches!(info.spec_type, SpecType::Int | SpecType::Bool))
            .collect();

        if guarded.is_empty() {
            builder.ins().jump(pass_block, &[]);
            return;
        }

        for (idx, info) in guarded.iter().enumerate() {
            let next_block = if idx + 1 == guarded.len() {
                pass_block
            } else {
                builder.create_block()
            };

            match info.spec_type {
                SpecType::Int => Self::emit_int_guard(
                    builder,
                    state_ptr,
                    byte_offset_i32(info),
                    fallback_block,
                    next_block,
                ),
                SpecType::Bool => Self::emit_bool_guard(
                    builder,
                    state_ptr,
                    byte_offset_i32(info),
                    fallback_block,
                    next_block,
                ),
                _ => {
                    builder.ins().jump(next_block, &[]);
                }
            }

            if idx + 1 != guarded.len() {
                builder.seal_block(next_block);
                builder.switch_to_block(next_block);
            }
        }
    }

    fn emit_int_guard(
        builder: &mut FunctionBuilder,
        state_ptr: CraneValue,
        byte_offset: i32,
        fallback_block: cranelift_codegen::ir::Block,
        next_block: cranelift_codegen::ir::Block,
    ) {
        let value = builder
            .ins()
            .load(types::I64, MemFlags::new(), state_ptr, byte_offset);
        let lower_ok = builder
            .ins()
            .icmp_imm(IntCC::SignedGreaterThanOrEqual, value, i64::MIN);
        let upper_ok = builder
            .ins()
            .icmp_imm(IntCC::SignedLessThanOrEqual, value, i64::MAX);
        let in_range = builder.ins().band(lower_ok, upper_ok);
        builder
            .ins()
            .brif(in_range, next_block, &[], fallback_block, &[]);
    }

    fn emit_bool_guard(
        builder: &mut FunctionBuilder,
        state_ptr: CraneValue,
        byte_offset: i32,
        fallback_block: cranelift_codegen::ir::Block,
        next_block: cranelift_codegen::ir::Block,
    ) {
        let value = builder
            .ins()
            .load(types::I64, MemFlags::new(), state_ptr, byte_offset);
        let is_zero = builder.ins().icmp_imm(IntCC::Equal, value, 0);
        let check_one_block = builder.create_block();

        builder
            .ins()
            .brif(is_zero, next_block, &[], check_one_block, &[]);

        builder.seal_block(check_one_block);
        builder.switch_to_block(check_one_block);

        let is_one = builder.ins().icmp_imm(IntCC::Equal, value, 1);
        builder
            .ins()
            .brif(is_one, next_block, &[], fallback_block, &[]);
    }
}

/// Emits specialized loads for monomorphic scalar state variables.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct SpecializedLoadEmitter;

impl SpecializedLoadEmitter {
    /// Load a state slot known to contain an integer scalar.
    pub(crate) fn emit_load_int(
        builder: &mut FunctionBuilder,
        state_ptr: CraneValue,
        var_idx: usize,
        state_len: CraneValue,
    ) -> CraneValue {
        let _ = state_len;
        builder.ins().load(
            types::I64,
            MemFlags::new(),
            state_ptr,
            byte_offset_from_var_idx(var_idx),
        )
    }

    /// Load a state slot known to contain a boolean scalar.
    pub(crate) fn emit_load_bool(
        builder: &mut FunctionBuilder,
        state_ptr: CraneValue,
        var_idx: usize,
        state_len: CraneValue,
    ) -> CraneValue {
        let _ = state_len;
        builder.ins().load(
            types::I64,
            MemFlags::new(),
            state_ptr,
            byte_offset_from_var_idx(var_idx),
        )
    }
}

/// Estimate the expected speedup for a specialization plan.
///
/// Heuristic:
/// - each `Int` specialization contributes a `1.1x` factor
/// - each `Bool` specialization contributes a `1.05x` factor
/// - the combined estimate is capped at `3.0x`
#[must_use]
pub(crate) fn estimate_speedup(plan: &SpecializationPlan) -> f64 {
    let int_factor = 1.1_f64.powi(plan.int_var_count() as i32);
    let bool_factor = 1.05_f64.powi(plan.bool_var_count() as i32);
    (int_factor * bool_factor).min(3.0)
}

/// Crate-local helper for the compile-side `byte_offset_i32` computation.
/// Lives as a free function (not an inherent impl) because `SpecializedVarInfo`
/// is defined in `tla-jit-abi` and Rust forbids inherent impls across crates.
fn byte_offset_i32(info: &SpecializedVarInfo) -> i32 {
    info.slot_offset
        .and_then(|offset| i32::try_from(offset).ok())
        .unwrap_or_else(|| byte_offset_from_var_idx(info.var_idx))
}

fn byte_offset_from_var_idx(var_idx: usize) -> i32 {
    var_idx
        .checked_mul(I64_SLOT_BYTES)
        .and_then(|offset| i32::try_from(offset).ok())
        .unwrap_or(i32::MAX)
}

#[cfg(test)]
mod tests {
    use super::{estimate_speedup, SpecializationPlan, SpecializationPlanExt, SpecializedVarInfo};
    use crate::type_profile::{SpecType, TypeProfile};

    fn approx_eq(lhs: f64, rhs: f64) {
        let diff = (lhs - rhs).abs();
        assert!(
            diff <= 1e-9,
            "expected {lhs} to be within tolerance of {rhs}, diff={diff}"
        );
    }

    #[test]
    fn specialization_plan_from_profile_all_int() {
        let mut profile = TypeProfile::new(3);
        profile.record_state(&[SpecType::Int, SpecType::Int, SpecType::Int]);
        profile.record_state(&[SpecType::Int, SpecType::Int, SpecType::Int]);
        profile.mark_stable();

        let plan = SpecializationPlan::from_profile(&profile);

        assert!(plan.guard_needed);
        assert!(plan.has_specializable_vars());
        assert_eq!(plan.specialized_var_count(), 3);
        assert_eq!(plan.int_var_count(), 3);
        assert_eq!(plan.bool_var_count(), 0);
        assert_eq!(plan.var_specializations[0].slot_offset, Some(0));
        assert_eq!(plan.var_specializations[1].slot_offset, Some(8));
        assert_eq!(plan.var_specializations[2].slot_offset, Some(16));
        approx_eq(plan.expected_speedup_factor, 1.1_f64.powi(3));
    }

    #[test]
    fn specialization_plan_from_profile_mixed_types() {
        let mut profile = TypeProfile::new(4);
        profile.record_state(&[
            SpecType::Int,
            SpecType::Bool,
            SpecType::String,
            SpecType::String,
        ]);
        profile.record_state(&[
            SpecType::Int,
            SpecType::Bool,
            SpecType::Other,
            SpecType::String,
        ]);
        profile.mark_stable();

        let plan = SpecializationPlan::from_profile(&profile);

        assert!(plan.guard_needed);
        assert!(plan.has_specializable_vars());
        assert_eq!(plan.specialized_var_count(), 3);
        assert_eq!(plan.int_var_count(), 1);
        assert_eq!(plan.bool_var_count(), 1);
        assert_eq!(plan.var_specializations[0].var_idx, 0);
        assert!(matches!(
            plan.var_specializations[0].spec_type,
            SpecType::Int
        ));
        assert_eq!(plan.var_specializations[1].var_idx, 1);
        assert!(matches!(
            plan.var_specializations[1].spec_type,
            SpecType::Bool
        ));
        assert_eq!(plan.var_specializations[2].var_idx, 3);
        assert!(matches!(
            plan.var_specializations[2].spec_type,
            SpecType::String
        ));
        approx_eq(plan.expected_speedup_factor, 1.1 * 1.05);
    }

    #[test]
    fn estimate_speedup_uses_heuristic_and_cap() {
        let no_specialization = SpecializationPlan {
            var_specializations: Vec::new(),
            guard_needed: false,
            expected_speedup_factor: 1.0,
        };
        approx_eq(estimate_speedup(&no_specialization), 1.0);

        let mixed = SpecializationPlan {
            var_specializations: vec![
                SpecializedVarInfo {
                    var_idx: 0,
                    spec_type: SpecType::Int,
                    slot_offset: Some(0),
                },
                SpecializedVarInfo {
                    var_idx: 1,
                    spec_type: SpecType::Bool,
                    slot_offset: Some(8),
                },
                SpecializedVarInfo {
                    var_idx: 2,
                    spec_type: SpecType::String,
                    slot_offset: Some(16),
                },
            ],
            guard_needed: true,
            expected_speedup_factor: 0.0,
        };
        approx_eq(estimate_speedup(&mixed), 1.1 * 1.05);

        let capped = SpecializationPlan {
            var_specializations: (0..20)
                .map(|idx| SpecializedVarInfo {
                    var_idx: idx,
                    spec_type: SpecType::Int,
                    slot_offset: idx.checked_mul(8),
                })
                .collect(),
            guard_needed: true,
            expected_speedup_factor: 0.0,
        };
        approx_eq(estimate_speedup(&capped), 3.0);
    }

    #[test]
    fn has_specializable_vars_distinguishes_scalar_fast_paths() {
        let mut scalar_profile = TypeProfile::new(2);
        scalar_profile.record_state(&[SpecType::Bool, SpecType::String]);
        scalar_profile.record_state(&[SpecType::Bool, SpecType::String]);
        let scalar_plan = SpecializationPlan::from_profile(&scalar_profile);
        assert!(scalar_plan.has_specializable_vars());

        let mut nonscalar_profile = TypeProfile::new(2);
        nonscalar_profile.record_state(&[SpecType::String, SpecType::Record]);
        nonscalar_profile.record_state(&[SpecType::String, SpecType::Record]);
        let nonscalar_plan = SpecializationPlan::from_profile(&nonscalar_profile);
        assert!(!nonscalar_plan.has_specializable_vars());
        assert_eq!(nonscalar_plan.specialized_var_count(), 2);
        assert_eq!(nonscalar_plan.int_var_count(), 0);
        assert_eq!(nonscalar_plan.bool_var_count(), 0);
        approx_eq(nonscalar_plan.expected_speedup_factor, 1.0);
    }
}
