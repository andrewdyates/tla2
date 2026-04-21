// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Invariant evaluation.
//!
//! TLC alignment: `Tool.isValid()` (invariant check). Constraint and terminal
//! evaluation live in the sibling `constraints` module (Part of #3603).

#[cfg(debug_assertions)]
use super::super::debug::debug_invariants;
#[cfg(debug_assertions)]
use super::super::Value;
use super::super::{ArrayState, CheckError, Fingerprint, ModelChecker};
use crate::checker_ops::InvariantOutcome;
// Part of #4267 Gate 1 Batch C: collapse Cranelift-backed JIT type paths.
use tla_jit::bytecode_lower::JitInvariantCache as JitInvariantCacheImpl;

pub(crate) fn collect_runtime_failing_invariant_bytecode_ops(
    bytecode: &tla_eval::bytecode_vm::CompiledBytecode,
    invariants: &[String],
    state_env: tla_eval::StateEnvRef,
    eval_ctx: &tla_eval::EvalCtx,
) -> Vec<(String, String)> {
    use tla_eval::bytecode_vm::BytecodeVm;

    let mut runtime_failed = Vec::new();
    if bytecode.op_indices.is_empty() {
        return runtime_failed;
    }

    let mut vm =
        BytecodeVm::from_state_env(&bytecode.chunk, state_env, None).with_eval_ctx(eval_ctx);
    for inv_name in invariants {
        let Some(&func_idx) = bytecode.op_indices.get(inv_name) else {
            continue;
        };
        if let Err(error) = vm.execute_function(func_idx) {
            runtime_failed.push((inv_name.clone(), error.to_string()));
        }
    }

    runtime_failed
}

pub(crate) fn prune_runtime_failing_invariant_bytecode_ops(
    bytecode: &mut tla_eval::bytecode_vm::CompiledBytecode,
    runtime_failed: Vec<(String, String)>,
    log_prefix: &str,
) {
    if runtime_failed.is_empty() {
        return;
    }

    let stats_enabled = crate::check::debug::bytecode_vm_stats_enabled();
    let reason_logs_enabled = stats_enabled || crate::check::debug::debug_bytecode_vm();

    for (name, reason) in runtime_failed {
        if bytecode.op_indices.remove(&name).is_none() {
            continue;
        }
        if reason_logs_enabled {
            eprintln!("[{log_prefix}]   runtime-prune {name}: {reason}");
        }
        bytecode.failed.push((
            name,
            tla_tir::bytecode::CompileError::Unsupported(format!(
                "runtime validation failed: {reason}"
            )),
        ));
    }
}

/// Convert a JIT i64 successor output back into an ArrayState.
///
/// The JIT next-state function writes primed variable values as i64 values,
/// where Int values are stored directly and Bool values are stored as 0/1.
///
/// This function creates a new ArrayState by:
/// 1. Cloning the parent state (to preserve unchanged variables, fp_cache-free)
/// 2. Overwriting each variable with the corresponding JIT output value,
///    using the parent's type tag (Bool/Int) to choose the right encoding
///
/// For compound types (records, functions, etc.), JIT next-state actions
/// return `FallbackNeeded`, so this function only handles scalar types.
/// Compound variables retain their parent value (clone_for_working copies them).
///
/// Uses `Value::SmallInt(i64)` to avoid BigInt heap allocation on the hot path.
///
/// Part of #3910: JIT next-state dispatch.
pub(crate) fn unflatten_i64_to_array_state(
    parent: &ArrayState,
    jit_output: &[i64],
    state_var_count: usize,
) -> ArrayState {
    unflatten_i64_to_array_state_with_input(parent, jit_output, state_var_count, None)
}

/// Unflatten JIT output to an ArrayState, optionally deserializing compound
/// values that were modified in-place in the input buffer.
///
/// When `jit_input` is `Some`, compound variables are deserialized from the
/// input buffer using the offset stored in `jit_output[var_idx]`. This handles
/// the case where native FuncExcept modifies compound data in-place in the
/// input buffer and writes the base_slot offset to the output.
///
/// Part of #3958: Enable native compound value write-back in JIT next-state.
pub(crate) fn unflatten_i64_to_array_state_with_input(
    parent: &ArrayState,
    jit_output: &[i64],
    state_var_count: usize,
    jit_input: Option<&[i64]>,
) -> ArrayState {
    let mut succ = parent.clone_for_working();
    let parent_values = parent.values();
    let n = state_var_count.min(jit_output.len()).min(parent_values.len());
    for var_idx in 0..n {
        let val = jit_output[var_idx];
        let cv = &parent_values[var_idx];
        if cv.is_bool() {
            succ.set(
                crate::var_index::VarIndex::new(var_idx),
                tla_value::Value::Bool(val != 0),
            );
        } else if cv.is_int() {
            succ.set(
                crate::var_index::VarIndex::new(var_idx),
                tla_value::Value::SmallInt(val),
            );
        } else if val >= tla_jit_runtime::abi::COMPOUND_SCRATCH_BASE {
            // Compound variable constructed by JIT (e.g., RecordNew) and written
            // to the thread-local scratch buffer. The offset encodes the position
            // within the scratch buffer.
            let scratch_pos = (val - tla_jit_runtime::abi::COMPOUND_SCRATCH_BASE) as usize;
            let scratch = tla_jit_runtime::abi::read_compound_scratch();
            if scratch_pos < scratch.len() {
                if let Ok((deserialized, _slots)) = tla_jit_runtime::deserialize_value(&scratch, scratch_pos) {
                    succ.set(
                        crate::var_index::VarIndex::new(var_idx),
                        deserialized,
                    );
                }
                // If deserialization fails, retain parent value
            }
        } else if let Some(input) = jit_input {
            // Compound variable: the JIT may have modified the serialized data
            // in-place in the input buffer. Deserialize from the input buffer
            // at the offset stored in jit_output[var_idx].
            let offset = val as usize;
            if offset < input.len() {
                if let Ok((deserialized, _slots)) = tla_jit_runtime::deserialize_value(input, offset) {
                    succ.set(
                        crate::var_index::VarIndex::new(var_idx),
                        deserialized,
                    );
                }
                // If deserialization fails, retain parent value
            }
            // If offset is 0 (no StoreVar for this compound var), retain parent value
        }
        // Non-scalar types without jit_input: retain parent value (clone_for_working copied them).
    }
    succ
}

/// Non-JIT version — same as unflatten_i64_to_array_state.

/// Compute a `Fingerprint(u64)` directly from a JIT flat i64 successor buffer.
///
/// This replicates the exact fingerprint that `ArrayState::fingerprint` would
/// produce after `unflatten_i64_to_array_state_with_input`, but WITHOUT
/// allocating the intermediate `ArrayState`. The parent state provides type
/// info (Bool vs Int) for each variable, and its per-variable fingerprint cache
/// provides fallback values for unchanged compound variables.
///
/// Returns `Some(Fingerprint)` when all variables can be fingerprinted from the
/// flat buffer. Returns `None` when any compound variable was modified (detected
/// by a value >= `COMPOUND_SCRATCH_BASE` or a changed serialization offset),
/// requiring the caller to fall back to full unflatten + fingerprint.
///
/// Part of #4032: Defer Value reconstruction to cold path.
/// Returns `Some((Fingerprint, combined_xor))` on success. The `combined_xor`
/// is the pre-finalization XOR accumulator that can be stored in `fp_cache`
/// for incremental fingerprinting of this state's successors.
///
/// Part of #4030: Return combined_xor for proper fp_cache propagation.
pub(crate) fn fingerprint_jit_flat_successor(
    parent: &ArrayState,
    jit_output: &[i64],
    state_var_count: usize,
    jit_input: Option<&[i64]>,
    registry: &crate::var_index::VarRegistry,
) -> Option<(crate::Fingerprint, u64)> {
    use crate::fingerprint::{fp64_extend_byte, fp64_extend_i32, fp64_extend_i64, FP64_INIT};
    use crate::fingerprint::value_tags::{BOOLVALUE, INTVALUE};
    use crate::state::finalize_fingerprint_xor;
    use tla_core::FNV_PRIME;

    let parent_values = parent.values();
    let n = state_var_count.min(jit_output.len()).min(parent_values.len());

    // Ensure parent has per-variable fingerprint cache for compound fallback.
    // If the parent doesn't have value_fps cached, we can still compute for
    // scalar variables but need the cache for compound ones. We'll compute
    // compound value fps on the fly from the parent's CompactValues.
    let parent_fp_cache = parent.cached_value_fps();

    let mut combined_xor = 0u64;

    for var_idx in 0..n {
        let val = jit_output[var_idx];
        let cv = &parent_values[var_idx];

        let value_fp = if cv.is_bool() {
            let b = val != 0;
            let fp = fp64_extend_i64(FP64_INIT, BOOLVALUE);
            let c = if b { b't' } else { b'f' };
            fp64_extend_byte(fp, c)
        } else if cv.is_int() {
            let fp = fp64_extend_i64(FP64_INIT, INTVALUE);
            if i32::try_from(val).is_ok() {
                fp64_extend_i32(fp, val as i32)
            } else {
                fp64_extend_i64(fp, val)
            }
        } else {
            // Compound variable. Check if it was modified by JIT.
            #[allow(clippy::collapsible_else_if)]
            if val >= tla_jit_runtime::abi::COMPOUND_SCRATCH_BASE {
                return None;
            } else if let Some(input) = jit_input {
                let parent_flat_val = if var_idx < input.len() {
                    input[var_idx]
                } else {
                    0
                };
                if val != parent_flat_val {
                    return None;
                }
                if let Some(fps) = parent_fp_cache {
                    fps[var_idx]
                } else {
                    crate::state::compact_value_fingerprint(cv)
                }
            } else {
                if let Some(fps) = parent_fp_cache {
                    fps[var_idx]
                } else {
                    crate::state::compact_value_fingerprint(cv)
                }
            }
        };

        let salt = registry.fp_salt(crate::var_index::VarIndex::new(var_idx));
        let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
        combined_xor ^= contribution;
    }

    // Handle remaining variables (beyond what JIT wrote) — they retain parent values.
    for var_idx in n..parent_values.len() {
        let cv = &parent_values[var_idx];
        let value_fp = if let Some(fps) = parent_fp_cache {
            fps[var_idx]
        } else {
            crate::state::compact_value_fingerprint(cv)
        };
        let salt = registry.fp_salt(crate::var_index::VarIndex::new(var_idx));
        let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
        combined_xor ^= contribution;
    }

    let mixed = finalize_fingerprint_xor(combined_xor, FNV_PRIME);
    Some((crate::Fingerprint(mixed), combined_xor))
}

/// Compute a fingerprint incrementally from the parent's cached `combined_xor`.
///
/// Instead of computing value fingerprints for ALL state variables (O(n)),
/// this only processes variables where `jit_output[i] != jit_input[i]`.
/// For most TLA+ actions that change 1-3 out of 10-20+ variables, this is
/// a significant win: O(changed_vars) fingerprint computations instead of
/// O(total_vars).
///
/// Requires the parent to have a populated `fp_cache` with `combined_xor`.
/// Returns `None` if:
/// - The parent lacks `fp_cache`
/// - Any changed variable is a compound type (needs full unflatten)
/// - Buffer lengths don't match
///
/// Returns `Some((Fingerprint, combined_xor))` on success.
///
/// Part of #4030: Incremental JIT fingerprinting for diff-based dedup.
pub(crate) fn fingerprint_jit_flat_successor_incremental(
    parent: &ArrayState,
    jit_output: &[i64],
    jit_input: &[i64],
    state_var_count: usize,
    registry: &crate::var_index::VarRegistry,
) -> Option<(crate::Fingerprint, u64)> {
    use crate::state::finalize_fingerprint_xor;
    use tla_core::FNV_PRIME;

    // Require parent fp_cache with combined_xor.
    let fp_cache = parent.fp_cache.as_ref()?;
    // Reject if combined_xor is zero AND value_fps is absent — this indicates an
    // uninitialized cache from set_cached_fingerprint(). A real state with all
    // variables at their default values could have combined_xor == 0, but it would
    // also have value_fps populated from the initial fingerprint() call.
    //
    // Part of #4165: Log a one-time warning when this fallback triggers, so
    // performance issues from silent recomputation are visible in diagnostics.
    if fp_cache.combined_xor == 0 && fp_cache.value_fps.is_none() {
        use std::sync::atomic::{AtomicBool, Ordering};
        static WARNED: AtomicBool = AtomicBool::new(false);
        if !WARNED.swap(true, Ordering::Relaxed) {
            eprintln!(
                "[jit] incremental fingerprint fallback: parent state has combined_xor=0 \
                 without value_fps (uninitialized fp_cache from set_cached_fingerprint). \
                 Falling back to full recomputation. This may indicate a missing \
                 set_cached_fingerprint_with_xor() call on the admission path."
            );
        }
        return None;
    }
    let mut combined_xor = fp_cache.combined_xor;

    let parent_values = parent.values();
    let n = state_var_count
        .min(jit_output.len())
        .min(jit_input.len())
        .min(parent_values.len());

    for var_idx in 0..n {
        let out_val = jit_output[var_idx];
        let in_val = jit_input[var_idx];

        // Fast path: unchanged variable — no fingerprint work needed.
        if out_val == in_val {
            continue;
        }

        let cv = &parent_values[var_idx];
        let salt = registry.fp_salt(crate::var_index::VarIndex::new(var_idx));

        if cv.is_bool() {
            // Bool changed: compute old and new fps, XOR delta.
            let old_fp = crate::fingerprint::fp64_bool_lookup(in_val != 0);
            let new_fp = crate::fingerprint::fp64_bool_lookup(out_val != 0);
            let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
            let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
            combined_xor ^= old_contrib ^ new_contrib;
        } else if cv.is_int() {
            // Int changed: compute old and new fps, XOR delta.
            let old_fp = compute_scalar_i64_fp(in_val);
            let new_fp = compute_scalar_i64_fp(out_val);
            let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
            let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
            combined_xor ^= old_contrib ^ new_contrib;
        } else {
            // Compound variable changed — can't do incremental, need full unflatten.
            return None;
        }
    }

    let mixed = finalize_fingerprint_xor(combined_xor, FNV_PRIME);
    Some((crate::Fingerprint(mixed), combined_xor))
}

/// Compute the value fingerprint for a scalar i64 (Int type).
///
/// Uses the precomputed lookup table for small ints (common case), falling back
/// to the full FP64 computation for large values.
///
/// Part of #4030: Extracted for reuse in incremental fingerprinting.
#[inline]
fn compute_scalar_i64_fp(val: i64) -> u64 {
    crate::fingerprint::fp64_smallint_lookup(val).unwrap_or_else(|| {
        use crate::fingerprint::{fp64_extend_i32, fp64_extend_i64, FP64_INIT};
        use crate::fingerprint::value_tags::INTVALUE;
        let fp = fp64_extend_i64(FP64_INIT, INTVALUE);
        if i32::try_from(val).is_ok() {
            fp64_extend_i32(fp, val as i32)
        } else {
            fp64_extend_i64(fp, val)
        }
    })
}

/// Compute a `Fingerprint(u64)` from a flat i64 buffer using xxh3-64 SIMD.
///
/// This is the "compiled fingerprinting" path for JIT Phase 4 (#3987). When
/// the model checker is operating in flat-state mode (all variables are scalar
/// Int/Bool), the fingerprint can be computed by hashing the raw byte
/// representation of the i64 buffer directly, bypassing per-variable value
/// fingerprint computation entirely.
///
/// Returns a `Fingerprint(u64)` compatible with the BFS dedup table.
///
/// # When to use
///
/// Use this when:
/// - ALL state variables are scalar (Int or Bool), no compound types
/// - The state is represented as a flat `[i64]` buffer
/// - You want maximum throughput (single SIMD hash call vs per-variable FP64)
///
/// Do NOT use when compound variables are present — their fingerprints cannot
/// be derived from the i64 buffer alone.
///
/// Part of #3987 Phase 4: compiled fingerprinting.
/// Part of #4215: Uses a domain-separation seed to prevent collisions with
/// the FP64/FNV array-path fingerprints that may coexist in the same dedup
/// table (init states are fingerprinted with FP64 before xxh3 activation).
///
/// Soundness contract (#4319 Phase 0 / Option D):
/// This is the *sole* compiled-path fingerprint entry point. Every caller in
/// the compiled fingerprint pipeline — `array_state_fingerprint_xxh3`,
/// `FlatState::fingerprint_compiled`, the flat-state-primary BFS successor
/// path, and (future) LLVM2 JIT-emitted IR (Phase 2, #4198) — must funnel
/// through this function so the entire BFS seen-set is in a single hash
/// domain (xxh3 + `FLAT_COMPILED_DOMAIN_SEED`). Adding a sibling hash
/// function or a sibling seed without converting all compiled-path callers
/// reintroduces the latent divergence this guard closes; see
/// `designs/2026-04-20-llvm2-fingerprint-unification.md`.
#[must_use]
#[inline]
pub(crate) fn fingerprint_flat_compiled(state: &[i64]) -> crate::Fingerprint {
    crate::Fingerprint(crate::state::flat_fingerprint::fingerprint_flat_xxh3_u64_with_seed(
        state,
        crate::state::flat_fingerprint::FLAT_COMPILED_DOMAIN_SEED,
    ))
}

/// Canonical extern for compiled fingerprint — xxh3-64 with the shared domain
/// seed.
///
/// This is the single `#[no_mangle]` symbol that LLVM2-emitted IR (Phase 2,
/// #4198) calls to fingerprint a flat `[i64]` state buffer in-lane, without
/// returning through the Rust driver. The Rust driver fingerprint path
/// (`fingerprint_flat_compiled` above) hashes the *same* buffer through the
/// *same* xxh3 + `FLAT_COMPILED_DOMAIN_SEED` pipeline, so the BFS dedup set
/// is always in a single hash domain regardless of which side computed the
/// fingerprint.
///
/// Phase 1 (#4319) ships this symbol definition only; the compiled IR still
/// calls `jit_xxh3_fingerprint_64` via `runtime_abi::fingerprint`. Phase 2
/// retargets `compiled_fingerprint.rs` to emit calls to this symbol instead.
///
/// # Soundness contract
///
/// The interpreter path MUST NOT call this function. The interpreter
/// fingerprints `OrdMap<Arc<str>, Value>` states via FNV-1a / FP64 in
/// `crate::state::value_hash_state`, which is a different hash family. Mixing
/// the two within one BFS run is a soundness violation — see the Phase 0
/// mixed-mode guard installed by TL69 in `state_fingerprint` and the design
/// doc `designs/2026-04-20-llvm2-fingerprint-unification.md`.
///
/// # Safety
///
/// * `buf` must point to `len` initialised `u8` values (typically the byte
///   reinterpretation of an `[i64; len / 8]` slice, matching the caller side
///   of the existing `jit_xxh3_fingerprint_64` ABI).
/// * The referenced memory must remain valid for the duration of the call.
///
/// Part of #4319 Phase 1. Shared by compiled Rust and (Phase 2) JIT-emitted
/// IR. Do NOT add sibling xxh3 helpers without converting all compiled-path
/// callers — the single-symbol invariant is the soundness property.
#[no_mangle]
pub unsafe extern "C" fn tla2_compiled_fp_u64(buf: *const u8, len: usize) -> u64 {
    if len == 0 {
        return crate::state::flat_fingerprint::fingerprint_flat_xxh3_u64_with_seed(
            &[],
            crate::state::flat_fingerprint::FLAT_COMPILED_DOMAIN_SEED,
        );
    }
    // SAFETY: the caller guarantees `buf` points to `len` valid bytes. We
    // reinterpret those bytes as `[i64]` so the call routes through the exact
    // same `fingerprint_flat_xxh3_u64_with_seed` entry point that the Rust
    // driver path uses. `len` is expected to be a multiple of 8 (one i64 per
    // state slot); if it is not, we round down — extra trailing bytes are
    // ignored rather than reinterpreted past the end of a partial slot. The
    // byte-level invariant matches the existing `jit_xxh3_fingerprint_64`
    // helper which today uses the same reinterpretation (see
    // `runtime_abi/fingerprint.rs`).
    let slot_count = len / core::mem::size_of::<i64>();
    let slots = unsafe { core::slice::from_raw_parts(buf.cast::<i64>(), slot_count) };
    crate::state::flat_fingerprint::fingerprint_flat_xxh3_u64_with_seed(
        slots,
        crate::state::flat_fingerprint::FLAT_COMPILED_DOMAIN_SEED,
    )
}

/// Compute a `Fingerprint(u64)` incrementally using a Zobrist table.
///
/// This is the O(k) incremental compiled fingerprinting path. The Zobrist
/// table provides per-slot random values, and the fingerprint is updated by
/// XOR-ing out old contributions and XOR-ing in new ones.
///
/// # Arguments
///
/// * `zobrist` - Pre-computed Zobrist fingerprinter for this state layout.
/// * `base_fp` - The `Fingerprint(u64)` of the parent state.
/// * `changes` - Slot changes as `(slot_index, old_value, new_value)`.
///
/// Returns a new `Fingerprint(u64)` for the successor state.
///
/// Part of #3987 Phase 4: compiled incremental fingerprinting.
#[must_use]
#[inline]
pub(crate) fn fingerprint_flat_compiled_incremental(
    zobrist: &crate::state::flat_fingerprint::ZobristFlatFingerprinter,
    base_fp: crate::Fingerprint,
    changes: &[(usize, i64, i64)],
) -> crate::Fingerprint {
    crate::Fingerprint(zobrist.incremental(base_fp.0, changes))
}

/// Flatten an ArrayState into a compact i64 buffer for JIT evaluation.
///
/// # Compact Buffer Layout
///
/// The buffer contains only the variables listed in `required_vars`, written
/// in the order they appear in that sorted list. JIT-compiled invariants have
/// their `LoadVar` opcodes remapped to compact indices at build time, so
/// `LoadVar { var_idx: 0 }` reads compact slot 0, etc.
///
/// The first `K` slots (where K = `required_vars.len()`) are "index slots":
/// - For scalar variables (Int, Bool): the slot contains the value directly.
/// - For compound variables: the slot contains the offset (in i64-slot units)
///   into this same buffer where the serialized compound data begins.
///
/// Compound data is appended after the K index slots.
///
/// ```text
/// [scalar_val, compound_offset, ..., TAG, len, field1, ...]
///  ^compact_0  ^compact_1            ^compound data for compact_1
/// ```
///
/// When `required_vars` is empty, ALL variables are written (legacy behavior
/// for caches that read every variable).
///
/// Returns `false` if serialization of a required compound value fails
/// (e.g., unsupported value type like ModelValue).
///
/// The caller retains the allocation so the JIT hot path can reuse one
/// buffer across many states instead of allocating per check.
///
/// Part of #3908.
pub(crate) fn flatten_state_to_i64_selective(
    array_state: &ArrayState,
    scratch: &mut Vec<i64>,
    required_vars: &[u16],
) -> bool {
    let compact_values = array_state.values();
    scratch.clear();

    // When required_vars is empty, fall back to writing ALL variables.
    if required_vars.is_empty() {
        let num_vars = compact_values.len();
        if scratch.capacity() < num_vars {
            scratch.reserve(num_vars - scratch.capacity());
        }
        let mut has_compound = false;
        for cv in compact_values.iter() {
            if cv.is_int() {
                scratch.push(cv.as_int());
            } else if cv.is_bool() {
                scratch.push(if cv.as_bool() { 1 } else { 0 });
            } else {
                scratch.push(0);
                has_compound = true;
            }
        }
        if has_compound {
            for (var_idx, cv) in compact_values.iter().enumerate() {
                if cv.is_int() || cv.is_bool() {
                    continue;
                }
                let compound_offset = scratch.len();
                scratch[var_idx] = compound_offset as i64;
                let value = tla_value::Value::from(cv);
                if let Err(e) = tla_jit_runtime::serialize_value(&value, scratch) {
                    static ONCE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
                    if !ONCE.swap(true, std::sync::atomic::Ordering::Relaxed) {
                        eprintln!("[jit-debug] flatten failed at var_idx={var_idx}: {e}, value={value:?}");
                    }
                    scratch.clear();
                    return false;
                }
            }
        }
        return true;
    }

    // Compact path: only write required_vars.len() index slots.
    let num_compact = required_vars.len();
    if scratch.capacity() < num_compact {
        scratch.reserve(num_compact - scratch.capacity());
    }

    // Phase 1: Fill the compact index slots.
    let mut has_required_compound = false;
    for &orig_idx in required_vars {
        let Some(cv) = compact_values.get(orig_idx as usize) else {
            // Variable index out of range — write 0 placeholder.
            scratch.push(0);
            continue;
        };
        if cv.is_int() {
            scratch.push(cv.as_int());
        } else if cv.is_bool() {
            scratch.push(if cv.as_bool() { 1 } else { 0 });
        } else {
            scratch.push(0); // placeholder for compound offset
            has_required_compound = true;
        }
    }

    if !has_required_compound {
        return true;
    }

    // Phase 2: Serialize compound values, patching their compact index slot.
    for (compact_idx, &orig_idx) in required_vars.iter().enumerate() {
        let Some(cv) = compact_values.get(orig_idx as usize) else {
            continue;
        };
        if cv.is_int() || cv.is_bool() {
            continue;
        }
        let compound_offset = scratch.len();
        scratch[compact_idx] = compound_offset as i64;

        let value = tla_value::Value::from(cv);
        if tla_jit_runtime::serialize_value(&value, scratch).is_err() {
            scratch.clear();
            return false;
        }
    }

    true
}

fn jit_verify_results_match(
    left: &Result<Option<String>, CheckError>,
    right: &Result<Option<String>, CheckError>,
) -> bool {
    match (left, right) {
        (Ok(left), Ok(right)) => left == right,
        (Err(left), Err(right)) => format!("{left:?}") == format!("{right:?}"),
        _ => false,
    }
}

fn format_jit_verify_result(result: &Result<Option<String>, CheckError>) -> String {
    match result {
        Ok(Some(invariant)) => format!("Ok(Some({invariant}))"),
        Ok(None) => "Ok(None)".to_string(),
        Err(error) => format!("Err({error:?})"),
    }
}

impl<'a> ModelChecker<'a> {
    /// Record JIT dispatch outcome by deriving counters from invariant count
    /// and unchecked count. Eliminates per-invariant counter increments inside
    /// the `check_all` loop, reducing hot-path overhead.
    #[inline(always)]
    fn record_jit_dispatch_derived(
        &mut self,
        invariant_count: usize,
        unchecked_count: usize,
    ) {
        self.total_invariant_evals += invariant_count;
        let hit = invariant_count.saturating_sub(unchecked_count);
        self.jit_hit += hit;
        // Cannot distinguish fallback from not-compiled without per-invariant
        // counters. Attribute all misses to jit_not_compiled (conservative).
        self.jit_not_compiled += unchecked_count;
    }

    pub(in crate::check) fn log_jit_dispatch_summary(&self) {
        let Some(jit_cache) = self.jit_cache.as_ref() else {
            return;
        };
        if jit_cache.is_empty() {
            return;
        }
        let total = self.total_invariant_evals;
        let pct = |n: usize| -> f64 {
            if total > 0 { n as f64 / total as f64 * 100.0 } else { 0.0 }
        };
        eprintln!(
            "JIT: {} hit ({:.1}%), {} fallback ({:.1}%), {} not compiled ({:.1}%)",
            self.jit_hit, pct(self.jit_hit),
            self.jit_fallback, pct(self.jit_fallback),
            self.jit_not_compiled, pct(self.jit_not_compiled),
        );
    }

    fn cross_check_jit_invariants(
        &mut self,
        array_state: &ArrayState,
        jit_result: Result<Option<String>, CheckError>,
    ) -> Result<Option<String>, CheckError> {
        if !self.config.jit_verify {
            return jit_result;
        }

        self.jit_verify_checked += 1;
        let interpreter_result = crate::checker_ops::check_invariants_array_state(
            &mut self.ctx,
            &self.config.invariants,
            array_state,
        );
        if !jit_verify_results_match(&jit_result, &interpreter_result) {
            self.jit_verify_mismatches += 1;
            eprintln!(
                "[jit-verify] mismatch: jit={} interpreter={}",
                format_jit_verify_result(&jit_result),
                format_jit_verify_result(&interpreter_result),
            );
        }
        interpreter_result
    }

    pub(in crate::check) fn log_jit_verify_summary(&self) {
        if self.config.jit_verify {
            eprintln!(
                "[jit-verify] checked={} mismatches={}",
                self.jit_verify_checked, self.jit_verify_mismatches
            );
        }
    }

    /// Check all invariants for an ArrayState, returning the first violated invariant.
    ///
    /// Delegates to the canonical `checker_ops::check_invariants_array_state` function
    /// shared with the parallel checker path. This is the fast path that uses
    /// pre-compiled invariants to avoid AST traversal. After the compiled/name-based
    /// pass, eval-based state invariants promoted from PROPERTY entries (for example
    /// `[]ENABLED Next`) are checked against the same state.
    ///
    /// Part of #2356 (Phase 2): sequential path now delegates to the shared canonical
    /// implementation instead of maintaining a duplicate copy.
    ///
    /// Part of #3194: when TIR eval mode is active (`TLA2_TIR_EVAL`), selected
    /// invariants are evaluated via the TIR interpreter instead of compiled guards
    /// or AST eval, exercising TIR as a production evaluation path.
    pub(in crate::check::model_checker) fn check_invariants_array(
        &mut self,
        array_state: &ArrayState,
    ) -> Result<Option<String>, CheckError> {
        let mut unchecked_by_jit: Option<Vec<String>> = None;

        // Part of #3582: JIT native code fast path for eligible invariants.
        // Try JIT-compiled invariants first (native code, ~2-5x faster than bytecode VM).
        // For non-JIT invariants or when state vars aren't flattenable, fall through.
        // Part of #3908: Use selective flattening — only serialize compound
        // vars that JIT invariants actually reference. This enables the JIT
        // path even when unreferenced vars have unsupported types (ModelValue).
        if let Some(ref jit_cache) = self.jit_cache {
            if jit_cache.len() == 0 {
                // No JIT-compiled invariants — skip flatten + dispatch overhead.
            } else if flatten_state_to_i64_selective(
                array_state,
                &mut self.jit_state_scratch,
                jit_cache.required_vars(),
            ) {
                // Fast path: when ALL invariants are JIT-compiled, skip the
                // unchecked Vec allocation entirely. This is the common case
                // for specs like EWD998 where 5/5 actions compile.
                if self.jit_all_compiled {
                    let inv_count = self.config.invariants.len();
                    // Use pre-resolved function pointers when available
                    // to eliminate per-invariant HashMap lookups.
                    let (result, needs_fallback) =
                        if let Some(ref resolved) = self.jit_resolved_fns {
                            JitInvariantCacheImpl::check_all_resolved(
                                &self.config.invariants,
                                resolved,
                                &self.jit_state_scratch,
                            )
                        } else {
                            jit_cache.check_all_compiled(
                                &self.config.invariants,
                                &self.jit_state_scratch,
                            )
                        };
                    if !needs_fallback {
                        self.record_jit_dispatch_derived(inv_count, 0);
                        match result {
                            Ok(Some(violated)) => {
                                self.jit_hits += 1;
                                if !self.config.jit_verify {
                                    return Ok(Some(violated.to_string()));
                                }
                                let verified_result = self.cross_check_jit_invariants(
                                    array_state,
                                    Ok(Some(violated.to_string())),
                                );
                                return match verified_result {
                                    Ok(Some(invariant)) => Ok(Some(invariant)),
                                    Ok(None) => {
                                        crate::checker_ops::check_eval_state_invariants(
                                            &mut self.ctx,
                                            &self.compiled.eval_state_invariants,
                                            array_state,
                                        )
                                    }
                                    Err(error) => Err(error),
                                };
                            }
                            Err(_) => {
                                self.jit_misses += 1;
                                // JIT runtime error — fall through to bytecode/tree-walk
                            }
                            Ok(None) => {
                                self.jit_hits += 1;
                                if !self.config.jit_verify {
                                    return crate::checker_ops::check_eval_state_invariants(
                                        &mut self.ctx,
                                        &self.compiled.eval_state_invariants,
                                        array_state,
                                    );
                                }
                                let verified_result =
                                    self.cross_check_jit_invariants(array_state, Ok(None));
                                return match verified_result {
                                    Ok(Some(invariant)) => Ok(Some(invariant)),
                                    Ok(None) => {
                                        crate::checker_ops::check_eval_state_invariants(
                                            &mut self.ctx,
                                            &self.compiled.eval_state_invariants,
                                            array_state,
                                        )
                                    }
                                    Err(error) => Err(error),
                                };
                            }
                        }
                    } else {
                        // Unexpected fallback from check_all_resolved — demote
                        // to non-fast path for all future states.
                        self.jit_all_compiled = false;
                        self.jit_resolved_fns = None;
                        self.jit_misses += 1;
                        // Fall through to bytecode/tree-walk for this state.
                    }
                } else {
                    // Slow path: some invariants are not JIT-compiled, need the
                    // unchecked buffer to identify which ones need fallback.
                    let mut unchecked = Vec::new();
                    let inv_count = self.config.invariants.len();
                    let jit_result = jit_cache.check_all(
                        &self.config.invariants,
                        &self.jit_state_scratch,
                        &mut unchecked,
                    );
                    let unchecked_count = unchecked.len();
                    self.record_jit_dispatch_derived(inv_count, unchecked_count);
                    match jit_result {
                        Ok(Some(violated)) => {
                            self.jit_hits += 1;
                            if !self.config.jit_verify {
                                return Ok(Some(violated.to_string()));
                            }
                            let verified_result = self.cross_check_jit_invariants(
                                array_state,
                                Ok(Some(violated.to_string())),
                            );
                            return match verified_result {
                                Ok(Some(invariant)) => Ok(Some(invariant)),
                                Ok(None) => crate::checker_ops::check_eval_state_invariants(
                                    &mut self.ctx,
                                    &self.compiled.eval_state_invariants,
                                    array_state,
                                ),
                                Err(error) => Err(error),
                            };
                        }
                        Err(_) => {
                            self.jit_misses += 1;
                            // JIT runtime error — fall through to bytecode/tree-walk
                        }
                        Ok(None) => {
                            if unchecked.is_empty() {
                                self.jit_hits += 1;
                                if !self.config.jit_verify {
                                    return crate::checker_ops::check_eval_state_invariants(
                                        &mut self.ctx,
                                        &self.compiled.eval_state_invariants,
                                        array_state,
                                    );
                                }
                                let verified_result =
                                    self.cross_check_jit_invariants(array_state, Ok(None));
                                return match verified_result {
                                    Ok(Some(invariant)) => Ok(Some(invariant)),
                                    Ok(None) => {
                                        crate::checker_ops::check_eval_state_invariants(
                                            &mut self.ctx,
                                            &self.compiled.eval_state_invariants,
                                            array_state,
                                        )
                                    }
                                    Err(error) => Err(error),
                                };
                            }
                            self.jit_misses += 1;
                            // Preserve invariant order on fallback.
                            unchecked_by_jit =
                                Some(unchecked.into_iter().map(str::to_string).collect());
                        }
                    }
                }
            } else {
                self.jit_misses += 1;
            }
        }

        let invariants = unchecked_by_jit
            .as_deref()
            .unwrap_or(&self.config.invariants);

        // Part of #3578: Hybrid bytecode/tree-walking invariant check.
        // Evaluates compiled invariants via bytecode VM, then tree-walks only
        // the invariants that couldn't be compiled. The bytecode VM uses its
        // own register file and state cache, so mixing is safe.
        if self.bytecode.is_some() {
            let (bc_result, unchecked, runtime_failed) = {
                let bytecode = self.bytecode.as_ref().expect("bytecode presence checked");
                Self::check_invariants_via_bytecode(bytecode, invariants, array_state, &self.ctx)
            };
            if let Some(bytecode) = self.bytecode.as_mut() {
                prune_runtime_failing_invariant_bytecode_ops(bytecode, runtime_failed, "bytecode");
                // Part of #3626: if all ops were pruned, drop bytecode entirely so
                // subsequent states skip the bytecode path and use the direct
                // tree-walk path without per-state Vec<String> allocation.
                if bytecode.op_indices.is_empty() {
                    self.bytecode = None;
                }
            }
            match bc_result {
                Ok(Some(invariant)) => return Ok(Some(invariant)),
                Err(error) => return Err(error),
                Ok(None) => {
                    // Bytecode-checked invariants all passed. Tree-walk the rest.
                    if unchecked.is_empty() {
                        return crate::checker_ops::check_eval_state_invariants(
                            &mut self.ctx,
                            &self.compiled.eval_state_invariants,
                            array_state,
                        );
                    }
                    let invariant_result = crate::checker_ops::check_invariants_array_state(
                        &mut self.ctx,
                        &unchecked,
                        array_state,
                    );
                    return match invariant_result {
                        Ok(Some(invariant)) => Ok(Some(invariant)),
                        Ok(None) => crate::checker_ops::check_eval_state_invariants(
                            &mut self.ctx,
                            &self.compiled.eval_state_invariants,
                            array_state,
                        ),
                        Err(error) => Err(error),
                    };
                }
            }
        }

        // Part of #3194: TIR eval mode — evaluate invariants via TIR interpreter.
        let invariant_result = if self
            .tir_parity
            .as_ref()
            .is_some_and(super::super::tir_parity::TirParityState::is_eval_mode)
        {
            self.check_invariants_via_tir(invariants, array_state)
        } else {
            crate::checker_ops::check_invariants_array_state(&mut self.ctx, invariants, array_state)
        };

        debug_block!(debug_invariants(), {
            if let Ok(Some(ref inv_name)) = invariant_result {
                match self.ctx.eval_op(inv_name) {
                    Ok(Value::Bool(true)) => eprintln!("[invariant] {} = TRUE", inv_name),
                    Ok(Value::Bool(false)) => eprintln!("[invariant] {} = FALSE", inv_name),
                    Ok(other) => eprintln!("[invariant] {} = non-boolean ({:?})", inv_name, other),
                    Err(e) => eprintln!("[invariant] {} = error ({}) {:?}", inv_name, e, e),
                }
            }
        });

        match invariant_result {
            Ok(Some(invariant)) => Ok(Some(invariant)),
            Ok(None) => crate::checker_ops::check_eval_state_invariants(
                &mut self.ctx,
                &self.compiled.eval_state_invariants,
                array_state,
            ),
            Err(error) => Err(error),
        }
    }

    /// Evaluate invariants via TIR interpreter (Part of #3194).
    ///
    /// For selected operators that can execute real TIR, evaluates through
    /// `TirProgram::eval_named_op()`. Operators that must AST-fallback keep the
    /// canonical AST / compiled-guard path instead of paying the TIR setup cost.
    fn check_invariants_via_tir(
        &mut self,
        invariants: &[String],
        array_state: &ArrayState,
    ) -> Result<Option<String>, CheckError> {
        // Part of #3354: Always use the canonical array-state invariant check.
        // Evaluates each invariant name via ctx.eval_op(inv_name).
        crate::checker_ops::check_invariants_array_state(&mut self.ctx, invariants, array_state)
    }

    /// Evaluate invariants via bytecode VM (Part of #3578).
    ///
    /// Hybrid approach: evaluates each invariant that has bytecode via the VM
    /// and collects the names of invariants that need tree-walking fallback.
    /// The bytecode VM operates on its own register file and state cache,
    /// independent of the eval cache, so mixing bytecode and tree-walking
    /// per-invariant is safe.
    ///
    /// Returns `(result, unchecked)` where:
    /// - `result` is `Err` on error, `Ok(Some(name))` on violation, `Ok(None)` if all checked passed
    /// - `unchecked` contains invariant names that need tree-walking fallback
    /// - `runtime_failed` contains bytecode operators to prune from future states
    fn check_invariants_via_bytecode(
        bytecode: &tla_eval::bytecode_vm::CompiledBytecode,
        invariants: &[String],
        array_state: &ArrayState,
        eval_ctx: &tla_eval::EvalCtx,
    ) -> (
        Result<Option<String>, CheckError>,
        Vec<String>,
        Vec<(String, String)>,
    ) {
        use tla_eval::bytecode_vm::BytecodeVm;

        let mut unchecked = Vec::new();
        let mut runtime_failed = Vec::new();

        if bytecode.op_indices.is_empty() {
            return (Ok(None), invariants.to_vec(), runtime_failed);
        }

        // Keep the invariant fast path on compact state storage and let the VM
        // reuse memoized slot decodes across all invariants for this state.
        let mut vm = BytecodeVm::from_state_env(&bytecode.chunk, array_state.env_ref(), None)
            .with_eval_ctx(eval_ctx);

        for inv_name in invariants {
            let Some(&func_idx) = bytecode.op_indices.get(inv_name) else {
                unchecked.push(inv_name.clone());
                continue;
            };

            match vm.execute_function(func_idx) {
                Ok(tla_value::Value::Bool(true)) => {
                    tla_eval::note_bytecode_vm_execution();
                }
                Ok(tla_value::Value::Bool(false)) => {
                    tla_eval::note_bytecode_vm_execution();
                    return (Ok(Some(inv_name.clone())), unchecked, runtime_failed);
                }
                Ok(_) => {
                    tla_eval::note_bytecode_vm_execution();
                    return (
                        Err(crate::EvalCheckError::InvariantNotBoolean(inv_name.clone()).into()),
                        unchecked,
                        runtime_failed,
                    );
                }
                Err(error) => {
                    tla_eval::note_bytecode_vm_fallback();
                    // VM execution error — fall back to tree-walking for this invariant.
                    unchecked.push(inv_name.clone());
                    runtime_failed.push((inv_name.clone(), error.to_string()));
                }
            }
        }

        (Ok(None), unchecked, runtime_failed)
    }

    /// TIR-based successor invariant checking (Part of #3194).
    ///
    /// Like `check_invariants_via_tir` but returns `InvariantOutcome` and sets
    /// TLC level for successor state semantics. Eval-based state invariants
    /// (ENABLED-containing) still use the canonical AST path.
    /// Scaffolding — not yet wired into production BFS.
    #[allow(dead_code)]
    pub(in crate::check) fn check_successor_invariant_via_tir(
        &mut self,
        succ: &ArrayState,
        succ_fp: Fingerprint,
        succ_level: u32,
    ) -> InvariantOutcome {
        if self.config.invariants.is_empty() && self.compiled.eval_state_invariants.is_empty() {
            return InvariantOutcome::Ok;
        }

        self.ctx.set_tlc_level(succ_level);

        // Part of #3391/#3465: Use the canonical array-bound eval boundary helper.
        crate::eval::clear_for_bound_state_eval_scope(&self.ctx);

        match crate::checker_ops::check_invariants_array_state(
            &mut self.ctx,
            &self.config.invariants,
            succ,
        ) {
            Ok(None) => {}
            Ok(Some(invariant)) => {
                return InvariantOutcome::Violation {
                    invariant,
                    state_fp: succ_fp,
                };
            }
            Err(e) => {
                return InvariantOutcome::Error(e);
            }
        }

        // Eval-based state invariants (ENABLED-containing) still use AST path.
        match crate::checker_ops::check_eval_state_invariants(
            &mut self.ctx,
            &self.compiled.eval_state_invariants,
            succ,
        ) {
            Ok(None) => InvariantOutcome::Ok,
            Ok(Some(invariant)) => InvariantOutcome::Violation {
                invariant,
                state_fp: succ_fp,
            },
            Err(e) => InvariantOutcome::Error(e),
        }
    }
}

// ============================================================================
// Tests for tla2_compiled_fp_u64 canonical extern (#4319 Phase 1)
// ============================================================================
#[cfg(test)]
mod canonical_extern_tests {
    use super::{fingerprint_flat_compiled, tla2_compiled_fp_u64};
    use crate::state::flat_fingerprint::{
        fingerprint_flat_xxh3_u64_with_seed, FLAT_COMPILED_DOMAIN_SEED,
    };

    /// Re-hash a flat `[i64]` buffer through `tla2_compiled_fp_u64` exactly
    /// how (Phase 2) JIT-emitted IR will call it: as a raw `*const u8` / `len`
    /// byte pair. Used by the parity tests below.
    fn call_extern(state: &[i64]) -> u64 {
        let bytes_len = state.len() * core::mem::size_of::<i64>();
        let byte_ptr = state.as_ptr().cast::<u8>();
        // SAFETY: `state` is a valid slice, so `byte_ptr` + `bytes_len` is a
        // valid byte range covering exactly the state's storage.
        unsafe { tla2_compiled_fp_u64(byte_ptr, bytes_len) }
    }

    #[test]
    fn tla2_compiled_fp_u64_matches_xxh3_direct() {
        // For every fixture, the extern must equal the canonical Rust entry
        // point `fingerprint_flat_xxh3_u64_with_seed(state, SEED)`. If this
        // ever diverges, the Phase 2 IR wiring and the Rust driver path will
        // hash identical buffers into different domains — the exact
        // soundness violation #4319 Phase 1 exists to prevent.
        let fixtures: &[&[i64]] = &[
            &[],
            &[0],
            &[1, 2, 3, 4, 5],
            &[i64::MAX, i64::MIN, 0, -1, 1],
            &[42, -7, 99, 1_000_000, -1_000_000, 0, 0, 0],
        ];
        for state in fixtures {
            let via_extern = call_extern(state);
            let via_rust =
                fingerprint_flat_xxh3_u64_with_seed(state, FLAT_COMPILED_DOMAIN_SEED);
            assert_eq!(
                via_extern, via_rust,
                "tla2_compiled_fp_u64 must equal fingerprint_flat_xxh3_u64_with_seed(SEED) for state {:?}",
                state,
            );

            // And it must equal the Rust driver's wrapper exactly — this is
            // the invariant Phase 2 depends on.
            let via_driver = fingerprint_flat_compiled(state).0;
            assert_eq!(
                via_extern, via_driver,
                "tla2_compiled_fp_u64 must equal fingerprint_flat_compiled for state {:?}",
                state,
            );
        }
    }

    #[test]
    fn tla2_compiled_fp_u64_empty_input_matches_seeded_xxh3() {
        // Empty buffer must still apply FLAT_COMPILED_DOMAIN_SEED, so the
        // empty-state fingerprint is distinct from the default xxh3(empty)
        // value. This pins that the seed is threaded end-to-end rather than
        // dropped when len == 0.
        let empty: &[i64] = &[];
        // SAFETY: null / 0 is a valid empty-buffer encoding per our own
        // impl contract — the function short-circuits on len == 0.
        let fp_via_null = unsafe { tla2_compiled_fp_u64(core::ptr::null(), 0) };
        let fp_via_nonnull = call_extern(empty);
        let expected = fingerprint_flat_xxh3_u64_with_seed(empty, FLAT_COMPILED_DOMAIN_SEED);
        assert_eq!(fp_via_null, expected, "null-ptr/zero-len must equal seeded empty xxh3");
        assert_eq!(
            fp_via_nonnull, expected,
            "nonnull/zero-len must equal seeded empty xxh3",
        );

        // Regression guard on domain separation: empty-seed != empty-unseeded.
        let unseeded = xxhash_rust::xxh3::xxh3_64(&[]);
        assert_ne!(
            expected, unseeded,
            "FLAT_COMPILED_DOMAIN_SEED must shift the empty-state fingerprint away \
             from the default xxh3 seed-zero domain (#4215)",
        );
    }

    #[test]
    fn tla2_compiled_fp_u64_stability() {
        // Two calls on the same input, separated by an unrelated call on a
        // different input, must return the same hash. This guards against
        // accidental dependence on call history (e.g. TLS state, mutable
        // statics) that an extern "C" symbol must never acquire.
        let state_a: &[i64] = &[1, 2, 3, 4, 5];
        let state_b: &[i64] = &[99, 99, 99];
        let first = call_extern(state_a);
        let _noise = call_extern(state_b);
        let second = call_extern(state_a);
        assert_eq!(
            first, second,
            "tla2_compiled_fp_u64 must be a pure function of its input",
        );
    }
}
