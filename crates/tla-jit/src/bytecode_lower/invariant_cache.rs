// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! JIT invariant cache: holds compiled native invariant functions.
//!
//! `JitInvariantCache` is constructed at model checker startup time by
//! attempting to JIT-compile each bytecode invariant. At check time, the cache
//! provides O(1) lookup from invariant name to native function pointer.

use crate::abi::{JitCallOut, JitInvariantFn, JitStatus};
use crate::compound_layout::StateLayout;
use crate::error::JitError;
use rustc_hash::{FxHashMap, FxHashSet};
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};

use super::check_eligibility_with_constants;
use super::compile_common::collect_loadvar_indices;
use super::inliner::BytecodeInliner;
use super::BytecodeLowerer;

/// Result of checking a single invariant via JIT.
///
/// Richer than `Option<Result<bool, JitError>>` — distinguishes between
/// full fallback (not compiled or entirely compound) and partial pass
/// (scalar conjuncts verified, compound conjuncts need interpreter).
#[derive(Debug)]
pub enum JitInvariantResult {
    /// Invariant fully evaluated by JIT: holds (true) or violated (false).
    Complete(bool),
    /// JIT runtime error occurred.
    Error(JitError),
    /// Invariant is not in the JIT cache (not compiled or ineligible).
    /// Caller must evaluate the entire invariant via interpreter.
    NotCompiled,
    /// Invariant is JIT-compiled but returned FallbackNeeded at runtime.
    /// Caller must evaluate the entire invariant via interpreter.
    FallbackNeeded,
    /// JIT evaluated some scalar conjuncts and they all passed, but could
    /// not evaluate the compound conjuncts. `conjuncts_passed` indicates
    /// how many top-level conjuncts were verified. The caller can skip
    /// those conjuncts when falling back to the interpreter.
    PartialPass {
        /// Number of top-level conjuncts verified by JIT.
        conjuncts_passed: u32,
    },
}

/// Per-dispatch outcome counters for JIT invariant evaluation profiling.
///
/// Tracks how each invariant dispatch was resolved:
/// - `jit_hit`: invariant was fully evaluated by JIT native code (pass or fail).
/// - `jit_fallback`: invariant was JIT-compiled but returned `FallbackNeeded`
///   at runtime (e.g., compound-value opcode encountered).
/// - `jit_not_compiled`: invariant was not present in the JIT cache at all.
/// - `jit_error`: JIT evaluation returned a runtime error.
/// - `total`: total number of individual invariant dispatch attempts.
///
/// Part of #3935.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct JitDispatchCounters {
    /// Invariant fully evaluated by JIT (pass or violation).
    pub jit_hit: usize,
    /// Invariant is JIT-compiled but returned FallbackNeeded at runtime.
    pub jit_fallback: usize,
    /// Invariant is not in the JIT cache (not compiled or ineligible).
    pub jit_not_compiled: usize,
    /// JIT evaluation returned a runtime error.
    pub jit_error: usize,
    /// Total individual invariant dispatch attempts.
    pub total: usize,
}

/// Build a compact `StateLayout` from the original layout by extracting
/// only the variables at the given indices (in order).
///
/// The resulting layout has `required_vars.len()` entries, where entry `i`
/// corresponds to original variable `required_vars[i]`. Variables beyond
/// the original layout's range get a default `ScalarInt` layout.
///
/// Part of #3909.
fn remap_state_layout(original: &StateLayout, required_vars: &[u16]) -> StateLayout {
    use crate::compound_layout::VarLayout;
    let vars: Vec<VarLayout> = required_vars
        .iter()
        .map(|&orig_idx| {
            original
                .var_layout(orig_idx as usize)
                .cloned()
                .unwrap_or(VarLayout::ScalarInt)
        })
        .collect();
    StateLayout::new(vars)
}

/// Build a callee map for bytecode inlining: scans all eligible functions
/// for `Call { op_idx }` references and collects their callee bytecode
/// functions from the chunk. Recurses up to `max_depth` to capture
/// transitively-called functions.
///
/// Part of #3950.
fn build_callee_map(
    chunk: &BytecodeChunk,
    eligible_entries: &[(String, u16)],
    max_depth: usize,
) -> std::collections::HashMap<u16, BytecodeFunction> {
    let mut callee_map = std::collections::HashMap::new();
    let mut frontier: Vec<u16> = Vec::new();
    let mut frontier_set = FxHashSet::default();

    // Collect direct Call targets from all eligible functions
    for (_name, func_idx) in eligible_entries {
        let func = &chunk.functions[*func_idx as usize];
        for op in &func.instructions {
            if let Opcode::Call { op_idx, .. } = *op {
                if !callee_map.contains_key(&op_idx) && frontier_set.insert(op_idx) {
                    frontier.push(op_idx);
                }
            }
        }
    }

    // Resolve transitive callees up to max_depth
    for _depth in 0..max_depth {
        if frontier.is_empty() {
            break;
        }
        let mut next_frontier = Vec::new();
        let mut next_frontier_set = FxHashSet::default();
        for op_idx in frontier.drain(..) {
            if callee_map.contains_key(&op_idx) {
                continue;
            }
            if let Some(callee) = chunk.functions.get(op_idx as usize) {
                // Scan callee for its own Call targets
                for op in &callee.instructions {
                    if let Opcode::Call { op_idx: nested, .. } = *op {
                        if !callee_map.contains_key(&nested) && next_frontier_set.insert(nested) {
                            next_frontier.push(nested);
                        }
                    }
                }
                callee_map.insert(op_idx, callee.clone());
            }
        }
        frontier = next_frontier;
        frontier_set = next_frontier_set;
    }

    callee_map
}

/// Clone a bytecode function, rewriting all `LoadVar` opcodes to use
/// compact slot indices from `var_remap`. The resulting function reads
/// from a compact state buffer instead of the full N-variable array.
fn remap_loadvar_indices(
    func: &BytecodeFunction,
    var_remap: &FxHashMap<u16, u16>,
) -> BytecodeFunction {
    let mut remapped = func.clone();
    for op in &mut remapped.instructions {
        if let Opcode::LoadVar { var_idx, .. } = op {
            if let Some(&compact_idx) = var_remap.get(var_idx) {
                *var_idx = compact_idx;
            }
        }
    }
    remapped
}

/// Cache of JIT-compiled invariant functions.
///
/// Built once at startup, queried per-state during model checking.
/// Tracks which state variables each invariant references, enabling
/// selective state flattening (Part of #3908).
///
/// # Compact State Buffer
///
/// JIT-compiled invariants use a **compact** state buffer that only
/// contains the variables they actually read. At build time, `LoadVar`
/// opcodes are rewritten from original `VarIdx` to compact slot indices.
/// At check time, the caller flattens only `required_vars` into a
/// compact buffer of length `required_vars.len()` (plus compound data),
/// which the JIT code reads via the remapped indices.
///
/// Example: if a spec has 10 state variables but JIT invariants only
/// read vars 2 and 7, the compact buffer has 2 index slots (not 10).
/// `LoadVar { var_idx: 2 }` is rewritten to `LoadVar { var_idx: 0 }`,
/// `LoadVar { var_idx: 7 }` → `LoadVar { var_idx: 1 }`.
pub struct JitInvariantCache {
    /// Owns the JIT module backing `functions`; dropping it invalidates pointers.
    _lowerer: BytecodeLowerer,
    /// Map from invariant name to native function pointer.
    functions: FxHashMap<String, JitInvariantFn>,
    /// Union of all `VarIdx` values referenced by any JIT-compiled invariant.
    /// Sorted, deduplicated. Used by the caller to selectively flatten only
    /// the state variables that JIT invariants actually read.
    /// Part of #3908.
    required_vars: Vec<u16>,
    /// Maps original VarIdx → compact slot index in the JIT state buffer.
    /// Built from `required_vars`: required_vars[i] maps to compact index i.
    /// Used by `flatten_state_to_i64_compact` to build the compact buffer.
    var_remap: FxHashMap<u16, u16>,
}

// SAFETY: After construction, the cache is immutable. The stored function
// pointers target finalized machine code owned by `_lowerer`, and `_lowerer`
// is retained for the cache lifetime so the backing memory stays valid.
unsafe impl Send for JitInvariantCache {}
// SAFETY: Concurrent callers only read immutable maps and invoke finalized code
// with caller-owned input/output buffers; the cache itself has no mutation.
unsafe impl Sync for JitInvariantCache {}

impl JitInvariantCache {
    /// Build a JIT invariant cache from a bytecode chunk and operator index.
    ///
    /// Uses a two-pass approach for compact state buffer optimization:
    ///
    /// **Pass 1**: Collect all `VarIdx` values from eligible functions to
    /// build the union set `required_vars` and the `var_remap` table.
    ///
    /// **Pass 2**: For each eligible function, clone it, rewrite `LoadVar`
    /// opcodes to use compact indices from `var_remap`, then JIT-compile.
    /// The resulting native code reads from a compact state buffer that
    /// only contains the required variables.
    ///
    /// Functions that are not eligible or fail compilation are silently
    /// skipped (the bytecode VM or tree-walker handles them instead).
    pub fn build(
        chunk: &BytecodeChunk,
        op_indices: &FxHashMap<String, u16>,
    ) -> Result<Self, JitError> {
        // Pass 0: Collect eligible entries (pre-inlining eligibility check).
        let mut eligible_entries: Vec<(String, u16)> = Vec::new();

        for (name, &func_idx) in op_indices {
            let func = chunk.functions.get(func_idx as usize).ok_or_else(|| {
                JitError::CompileError(format!(
                    "operator index {func_idx} for invariant {name} is out of range ({} functions)",
                    chunk.functions.len()
                ))
            })?;
            if check_eligibility_with_constants(func, Some(&chunk.constants)).is_err() {
                continue;
            }
            eligible_entries.push((name.clone(), func_idx));
        }

        // Pass 0.5: Inline Call opcodes so JIT sees flat bytecode.
        // Part of #3950.
        let callee_map = build_callee_map(chunk, &eligible_entries, 4);
        let mut inlined_funcs: Vec<(String, BytecodeFunction)> = Vec::new();
        for (name, func_idx) in &eligible_entries {
            let func = &chunk.functions[*func_idx as usize];
            let inlined = if callee_map.is_empty() {
                func.clone()
            } else {
                match BytecodeInliner::inline(func, &callee_map, 4) {
                    Ok(f) => f,
                    Err(_) => func.clone(),
                }
            };
            inlined_funcs.push((name.clone(), inlined));
        }

        // Pass 1: Collect all VarIdx values from inlined functions.
        let mut all_var_set = FxHashSet::default();
        let mut all_var_indices: Vec<u16> = Vec::new();
        for (_name, func) in &inlined_funcs {
            let var_indices = collect_loadvar_indices(func);
            for &idx in &var_indices {
                if all_var_set.insert(idx) {
                    all_var_indices.push(idx);
                }
            }
        }

        all_var_indices.sort_unstable();

        // Build the var_remap: original VarIdx → compact slot index.
        let var_remap: FxHashMap<u16, u16> = all_var_indices
            .iter()
            .enumerate()
            .map(|(compact_idx, &orig_idx)| (orig_idx, compact_idx as u16))
            .collect();

        // Pass 2: Compile each inlined function with remapped LoadVar indices.
        let mut lowerer = BytecodeLowerer::new()?;
        let mut functions = FxHashMap::default();

        for (name, func) in &inlined_funcs {
            let remapped = remap_loadvar_indices(func, &var_remap);

            match lowerer.compile_invariant_with_constants(&remapped, &chunk.constants) {
                Ok(Some(jit_fn)) => {
                    functions.insert(name.clone(), jit_fn);
                }
                Ok(None) => {
                    // Not eligible after remap — fall back to bytecode VM
                }
                Err(_) => {
                    // Compilation error — fall back to bytecode VM
                }
            }
        }

        Ok(JitInvariantCache {
            _lowerer: lowerer,
            functions,
            required_vars: all_var_indices,
            var_remap,
        })
    }

    /// Build a JIT invariant cache with state layout information for native
    /// compound-value access (RecordGet, FuncApply, TupleGet).
    ///
    /// When a `StateLayout` is provided, the compiler resolves record field
    /// accesses to direct slot loads instead of emitting `FallbackNeeded`.
    /// The layout is remapped to match the compact state buffer so that
    /// compound variable offsets remain correct after `LoadVar` remapping.
    ///
    /// Part of #3909.
    pub fn build_with_layout(
        chunk: &BytecodeChunk,
        op_indices: &FxHashMap<String, u16>,
        state_layout: &StateLayout,
    ) -> Result<Self, JitError> {
        // Pass 0: Collect eligible entries (pre-inlining eligibility check).
        let mut eligible_entries: Vec<(String, u16)> = Vec::new();

        for (name, &func_idx) in op_indices {
            let func = chunk.functions.get(func_idx as usize).ok_or_else(|| {
                JitError::CompileError(format!(
                    "operator index {func_idx} for invariant {name} is out of range ({} functions)",
                    chunk.functions.len()
                ))
            })?;
            if check_eligibility_with_constants(func, Some(&chunk.constants)).is_err() {
                continue;
            }
            eligible_entries.push((name.clone(), func_idx));
        }

        // Pass 0.5: Build callee map and inline Call opcodes into each
        // eligible function. After inlining, functions no longer contain
        // Call opcodes and can be JIT-compiled end-to-end.
        // Part of #3950.
        let callee_map = build_callee_map(chunk, &eligible_entries, 4);

        let mut inlined_funcs: Vec<(String, BytecodeFunction)> = Vec::new();
        for (name, func_idx) in &eligible_entries {
            let func = &chunk.functions[*func_idx as usize];
            let inlined = if callee_map.is_empty() {
                func.clone()
            } else {
                match BytecodeInliner::inline(func, &callee_map, 4) {
                    Ok(f) => f,
                    Err(_) => func.clone(), // register overflow → use original
                }
            };
            inlined_funcs.push((name.clone(), inlined));
        }

        // Pass 1: Collect all VarIdx values from inlined functions.
        let mut all_var_set = FxHashSet::default();
        let mut all_var_indices: Vec<u16> = Vec::new();
        for (_name, func) in &inlined_funcs {
            let var_indices = collect_loadvar_indices(func);
            for &idx in &var_indices {
                if all_var_set.insert(idx) {
                    all_var_indices.push(idx);
                }
            }
        }

        all_var_indices.sort_unstable();

        let var_remap: FxHashMap<u16, u16> = all_var_indices
            .iter()
            .enumerate()
            .map(|(compact_idx, &orig_idx)| (orig_idx, compact_idx as u16))
            .collect();

        // Build a compact StateLayout that matches the remapped var indices.
        let compact_layout = remap_state_layout(state_layout, &all_var_indices);
        let field_name_ids = chunk.constants.field_ids();

        // Pass 2: Compile each inlined function with remapped LoadVar indices
        // and compound layout info.
        let mut lowerer = BytecodeLowerer::new()?;
        let mut functions = FxHashMap::default();

        for (name, func) in &inlined_funcs {
            let remapped = remap_loadvar_indices(func, &var_remap);

            match lowerer.compile_invariant_with_constants_and_layout(
                &remapped,
                &chunk.constants,
                &compact_layout,
                field_name_ids,
            ) {
                Ok(Some(jit_fn)) => {
                    functions.insert(name.clone(), jit_fn);
                }
                Ok(None) => {
                    // Not eligible after remap — fall back to bytecode VM
                }
                Err(_) => {
                    // Compilation error — fall back to bytecode VM
                }
            }
        }

        Ok(JitInvariantCache {
            _lowerer: lowerer,
            functions,
            required_vars: all_var_indices,
            var_remap,
        })
    }

    /// Check if any invariants were JIT-compiled.
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }

    /// Number of JIT-compiled invariants.
    pub fn len(&self) -> usize {
        self.functions.len()
    }

    /// Sorted, deduplicated list of `VarIdx` values referenced by any
    /// JIT-compiled invariant's `LoadVar` opcodes. The caller uses this
    /// to selectively flatten only the required state variables, skipping
    /// compound serialization for unreferenced variables.
    /// Part of #3908.
    pub fn required_vars(&self) -> &[u16] {
        &self.required_vars
    }

    /// Maps original VarIdx to compact slot index. Used by the flatten
    /// function to build the compact state buffer that JIT code reads.
    /// Part of #3908.
    pub fn var_remap(&self) -> &FxHashMap<u16, u16> {
        &self.var_remap
    }

    /// Number of compact slots (= `required_vars.len()`). This is the
    /// number of index slots in the compact state buffer before compound
    /// data is appended.
    pub fn compact_slot_count(&self) -> usize {
        self.required_vars.len()
    }

    /// Check an invariant against a flattened i64 state array.
    ///
    /// Returns a `JitInvariantResult` distinguishing between:
    /// - `Complete(true)` — invariant holds (all conjuncts passed)
    /// - `Complete(false)` — invariant violated
    /// - `Error(_)` — JIT runtime error
    /// - `NotCompiled` — invariant not in JIT cache
    /// - `FallbackNeeded` — compiled but hit compound op at runtime
    /// - `PartialPass { conjuncts_passed }` — scalar conjuncts passed,
    ///   compound conjuncts need interpreter
    ///
    /// # Safety
    ///
    /// `state` must point to a valid array of at least `state_len` i64 values.
    /// The caller is responsible for decoding CompactValue state to i64.
    pub fn check_invariant_rich(&self, name: &str, state: &[i64]) -> JitInvariantResult {
        let jit_fn = match self.functions.get(name) {
            Some(f) => f,
            None => return JitInvariantResult::NotCompiled,
        };

        let mut out = JitCallOut::default();
        // SAFETY: state points to a valid i64 slice, out is a valid JitCallOut.
        unsafe {
            jit_fn(&mut out, state.as_ptr(), state.len() as u32);
        }

        match out.status {
            JitStatus::Ok => {
                // Bool result: 0 = false (violation), nonzero = true (holds)
                JitInvariantResult::Complete(out.value != 0)
            }
            JitStatus::RuntimeError => {
                JitInvariantResult::Error(JitError::RuntimeError { kind: out.err_kind })
            }
            JitStatus::FallbackNeeded => JitInvariantResult::FallbackNeeded,
            JitStatus::PartialPass => JitInvariantResult::PartialPass {
                conjuncts_passed: out.conjuncts_passed,
            },
        }
    }

    /// Check an invariant against a flattened i64 state array.
    ///
    /// Returns:
    /// - `Some(true)` if the invariant holds
    /// - `Some(false)` if the invariant is violated
    /// - `None` if the invariant is not JIT-compiled or needs fallback
    ///
    /// This is the legacy API. Prefer `check_invariant_rich` for new code
    /// that can handle partial passes.
    ///
    /// # Safety
    ///
    /// `state` must point to a valid array of at least `state_len` i64 values.
    /// The caller is responsible for decoding CompactValue state to i64.
    pub fn check_invariant(&self, name: &str, state: &[i64]) -> Option<Result<bool, JitError>> {
        match self.check_invariant_rich(name, state) {
            JitInvariantResult::Complete(b) => Some(Ok(b)),
            JitInvariantResult::Error(e) => Some(Err(e)),
            JitInvariantResult::NotCompiled
            | JitInvariantResult::FallbackNeeded
            | JitInvariantResult::PartialPass { .. } => None,
        }
    }

    /// Check whether ALL invariants are JIT-compiled.
    ///
    /// When true, `resolve_ordered` can be used to build a pre-resolved
    /// function pointer list for the zero-overhead `check_all_resolved`
    /// fast path.
    pub fn covers_all(&self, invariants: &[String]) -> bool {
        invariants
            .iter()
            .all(|name| self.functions.contains_key(name))
    }

    /// Resolve invariant names to native function pointers in the given order.
    ///
    /// Returns `Some(vec)` if all invariants are JIT-compiled, `None` if any
    /// is missing. The returned Vec has the same length and order as
    /// `invariants`, enabling `check_all_resolved` to iterate by index
    /// without any HashMap lookups in the hot path.
    pub fn resolve_ordered(&self, invariants: &[String]) -> Option<Vec<JitInvariantFn>> {
        let mut resolved = Vec::with_capacity(invariants.len());
        for name in invariants {
            match self.functions.get(name) {
                Some(&f) => resolved.push(f),
                None => return None,
            }
        }
        Some(resolved)
    }

    /// Check all invariants using pre-resolved function pointers.
    ///
    /// This is the zero-allocation, zero-lookup fast path: no `unchecked`
    /// buffer, no HashMap lookups, no per-invariant struct initialization
    /// beyond the single `JitCallOut` that is reused across calls.
    ///
    /// `resolved_fns` must have been obtained from `resolve_ordered` with
    /// the same `invariants` slice and same order.
    ///
    /// Returns `(result, needs_fallback)`. When `needs_fallback` is true,
    /// the caller must re-check ALL invariants via the interpreter.
    #[inline]
    pub fn check_all_resolved<'a>(
        invariants: &'a [String],
        resolved_fns: &[JitInvariantFn],
        state: &[i64],
    ) -> (Result<Option<&'a str>, JitError>, bool) {
        debug_assert_eq!(invariants.len(), resolved_fns.len());
        let state_ptr = state.as_ptr();
        let state_len = state.len() as u32;
        let mut out = JitCallOut::default();
        for (inv_name, jit_fn) in invariants.iter().zip(resolved_fns.iter()) {
            // SAFETY: state points to a valid i64 slice, out is a valid JitCallOut.
            unsafe {
                jit_fn(&mut out, state_ptr, state_len);
            }
            match out.status {
                JitStatus::Ok => {
                    if out.value == 0 {
                        // Violation detected.
                        return (Ok(Some(inv_name)), false);
                    }
                    // Passed — continue to next invariant.
                }
                JitStatus::RuntimeError => {
                    return (Err(JitError::RuntimeError { kind: out.err_kind }), false);
                }
                JitStatus::FallbackNeeded | JitStatus::PartialPass => {
                    return (Ok(None), true);
                }
            }
        }
        (Ok(None), false)
    }

    /// Check all invariants when every invariant is known to be JIT-compiled.
    ///
    /// This is the zero-allocation fast path: no `unchecked` buffer needed.
    /// Returns `Ok(Some(name))` on first violation, `Ok(None)` if all pass,
    /// or `Err` on JIT runtime error. `FallbackNeeded`/`PartialPass` results
    /// are treated as errors (return `Err`) since the caller expected full
    /// coverage — the caller should fall through to the interpreter.
    ///
    /// Returns `(result, needs_fallback)`. When `needs_fallback` is true,
    /// the caller must re-check ALL invariants via the interpreter (a
    /// FallbackNeeded was encountered). When false, the result is definitive.
    #[inline]
    pub fn check_all_compiled<'a>(
        &self,
        invariants: &'a [String],
        state: &[i64],
    ) -> (Result<Option<&'a str>, JitError>, bool) {
        for inv_name in invariants.iter() {
            match self.check_invariant_rich(inv_name, state) {
                JitInvariantResult::Complete(true) => {} // passed
                JitInvariantResult::Complete(false) => {
                    return (Ok(Some(inv_name)), false);
                }
                JitInvariantResult::Error(e) => return (Err(e), false),
                JitInvariantResult::NotCompiled
                | JitInvariantResult::FallbackNeeded
                | JitInvariantResult::PartialPass { .. } => {
                    // Unexpected fallback — caller must use interpreter.
                    return (Ok(None), true);
                }
            }
        }
        (Ok(None), false)
    }

    /// Check all JIT-compiled invariants against a state.
    ///
    /// Returns the name of the first violated invariant, or `None` if all pass.
    /// Invariants that need fallback (not compiled, FallbackNeeded, or PartialPass)
    /// are added to `unchecked` individually — unlike the old behavior, we do NOT
    /// bail on the first unchecked invariant. This allows subsequent invariants
    /// to still benefit from JIT evaluation.
    ///
    /// Correctness: invariant violations are definitive (if JIT says false, it IS
    /// false). Passes are also definitive for Complete results. For FallbackNeeded
    /// or PartialPass, the invariant is added to unchecked for interpreter re-check.
    /// The interpreter will check unchecked invariants in their original relative
    /// order, preserving TLC-compatible violation reporting order.
    pub fn check_all<'a>(
        &self,
        invariants: &'a [String],
        state: &[i64],
        unchecked: &mut Vec<&'a str>,
    ) -> Result<Option<&'a str>, JitError> {
        for inv_name in invariants.iter() {
            match self.check_invariant_rich(inv_name, state) {
                JitInvariantResult::Complete(true) => {} // passed
                JitInvariantResult::Complete(false) => return Ok(Some(inv_name)),
                JitInvariantResult::Error(e) => return Err(e),
                JitInvariantResult::NotCompiled
                | JitInvariantResult::FallbackNeeded
                | JitInvariantResult::PartialPass { .. } => {
                    // Add this specific invariant to unchecked, but continue
                    // checking remaining invariants via JIT.
                    unchecked.push(inv_name.as_str());
                }
            }
        }
        Ok(None)
    }

    /// Check all JIT-compiled invariants against a state, recording per-dispatch
    /// outcome counters for profiling.
    ///
    /// Like [`check_all`], does NOT bail on the first unchecked invariant —
    /// continues checking all invariants via JIT, adding fallback/partial-pass
    /// invariants to `unchecked` individually.
    ///
    /// Part of #3935.
    pub fn check_all_with_counters<'a>(
        &self,
        invariants: &'a [String],
        state: &[i64],
        unchecked: &mut Vec<&'a str>,
        counters: &mut JitDispatchCounters,
    ) -> Result<Option<&'a str>, JitError> {
        for inv_name in invariants.iter() {
            counters.total += 1;
            match self.check_invariant_rich(inv_name, state) {
                JitInvariantResult::Complete(true) => {
                    counters.jit_hit += 1;
                }
                JitInvariantResult::Complete(false) => {
                    counters.jit_hit += 1;
                    return Ok(Some(inv_name));
                }
                JitInvariantResult::Error(e) => {
                    counters.jit_error += 1;
                    return Err(e);
                }
                JitInvariantResult::FallbackNeeded | JitInvariantResult::PartialPass { .. } => {
                    counters.jit_fallback += 1;
                    unchecked.push(inv_name.as_str());
                }
                JitInvariantResult::NotCompiled => {
                    counters.jit_not_compiled += 1;
                    unchecked.push(inv_name.as_str());
                }
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_tir::bytecode::{BytecodeFunction, Opcode};

    fn make_simple_chunk() -> (BytecodeChunk, FxHashMap<String, u16>) {
        // Invariant: state[0] > 5
        let mut func = BytecodeFunction::new("Inv1".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 5 });
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv1".to_string(), 0);

        (chunk, op_indices)
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_build_and_check_passing() {
        let (chunk, op_indices) = make_simple_chunk();
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert_eq!(cache.len(), 1);

        // state[0] = 10 > 5, should pass
        let state = vec![10i64];
        let result = cache.check_invariant("Inv1", &state);
        assert_eq!(result, Some(Ok(true)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_check_violation() {
        let (chunk, op_indices) = make_simple_chunk();
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();

        // state[0] = 3 <= 5, should fail
        let state = vec![3i64];
        let result = cache.check_invariant("Inv1", &state);
        assert_eq!(result, Some(Ok(false)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_missing_invariant_returns_none() {
        let (chunk, op_indices) = make_simple_chunk();
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();

        let state = vec![10i64];
        let result = cache.check_invariant("NonExistent", &state);
        assert!(result.is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_check_all() {
        let (chunk, op_indices) = make_simple_chunk();
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();

        let invariants = vec!["Inv1".to_string(), "Inv2".to_string()];
        let state = vec![10i64];
        let mut unchecked = Vec::new();

        let result = cache
            .check_all(&invariants, &state, &mut unchecked)
            .unwrap();
        assert!(result.is_none()); // Inv1 passed
        assert_eq!(unchecked, vec!["Inv2"]); // Inv2 not in cache
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_check_all_continues_past_unchecked() {
        // With the non-bailing check_all, when Inv2 (not in cache) is
        // encountered, it goes to unchecked but Inv1 is still JIT-checked.
        // Since Inv1 is violated (3 <= 5), we get a violation result.
        let (chunk, op_indices) = make_simple_chunk();
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();

        let invariants = vec!["Inv2".to_string(), "Inv1".to_string()];
        let state = vec![3i64]; // Inv1: 3 <= 5, violation
        let mut unchecked = Vec::new();

        let result = cache
            .check_all(&invariants, &state, &mut unchecked)
            .unwrap();
        // Inv1 is detected as violated by JIT (even though Inv2 came first)
        assert_eq!(result, Some("Inv1"));
        // Inv2 was added to unchecked before the violation was detected
        assert_eq!(unchecked, vec!["Inv2"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_check_all_unchecked_only_when_passing() {
        // When all JIT-compilable invariants pass, unchecked only contains
        // the non-compiled ones (not the entire suffix).
        let (chunk, op_indices) = make_simple_chunk();
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();

        let invariants = vec!["Inv2".to_string(), "Inv1".to_string(), "Inv3".to_string()];
        let state = vec![10i64]; // Inv1: 10 > 5, passes
        let mut unchecked = Vec::new();

        let result = cache
            .check_all(&invariants, &state, &mut unchecked)
            .unwrap();
        assert!(result.is_none()); // No violations detected by JIT
                                   // Only Inv2 and Inv3 are unchecked (not in cache); Inv1 passed via JIT
        assert_eq!(unchecked, vec!["Inv2", "Inv3"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_check_all_violation() {
        let (chunk, op_indices) = make_simple_chunk();
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();

        let invariants = vec!["Inv1".to_string()];
        let state = vec![3i64]; // 3 <= 5, violation
        let mut unchecked = Vec::new();

        let result = cache
            .check_all(&invariants, &state, &mut unchecked)
            .unwrap();
        assert_eq!(result, Some("Inv1"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_ineligible_function_skipped() {
        // Function with StoreVar opcode (ineligible for invariant context —
        // only allowed in next-state compilation).
        let mut func = BytecodeFunction::new("BadInv".to_string(), 0);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("BadInv".to_string(), 0);

        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert!(cache.is_empty()); // Ineligible, not cached
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_build_rejects_out_of_range_operator_index() {
        let chunk = BytecodeChunk::new();
        let mut op_indices = FxHashMap::default();
        op_indices.insert("MissingInv".to_string(), 1);

        match JitInvariantCache::build(&chunk, &op_indices) {
            Err(JitError::CompileError(message)) => {
                assert!(message.contains("out of range"));
            }
            Err(other) => panic!("expected out-of-range compile error, got {other:?}"),
            Ok(_) => panic!("expected out-of-range operator index to fail"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_collect_loadvar_indices_simple() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 2 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 2, var_idx: 2 }); // duplicate
        func.emit(Opcode::Ret { rs: 0 });
        assert_eq!(collect_loadvar_indices(&func), vec![0, 2]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_required_vars_union_across_invariants() {
        // Inv1 reads var 0, Inv2 reads var 2 — required_vars should be [0, 2]
        let mut func1 = BytecodeFunction::new("Inv1".to_string(), 0);
        func1.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func1.emit(Opcode::LoadImm { rd: 1, value: 5 });
        func1.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func1.emit(Opcode::Ret { rs: 2 });

        let mut func2 = BytecodeFunction::new("Inv2".to_string(), 0);
        func2.emit(Opcode::LoadVar { rd: 0, var_idx: 2 });
        func2.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func2.emit(Opcode::GeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func2.emit(Opcode::Ret { rs: 2 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func1);
        chunk.functions.push(func2);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv1".to_string(), 0);
        op_indices.insert("Inv2".to_string(), 1);

        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.required_vars(), &[0, 2]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_remap_loadvar_indices() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 5 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 10 });
        func.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func.emit(Opcode::Ret { rs: 0 });

        let mut remap = FxHashMap::default();
        remap.insert(5, 0);
        remap.insert(10, 1);

        let remapped = remap_loadvar_indices(&func, &remap);
        assert_eq!(
            remapped.instructions[0],
            Opcode::LoadVar { rd: 0, var_idx: 0 }
        );
        assert_eq!(
            remapped.instructions[1],
            Opcode::LoadVar { rd: 1, var_idx: 1 }
        );
        // Non-LoadVar instructions are unchanged.
        assert_eq!(
            remapped.instructions[2],
            Opcode::LoadImm { rd: 2, value: 1 }
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compact_buffer_with_sparse_var_indices() {
        // Invariant reads var 5 only. With 10 state variables, the compact
        // buffer should have 1 slot (not 10). var_remap: {5 → 0}.
        let mut func = BytecodeFunction::new("Inv".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv".to_string(), 0);

        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.required_vars(), &[5]);
        assert_eq!(cache.compact_slot_count(), 1);
        assert_eq!(*cache.var_remap().get(&5).unwrap(), 0);

        // Compact state: only 1 slot for var 5's value.
        // Value 10 > 3 → should pass.
        let compact_state = vec![10i64];
        let result = cache.check_invariant("Inv", &compact_state);
        assert_eq!(result, Some(Ok(true)));

        // Value 2 <= 3 → should fail.
        let compact_state = vec![2i64];
        let result = cache.check_invariant("Inv", &compact_state);
        assert_eq!(result, Some(Ok(false)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compact_buffer_two_invariants_different_vars() {
        // Inv1 reads var 3, Inv2 reads var 7.
        // Compact buffer: [var3_val, var7_val] (2 slots).
        // var_remap: {3 → 0, 7 → 1}.
        let mut func1 = BytecodeFunction::new("Inv1".to_string(), 0);
        func1.emit(Opcode::LoadVar { rd: 0, var_idx: 3 });
        func1.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func1.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func1.emit(Opcode::Ret { rs: 2 });

        let mut func2 = BytecodeFunction::new("Inv2".to_string(), 0);
        func2.emit(Opcode::LoadVar { rd: 0, var_idx: 7 });
        func2.emit(Opcode::LoadImm { rd: 1, value: 100 });
        func2.emit(Opcode::LtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func2.emit(Opcode::Ret { rs: 2 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func1);
        chunk.functions.push(func2);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv1".to_string(), 0);
        op_indices.insert("Inv2".to_string(), 1);

        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.required_vars(), &[3, 7]);
        assert_eq!(cache.compact_slot_count(), 2);

        // Compact state: [var3=5, var7=50]
        // Inv1: 5 > 0 → true. Inv2: 50 < 100 → true.
        let compact_state = vec![5i64, 50i64];
        assert_eq!(
            cache.check_invariant("Inv1", &compact_state),
            Some(Ok(true))
        );
        assert_eq!(
            cache.check_invariant("Inv2", &compact_state),
            Some(Ok(true))
        );

        // Compact state: [var3=-1, var7=50]
        // Inv1: -1 > 0 → false (violation).
        let compact_state = vec![-1i64, 50i64];
        assert_eq!(
            cache.check_invariant("Inv1", &compact_state),
            Some(Ok(false))
        );

        // Compact state: [var3=5, var7=200]
        // Inv2: 200 < 100 → false (violation).
        let compact_state = vec![5i64, 200i64];
        assert_eq!(
            cache.check_invariant("Inv2", &compact_state),
            Some(Ok(false))
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_var_remap_identity_for_contiguous_vars() {
        // When vars are already 0, 1, 2 (contiguous from 0), the remap is identity.
        let (chunk, op_indices) = make_simple_chunk();
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();

        // make_simple_chunk uses var_idx: 0 only.
        assert_eq!(cache.required_vars(), &[0]);
        assert_eq!(*cache.var_remap().get(&0).unwrap(), 0);
    }

    // ================================================================
    // build_with_layout: native RecordGet via compound layout
    // ================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_with_layout_native_record_get() {
        use crate::compound_layout::*;

        // Invariant: state[0].a > 10
        // state[0] is a record [a |-> 42, b |-> TRUE]
        let name_a = tla_core::intern_name("a");
        let name_b = tla_core::intern_name("b");

        // Build bytecode: LoadVar r0 (record), RecordGet r1 r0 field 0, LoadImm r2 10, Gt r3 r1 r2, Ret r3
        let mut func = BytecodeFunction::new("Inv1".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: 0,
        });
        func.emit(Opcode::LoadImm { rd: 2, value: 10 });
        func.emit(Opcode::GtInt {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let mut chunk = BytecodeChunk::new();
        // field_idx 0 maps to name_a
        chunk.constants.add_field_id(name_a.0);
        chunk.constants.add_field_id(name_b.0);
        chunk.functions.push(func);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv1".to_string(), 0);

        // State layout: one record variable [a |-> Int, b |-> Bool]
        let state_layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (name_a, CompoundLayout::Int),
                (name_b, CompoundLayout::Bool),
            ],
        })]);

        let cache =
            JitInvariantCache::build_with_layout(&chunk, &op_indices, &state_layout).unwrap();
        assert_eq!(cache.len(), 1, "invariant should be JIT-compiled");

        // Serialized state: [TAG_RECORD, 2, name_a, TAG_INT, 42, name_b, TAG_BOOL, 1]
        let state = vec![
            TAG_RECORD,
            2,
            name_a.0 as i64,
            TAG_INT,
            42,
            name_b.0 as i64,
            TAG_BOOL,
            1,
        ];
        // 42 > 10 → true (JIT native path, no fallback)
        let result = cache.check_invariant("Inv1", &state);
        assert_eq!(
            result,
            Some(Ok(true)),
            "RecordGet should resolve natively: 42 > 10"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_with_layout_native_record_get_violation() {
        use crate::compound_layout::*;

        // Invariant: state[0].a > 10, but a = 5 → violation
        let name_a = tla_core::intern_name("a");
        let name_b = tla_core::intern_name("b");

        let mut func = BytecodeFunction::new("Inv1".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: 0,
        });
        func.emit(Opcode::LoadImm { rd: 2, value: 10 });
        func.emit(Opcode::GtInt {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let mut chunk = BytecodeChunk::new();
        chunk.constants.add_field_id(name_a.0);
        chunk.constants.add_field_id(name_b.0);
        chunk.functions.push(func);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv1".to_string(), 0);

        let state_layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (name_a, CompoundLayout::Int),
                (name_b, CompoundLayout::Bool),
            ],
        })]);

        let cache =
            JitInvariantCache::build_with_layout(&chunk, &op_indices, &state_layout).unwrap();

        // a = 5, b = TRUE
        let state = vec![
            TAG_RECORD,
            2,
            name_a.0 as i64,
            TAG_INT,
            5,
            name_b.0 as i64,
            TAG_BOOL,
            1,
        ];
        // 5 > 10 → false (violation, detected natively)
        let result = cache.check_invariant("Inv1", &state);
        assert_eq!(
            result,
            Some(Ok(false)),
            "RecordGet should resolve natively: 5 > 10 is false"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_with_layout_remap_preserves_record_access() {
        use crate::compound_layout::*;

        // Test that var remapping correctly remaps the layout too.
        // Invariant reads var 2 (not var 0), which is a record.
        let name_x = tla_core::intern_name("x");

        let mut func = BytecodeFunction::new("Inv".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 2 });
        func.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: 0,
        });
        func.emit(Opcode::LoadImm { rd: 2, value: 0 });
        func.emit(Opcode::GtInt {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let mut chunk = BytecodeChunk::new();
        chunk.constants.add_field_id(name_x.0);
        chunk.functions.push(func);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv".to_string(), 0);

        // State layout: var 0 = ScalarInt, var 1 = ScalarBool, var 2 = Record [x |-> Int]
        let state_layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::ScalarBool,
            VarLayout::Compound(CompoundLayout::Record {
                fields: vec![(name_x, CompoundLayout::Int)],
            }),
        ]);

        let cache =
            JitInvariantCache::build_with_layout(&chunk, &op_indices, &state_layout).unwrap();
        assert_eq!(cache.len(), 1);
        // Var 2 is remapped to compact index 0.
        assert_eq!(cache.required_vars(), &[2]);
        assert_eq!(*cache.var_remap().get(&2).unwrap(), 0);

        // Compact state buffer only contains var 2's data.
        // Record [x |-> 99]: [TAG_RECORD, 1, name_x, TAG_INT, 99]
        let compact_state = vec![TAG_RECORD, 1, name_x.0 as i64, TAG_INT, 99];
        // 99 > 0 → true
        let result = cache.check_invariant("Inv", &compact_state);
        assert_eq!(
            result,
            Some(Ok(true)),
            "RecordGet on remapped var should resolve natively: 99 > 0"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_with_layout_without_record_falls_back() {
        use crate::compound_layout::*;

        // When the invariant accesses a scalar variable (no compound layout),
        // build_with_layout should still work like build.
        let (chunk, op_indices) = make_simple_chunk();

        let state_layout = StateLayout::new(vec![VarLayout::ScalarInt]);

        let cache =
            JitInvariantCache::build_with_layout(&chunk, &op_indices, &state_layout).unwrap();
        assert_eq!(cache.len(), 1);

        // Scalar: state[0] = 10 > 5 → true
        let state = vec![10i64];
        assert_eq!(cache.check_invariant("Inv1", &state), Some(Ok(true)));
    }

    // ================================================================
    // Call inlining: invariants that call sub-operators
    // Part of #3948.
    // ================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_call_inlining_simple_callee() {
        // TypeOK (func 0): state[0] >= 0
        let mut type_ok = BytecodeFunction::new("TypeOK".to_string(), 0);
        type_ok.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        type_ok.emit(Opcode::LoadImm { rd: 1, value: 0 });
        type_ok.emit(Opcode::GeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        type_ok.emit(Opcode::Ret { rs: 2 });

        // Inv (func 1): Call TypeOK
        let mut inv = BytecodeFunction::new("Inv".to_string(), 0);
        inv.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(type_ok);
        chunk.functions.push(inv);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv".to_string(), 1);

        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert_eq!(
            cache.len(),
            1,
            "Inv should be JIT-compiled after inlining Call"
        );

        // state[0] = 5 >= 0 → true
        let state = vec![5i64];
        assert_eq!(
            cache.check_invariant("Inv", &state),
            Some(Ok(true)),
            "Inv(5) should pass: 5 >= 0"
        );

        // state[0] = -1 < 0 → false (violation)
        let state = vec![-1i64];
        assert_eq!(
            cache.check_invariant("Inv", &state),
            Some(Ok(false)),
            "Inv(-1) should fail: -1 < 0"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_call_inlining_conjunction() {
        // Simulates: Inv == TypeOK /\ Positive
        // TypeOK (func 0): state[0] >= 0
        let mut type_ok = BytecodeFunction::new("TypeOK".to_string(), 0);
        type_ok.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        type_ok.emit(Opcode::LoadImm { rd: 1, value: 0 });
        type_ok.emit(Opcode::GeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        type_ok.emit(Opcode::Ret { rs: 2 });

        // Positive (func 1): state[0] > 0
        let mut positive = BytecodeFunction::new("Positive".to_string(), 0);
        positive.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        positive.emit(Opcode::LoadImm { rd: 1, value: 0 });
        positive.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        positive.emit(Opcode::Ret { rs: 2 });

        // Inv (func 2): Call TypeOK, Call Positive, And, Ret
        let mut inv = BytecodeFunction::new("Inv".to_string(), 0);
        inv.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::Call {
            rd: 1,
            op_idx: 1,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::And {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inv.emit(Opcode::Ret { rs: 2 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(type_ok);
        chunk.functions.push(positive);
        chunk.functions.push(inv);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv".to_string(), 2);

        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert_eq!(
            cache.len(),
            1,
            "Inv should be JIT-compiled after inlining both Calls"
        );

        // state[0] = 5: TypeOK(5)=true, Positive(5)=true → true
        let state = vec![5i64];
        assert_eq!(cache.check_invariant("Inv", &state), Some(Ok(true)));

        // state[0] = 0: TypeOK(0)=true, Positive(0)=false → false
        let state = vec![0i64];
        assert_eq!(cache.check_invariant("Inv", &state), Some(Ok(false)));

        // state[0] = -1: TypeOK(-1)=false, Positive(-1)=false → false
        let state = vec![-1i64];
        assert_eq!(cache.check_invariant("Inv", &state), Some(Ok(false)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_call_inlining_callee_reads_different_var() {
        // TypeOK (func 0): state[0] >= 0
        let mut type_ok = BytecodeFunction::new("TypeOK".to_string(), 0);
        type_ok.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        type_ok.emit(Opcode::LoadImm { rd: 1, value: 0 });
        type_ok.emit(Opcode::GeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        type_ok.emit(Opcode::Ret { rs: 2 });

        // CheckX (func 1): state[2] > 10
        let mut check_x = BytecodeFunction::new("CheckX".to_string(), 0);
        check_x.emit(Opcode::LoadVar { rd: 0, var_idx: 2 });
        check_x.emit(Opcode::LoadImm { rd: 1, value: 10 });
        check_x.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        check_x.emit(Opcode::Ret { rs: 2 });

        // Inv (func 2): Call TypeOK /\ Call CheckX
        let mut inv = BytecodeFunction::new("Inv".to_string(), 0);
        inv.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::Call {
            rd: 1,
            op_idx: 1,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::And {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inv.emit(Opcode::Ret { rs: 2 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(type_ok);
        chunk.functions.push(check_x);
        chunk.functions.push(inv);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv".to_string(), 2);

        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert_eq!(cache.len(), 1, "Inv should be JIT-compiled");

        // required_vars should include both var 0 and var 2
        assert!(
            cache.required_vars().contains(&0) && cache.required_vars().contains(&2),
            "required_vars should include vars from both callees, got {:?}",
            cache.required_vars()
        );

        // compact_slot_count should be 2 (var 0 and var 2)
        assert_eq!(cache.compact_slot_count(), 2);

        // Compact state: [var0=5, var2=20]
        // TypeOK: 5 >= 0 → true, CheckX: 20 > 10 → true
        let state = vec![5i64, 20i64];
        assert_eq!(cache.check_invariant("Inv", &state), Some(Ok(true)));

        // Compact state: [var0=5, var2=5]
        // TypeOK: 5 >= 0 → true, CheckX: 5 > 10 → false
        let state = vec![5i64, 5i64];
        assert_eq!(cache.check_invariant("Inv", &state), Some(Ok(false)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_call_inlining_nested_calls() {
        // Inner (func 0): state[0] > 0
        let mut inner = BytecodeFunction::new("Inner".to_string(), 0);
        inner.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inner.emit(Opcode::LoadImm { rd: 1, value: 0 });
        inner.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inner.emit(Opcode::Ret { rs: 2 });

        // Middle (func 1): Call Inner (nested call)
        let mut middle = BytecodeFunction::new("Middle".to_string(), 0);
        middle.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 0,
            argc: 0,
        });
        middle.emit(Opcode::Ret { rs: 0 });

        // Inv (func 2): Call Middle (double-nested call)
        let mut inv = BytecodeFunction::new("Inv".to_string(), 0);
        inv.emit(Opcode::Call {
            rd: 0,
            op_idx: 1,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(inner);
        chunk.functions.push(middle);
        chunk.functions.push(inv);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv".to_string(), 2);

        // max_depth=4 in build_callee_map should handle 2 levels of nesting
        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();
        assert_eq!(
            cache.len(),
            1,
            "Inv should be JIT-compiled after resolving nested Call chain"
        );

        // state[0] = 1 > 0 → true
        let state = vec![1i64];
        assert_eq!(cache.check_invariant("Inv", &state), Some(Ok(true)));

        // state[0] = -1 < 0 → false
        let state = vec![-1i64];
        assert_eq!(cache.check_invariant("Inv", &state), Some(Ok(false)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_call_inlining_with_build_with_layout() {
        use crate::compound_layout::*;

        // TypeOK (func 0): state[0].x >= 0
        let name_x = tla_core::intern_name("call_inl_x");

        let mut type_ok = BytecodeFunction::new("TypeOK".to_string(), 0);
        type_ok.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        type_ok.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: 0,
        });
        type_ok.emit(Opcode::LoadImm { rd: 2, value: 0 });
        type_ok.emit(Opcode::GeInt {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        type_ok.emit(Opcode::Ret { rs: 3 });

        // Inv (func 1): Call TypeOK
        let mut inv = BytecodeFunction::new("Inv".to_string(), 0);
        inv.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.constants.add_field_id(name_x.0);
        chunk.functions.push(type_ok);
        chunk.functions.push(inv);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv".to_string(), 1);

        let state_layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![(name_x, CompoundLayout::Int)],
        })]);

        let cache =
            JitInvariantCache::build_with_layout(&chunk, &op_indices, &state_layout).unwrap();
        assert_eq!(
            cache.len(),
            1,
            "Inv with Call + RecordGet should be JIT-compiled after inlining"
        );

        // Record [x |-> 42]: state[0].x = 42 >= 0 → true
        let state = vec![TAG_RECORD, 1, name_x.0 as i64, TAG_INT, 42];
        assert_eq!(
            cache.check_invariant("Inv", &state),
            Some(Ok(true)),
            "Inlined TypeOK: 42 >= 0 should pass"
        );

        // Record [x |-> -5]: state[0].x = -5 < 0 → false
        let state = vec![TAG_RECORD, 1, name_x.0 as i64, TAG_INT, -5];
        assert_eq!(
            cache.check_invariant("Inv", &state),
            Some(Ok(false)),
            "Inlined TypeOK: -5 < 0 should fail"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_call_inlining_dispatch_counters() {
        // Verify that after inlining, the invariant gets a jit_hit (not jit_fallback)
        let mut type_ok = BytecodeFunction::new("TypeOK".to_string(), 0);
        type_ok.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        type_ok.emit(Opcode::LoadImm { rd: 1, value: 0 });
        type_ok.emit(Opcode::GeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        type_ok.emit(Opcode::Ret { rs: 2 });

        let mut inv = BytecodeFunction::new("Inv".to_string(), 0);
        inv.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(type_ok);
        chunk.functions.push(inv);

        let mut op_indices = FxHashMap::default();
        op_indices.insert("Inv".to_string(), 1);

        let cache = JitInvariantCache::build(&chunk, &op_indices).unwrap();

        // Check with counters
        let invariants = vec!["Inv".to_string()];
        let state = vec![5i64];
        let mut unchecked = Vec::new();
        let mut counters = JitDispatchCounters::default();

        let result = cache
            .check_all_with_counters(&invariants, &state, &mut unchecked, &mut counters)
            .unwrap();
        assert!(result.is_none(), "should pass");
        assert_eq!(counters.jit_hit, 1, "should be a JIT hit (not fallback)");
        assert_eq!(counters.jit_fallback, 0, "should not fall back");
        assert_eq!(counters.total, 1);
        assert!(unchecked.is_empty(), "nothing should be unchecked");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_remap_state_layout() {
        use crate::compound_layout::*;

        let name_a = tla_core::intern_name("remap_a");
        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,  // var 0
            VarLayout::ScalarBool, // var 1
            VarLayout::Compound(CompoundLayout::Record {
                fields: vec![(name_a, CompoundLayout::Int)],
            }), // var 2
            VarLayout::ScalarInt,  // var 3
        ]);

        // required_vars = [1, 3] → compact layout should be [ScalarBool, ScalarInt]
        let compact = remap_state_layout(&layout, &[1, 3]);
        assert_eq!(compact.var_count(), 2);
        assert_eq!(compact.var_layout(0), Some(&VarLayout::ScalarBool));
        assert_eq!(compact.var_layout(1), Some(&VarLayout::ScalarInt));

        // required_vars = [2] → compact layout should be [Record{...}]
        let compact = remap_state_layout(&layout, &[2]);
        assert_eq!(compact.var_count(), 1);
        match compact.var_layout(0) {
            Some(VarLayout::Compound(CompoundLayout::Record { fields })) => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0, name_a);
            }
            other => panic!("expected Compound(Record), got {other:?}"),
        }
    }
}
