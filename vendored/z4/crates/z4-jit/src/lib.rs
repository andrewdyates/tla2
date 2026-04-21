// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Andrew Yates
//! # z4-jit: Native JIT compilation for SAT clause propagation
//!
//! Compiles static (irredundant) SAT clauses into per-variable native
//! propagation functions. Instead of the interpreted 2-watched-literal BCP
//! loop, each variable gets a pair of compiled functions:
//!
//! - `propagate_pos(ctx)` — called when x_i becomes TRUE
//! - `propagate_neg(ctx)` — called when x_i becomes FALSE
//!
//! Based on the FC-SAT paper: Formula-Compiled SAT via JIT compilation of BCP.
//!
//! ## Architecture
//!
//! Uses a custom lightweight assembler (~400 lines) instead of Cranelift
//! (~35 dependency crates). The generated code consists of only ~15 aarch64
//! instruction types: load/store, compare, branch, add, shift, select.
//! This eliminates Cranelift's compilation overhead (IR construction, register
//! allocation, instruction selection) and reduces compilation time by ~50-100x.
//!
//! ## Literal encoding
//!
//! `encoded_lit = var * 2 + polarity` where polarity 0 = positive, 1 = negative.

pub mod context;
pub mod guards;
#[cfg(target_arch = "aarch64")]
#[allow(unreachable_pub)]
pub(crate) mod aarch64;
#[cfg(target_arch = "x86_64")]
#[allow(unreachable_pub)]
pub(crate) mod x86_64;
pub(crate) mod emit;
pub(crate) mod executable;

#[cfg(test)]
mod tests;

pub use context::PropagationContext;
pub use guards::ClauseGuards;

use executable::ExecutableMemory;

/// Error type for JIT compilation failures.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum JitError {
    #[error("No native ISA available for this platform")]
    NoNativeIsa,

    #[error("Empty clause (clause_id={0}) cannot be compiled")]
    EmptyClause(u32),

    #[error("Unit clause (clause_id={0}) should be propagated at preprocessing")]
    UnitClause(u32),

    #[error("mmap failed: could not allocate executable memory")]
    MmapFailed,
}

/// Metadata for a compiled clause, used by conflict analysis to retrieve
/// the original literals.
#[derive(Debug, Clone)]
pub struct ClauseMetadata {
    /// The encoded literals in this clause.
    pub literals: Vec<u32>,
}

/// Type alias for compiled propagation functions.
/// Signature: `fn(*mut PropagationContext) -> i32`
/// Returns 0 for no conflict, or nonzero for conflict (clause_id in ctx.conflict).
type PropFn = unsafe extern "C" fn(*mut PropagationContext) -> i32;

/// A formula compiled into native per-variable propagation functions.
pub struct CompiledFormula {
    /// Per-variable propagation functions.
    /// Index: `variable_index * 2 + polarity` where polarity 0=pos, 1=neg.
    /// `None` means no clauses watch this literal (no-op propagation).
    functions: Vec<Option<PropFn>>,

    /// Clause metadata indexed by clause_id, for conflict analysis.
    clause_metadata: Vec<ClauseMetadata>,

    /// Number of variables in the compiled formula.
    num_vars: usize,

    /// Whether the code size budget was exhausted during compilation.
    budget_exhausted: bool,

    /// Estimated total compiled code size in bytes.
    estimated_code_bytes: usize,

    /// The executable memory must stay alive while functions are callable.
    _executable: ExecutableMemory,
}

impl CompiledFormula {
    /// Number of variables.
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Get clause metadata by clause_id.
    pub fn clause(&self, clause_id: u32) -> Option<&ClauseMetadata> {
        self.clause_metadata.get(clause_id as usize)
    }

    /// Number of compiled clauses.
    pub fn num_clauses(&self) -> usize {
        self.clause_metadata.len()
    }

    /// Check whether a given variable+polarity has a compiled function.
    pub fn has_function(&self, var: usize, polarity: usize) -> bool {
        let idx = var * 2 + polarity;
        self.functions.get(idx).is_some_and(|f| f.is_some())
    }

    /// Whether the code size budget was exhausted during compilation.
    pub fn budget_exhausted(&self) -> bool {
        self.budget_exhausted
    }

    /// Estimated total compiled code size in bytes.
    pub fn estimated_code_bytes(&self) -> usize {
        self.estimated_code_bytes
    }
}

/// Compile a CNF formula into native per-variable propagation functions.
///
/// # Arguments
///
/// * `num_vars` — Number of variables (variables are 0-indexed: 0..num_vars)
/// * `clauses` — Slice of `(clause_id, literals)`. Clause IDs must be
///   sequential starting from 0. Literals use the encoding `var * 2 + pol`.
///
/// # Errors
///
/// Returns `JitError` if compilation fails (ISA unavailable, invalid clauses).
pub fn compile(
    num_vars: usize,
    clauses: &[(u32, &[u32])],
) -> Result<CompiledFormula, JitError> {
    // Validate clauses.
    let mut clause_metadata = Vec::with_capacity(clauses.len());
    let num_lits = num_vars * 2;

    // Build: for each literal L, which clauses contain L, and what are the
    // other literals in that clause?
    let mut lit_to_clauses: Vec<Vec<(u32, Vec<u32>)>> = vec![Vec::new(); num_lits];

    for &(clause_id, lits) in clauses {
        if lits.is_empty() {
            return Err(JitError::EmptyClause(clause_id));
        }
        if lits.len() == 1 {
            return Err(JitError::UnitClause(clause_id));
        }

        clause_metadata.push(ClauseMetadata {
            literals: lits.to_vec(),
        });

        for &lit in lits {
            let mut other_lits: Vec<u32> = lits.iter().copied().filter(|&l| l != lit).collect();
            // Sort by variable index so lowest-indexed variable is checked first
            // (early-exit optimization: low-index vars tend to be assigned earlier).
            other_lits.sort_unstable_by_key(|&l| l >> 1);
            if (lit as usize) < num_lits {
                lit_to_clauses[lit as usize].push((clause_id, other_lits));
            }
        }
    }

    // Code size budget: 256KB fits in L2 I-cache.
    const CODE_BUDGET_BYTES: usize = 256 * 1024;
    // Per-function code size cap: skip variables whose clause set would
    // generate >4KB of code, to avoid I-cache pressure from a single
    // hot function evicting code for many other variables.
    const MAX_FUNCTION_BYTES: usize = 4 * 1024;
    let mut estimated_code_bytes: usize = 0;
    let mut budget_exhausted = false;

    // Compile all functions into a single contiguous code buffer.
    let mut combined_code: Vec<u8> = Vec::new();
    let mut func_offsets: Vec<Option<usize>> = vec![None; num_lits];

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        let _ = (&lit_to_clauses, &mut combined_code, &mut func_offsets, &mut estimated_code_bytes, &mut budget_exhausted);
        return Err(JitError::NoNativeIsa);
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        // Priority-ordered compilation: compile high-value (var, pol) pairs first
        // so that the 256KB code budget is spent on functions that will reduce
        // the most BCP cache misses. Score weights: ternary 4x, binary 3x,
        // 4-5 lit 1x, longer 0x.
        let mut compile_order: Vec<(usize, usize, u32)> = Vec::new();
        for var in 0..num_vars {
            for pol in 0..2u32 {
                let false_lit = if pol == 0 {
                    var as u32 * 2 + 1
                } else {
                    var as u32 * 2
                };

                let clause_list = &lit_to_clauses[false_lit as usize];
                if clause_list.is_empty() {
                    continue;
                }

                let score: usize = clause_list
                    .iter()
                    .map(|(_, lits)| match lits.len() {
                        2 => 4,       // ternary clause (highest BCP benefit)
                        1 => 3,       // binary clause
                        3 | 4 => 2,   // 4-5 literal clause
                        5..=11 => 1,  // 6-12 literal clause (lower priority)
                        _ => 0,       // >12 literals (not compiled)
                    })
                    .sum();

                compile_order.push((score, var, pol));
            }
        }

        // Sort descending by score; tie-break by var then pol for determinism.
        compile_order.sort_unstable_by(|a, b| {
            b.0.cmp(&a.0)
                .then_with(|| a.1.cmp(&b.1))
                .then_with(|| a.2.cmp(&b.2))
        });

        for &(_, var, pol) in &compile_order {
            let false_lit = if pol == 0 {
                var as u32 * 2 + 1
            } else {
                var as u32 * 2
            };

            let clause_list = &lit_to_clauses[false_lit as usize];

            // Estimate code size for budget check.
            // x86_64 instructions are larger on average (~5-7 bytes vs
            // aarch64's fixed 4 bytes), so estimates are conservative.
            let func_estimate: usize = 64 // prologue + epilogue + ctx loads
                + clause_list
                    .iter()
                    .map(|(_, lits)| match lits.len() {
                        1 => 80,   // binary: ~20 instructions
                        2 => 160,  // ternary: ~40 instructions
                        n => 32 * n + 80, // general: ~8 per lit + overhead
                    })
                    .sum::<usize>();

            // Per-function I-cache pressure cap: skip variables with
            // too many clause occurrences. A single 4KB+ function would
            // dominate the I-cache working set and evict many other
            // per-variable functions.
            if func_estimate > MAX_FUNCTION_BYTES {
                budget_exhausted = true;
                continue;
            }

            if estimated_code_bytes + func_estimate > CODE_BUDGET_BYTES {
                budget_exhausted = true;
                continue;
            }
            estimated_code_bytes += func_estimate;

            // Build clause slice for emit.
            let clause_refs: Vec<(u32, &[u32])> = clause_list
                .iter()
                .map(|(cid, lits)| (*cid, lits.as_slice()))
                .collect();

            // Align function start to 16 bytes for I-cache line alignment.
            while combined_code.len() % 16 != 0 {
                combined_code.push(0);
            }

            let func_offset = combined_code.len();
            let func_code = emit::emit_propagation_function(&clause_refs);
            combined_code.extend_from_slice(&func_code);

            let idx = var * 2 + pol as usize;
            func_offsets[idx] = Some(func_offset);
        }
    }

    // Allocate executable memory and copy all function code.
    let executable = ExecutableMemory::new(&combined_code)?;
    let base_ptr = executable.as_ptr();

    // Resolve function pointers from base + offset.
    let mut functions: Vec<Option<PropFn>> = vec![None; num_lits];
    for (idx, offset) in func_offsets.iter().enumerate() {
        if let Some(off) = offset {
            // SAFETY (pointer arithmetic): base_ptr is the start of the mmap'd
            // executable region. *off is a byte offset within combined_code
            // (which was copied into that region). The sum base_ptr + *off is
            // within the allocation because *off < combined_code.len() <=
            // alloc_len (the mmap size). Function starts are 16-byte aligned
            // within combined_code, satisfying any ABI alignment requirements.
            let fn_ptr = unsafe { base_ptr.add(*off) };
            // SAFETY (transmute): The bytes at fn_ptr are valid machine code
            // generated by our assembler with the signature:
            //   extern "C" fn(*mut PropagationContext) -> i32
            // The function uses the platform ABI (aarch64 AAPCS or System V
            // AMD64) and is 16-byte aligned. The ExecutableMemory backing this
            // code is owned by CompiledFormula._executable and remains alive
            // for the lifetime of the CompiledFormula, so the function pointer
            // remains valid for as long as the CompiledFormula exists.
            functions[idx] = Some(unsafe {
                std::mem::transmute::<*const u8, PropFn>(fn_ptr)
            });
        }
    }

    Ok(CompiledFormula {
        functions,
        clause_metadata,
        num_vars,
        budget_exhausted,
        estimated_code_bytes,
        _executable: executable,
    })
}

/// Call the compiled propagation function for a literal assignment.
///
/// When variable `var` is assigned, call with `polarity` 0 for true, 1 for false.
///
/// Returns `true` if a conflict was detected (check `ctx.conflict` for the
/// clause ID).
///
/// # Safety
///
/// The caller must ensure:
/// - `ctx` fields (`vals`, `trail`, `trail_len`, etc.) point to valid,
///   sufficiently-sized arrays
/// - Variable indices in the compiled formula are within bounds of those arrays
/// - No other thread is concurrently modifying the arrays
pub unsafe fn propagate(
    formula: &CompiledFormula,
    var: usize,
    polarity: usize,
    ctx: &mut PropagationContext,
) -> bool {
    debug_assert!(var < formula.num_vars, "variable out of range");
    debug_assert!(polarity < 2, "polarity must be 0 or 1");

    let idx = var * 2 + polarity;
    if let Some(func) = formula.functions.get(idx).copied().flatten() {
        // SAFETY: The function pointer `func` is valid native code residing in
        // the mmap'd ExecutableMemory owned by formula._executable (alive for
        // the lifetime of `formula`). The caller guarantees:
        //   1. ctx.vals points to a valid i8 array of size >= num_vars * 2
        //   2. ctx.trail points to a valid u32 array with room for new entries
        //   3. ctx.trail_len points to a valid u32 counter
        //   4. ctx.conflict points to a valid u32 for conflict clause ID
        //   5. ctx.reasons points to a valid u32 array of size >= num_vars
        //   6. ctx.guards points to a valid u8 array covering all clause IDs
        //      (or is null if guards are disabled)
        //   7. No concurrent modification of the pointed-to arrays
        // The compiled function accesses these arrays at indices derived from
        // the compile-time literal encodings, which are bounded by num_vars * 2.
        let result = unsafe { func(ctx as *mut PropagationContext) };
        result != 0
    } else {
        false
    }
}
