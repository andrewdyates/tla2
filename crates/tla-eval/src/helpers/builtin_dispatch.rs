// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Builtin operator dispatch, arity checking, placeholder detection,
//! and permutation function generation.
//!
//! Extracted from `helpers/mod.rs` as part of #1669.

use super::super::{
    apply_builtin_binary_op, eval, eval_builtin_apalache, eval_builtin_bags, eval_builtin_bagsext,
    eval_builtin_finite_sets, eval_builtin_fold, eval_builtin_functions,
    eval_builtin_functions_ext, eval_builtin_graphs, eval_builtin_io, eval_builtin_misc,
    eval_builtin_relation, eval_builtin_sequences, eval_builtin_sequences_ext,
    eval_builtin_sequences_ext_ops, eval_builtin_stdlib_ext, eval_builtin_svg, eval_builtin_tlc,
    eval_builtin_tlcext, eval_builtin_variants, eval_builtin_vector_clocks, EvalCtx, EvalError,
    EvalResult,
};
use crate::value::{boolean_set, FuncValue, Value};
use std::sync::Arc;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::{FileId, Span, Spanned};

/// Builtins from Json/IOUtils/Community modules where the TLA module body is often
/// only a placeholder (e.g., `CHOOSE v : TRUE` / `TRUE`) and TLC uses a Java override.
///
/// These operators should prefer the builtin evaluator when such a placeholder
/// definition is present in the loaded operator environment.
pub(super) fn builtin_placeholder_arity(name: &str) -> Option<usize> {
    match name {
        // Randomization
        "RandomSubset" => Some(2),
        "RandomSetOfSubsets" => Some(3),
        "RandomSubsetSet" => Some(3),

        // CSV
        "CSVWrite" => Some(3),
        "CSVRead" => Some(3),
        "CSVRecords" => Some(1),

        // Json
        "ToJson" => Some(1),
        "ToJsonArray" => Some(1),
        "ToJsonObject" => Some(1),
        "JsonSerialize" => Some(2),
        "JsonDeserialize" => Some(1),
        "ndJsonSerialize" => Some(2),
        "ndJsonDeserialize" => Some(1),

        // IOUtils
        "IOExec" => Some(1),
        "IOEnvExec" => Some(2),
        "IOExecTemplate" => Some(2),
        "IOEnvExecTemplate" => Some(3),
        "IOEnv" => Some(0),
        "IOEnvGet" => Some(1),
        "IOEnvPut" => Some(2),
        "IOSerialize" => Some(3),
        "Serialize" => Some(3),
        "IODeserialize" => Some(2),
        "Deserialize" => Some(2),
        "atoi" => Some(1),
        "zeroPadN" => Some(2),

        // VectorClocks
        "IsCausalOrder" => Some(2),
        "CausalOrder" => Some(4),

        // Statistics
        "ChiSquare" => Some(3),
        _ => None,
    }
}

pub(super) fn is_placeholder_override_body(expr: &Spanned<Expr>) -> bool {
    match &expr.node {
        Expr::Bool(true) => true,
        Expr::Choose(_, pred) => matches!(pred.node, Expr::Bool(true)),
        _ => false,
    }
}

/// Operators with complete Rust builtin implementations that should take
/// priority over TLA+ definitions loaded from disk, but ONLY when the
/// source module is actually imported. This handles community modules
/// like DyadicRationals where the .tla file has real (non-placeholder)
/// definitions, but TLC uses Java overrides for performance.
/// The module check prevents hijacking user-defined operators that happen
/// to share names (e.g., a user-defined `Add(a, b) == a + b`).
fn has_module_scoped_complete_builtin_override(
    name: &str,
    arg_count: usize,
    ctx: &EvalCtx,
) -> bool {
    // DyadicRationals operators — only override when the module is loaded
    if ctx.shared.extended_module_names.contains("DyadicRationals")
        && matches!(
            (name, arg_count),
            ("Zero", 0)
                | ("One", 0)
                | ("IsDyadicRational", 1)
                | ("Add", 2)
                | ("Half", 1)
                | ("PrettyPrint", 1)
        )
    {
        return true;
    }
    // Fold operators from Functions — the community Functions.tla defines
    // FoldFunction/FoldFunctionOnSet via LOCAL INSTANCE Folds using
    // MapThenFoldSet, but TLA2 has complete Rust builtin implementations.
    // Without this override, specs with a local Functions.tla (e.g., ewd998)
    // fail with "Undefined operator: MapThenFoldSet".
    if ctx.shared.extended_module_names.contains("Functions")
        && matches!(
            (name, arg_count),
            ("FoldFunction", 3) | ("FoldFunctionOnSet", 4)
        )
    {
        return true;
    }
    // FoldSet — only override when FiniteSetsExt is loaded (TLC: @TLAPlusOperator(module="FiniteSetsExt"))
    if ctx.shared.extended_module_names.contains("FiniteSetsExt")
        && matches!((name, arg_count), ("FoldSet", 3))
    {
        return true;
    }
    // SequencesExt fold operators — only override when SequencesExt is loaded
    // (TLC: @TLAPlusOperator(module="SequencesExt") for each)
    if ctx.shared.extended_module_names.contains("SequencesExt")
        && matches!(
            (name, arg_count),
            ("FoldSeq", 3)
                | ("FoldLeft", 3)
                | ("FoldRight", 3)
                | ("FoldLeftDomain", 3)
                | ("FoldRightDomain", 3)
        )
    {
        return true;
    }
    // Apalache module operators — only override when Apalache is loaded.
    // ApaFoldSet/ApaFoldSeqLeft have recursive TLA+ bodies; native builtins
    // are O(n) iterative. Gen/Guess have placeholder bodies. MkSeq/Repeat/
    // SetAsFun have real TLA+ bodies but benefit from native implementation.
    // Skolem/Expand/ConstCardinality are identity annotations.
    if ctx.shared.extended_module_names.contains("Apalache")
        && matches!(
            (name, arg_count),
            ("Gen", 1)
                | ("Guess", 1)
                | ("ApaFoldSet", 3)
                | ("ApaFoldSeqLeft", 3)
                | ("MkSeq", 2)
                | ("Repeat", 3)
                | ("SetAsFun", 1)
                | ("Skolem", 1)
                | ("Expand", 1)
                | ("ConstCardinality", 1)
        )
    {
        return true;
    }
    // Variants module operators — only override when Variants is loaded.
    if ctx.shared.extended_module_names.contains("Variants")
        && matches!(
            (name, arg_count),
            ("Variant", 2)
                | ("VariantTag", 1)
                | ("VariantGetUnsafe", 2)
                | ("VariantGetOrElse", 3)
                | ("VariantFilter", 2)
        )
    {
        return true;
    }
    false
}

fn has_unconditional_complete_builtin_override(name: &str, arg_count: usize) -> bool {
    // Part of #3075: ReduceSet(op(_, _), S, base) — unconditional override.
    // Many specs (e.g., Util.tla in MCKVsnap) define ReduceSet inline using a
    // recursive function over SUBSET set — O(2^n). The builtin uses O(n) iteration.
    // The signature is distinctive (arity 3, higher-order first param) and
    // universally standardized across the TLA+ community.
    if matches!((name, arg_count), ("ReduceSet", 3)) {
        return true;
    }
    // Part of #3075: SetToSeq(S) — unconditional override.
    // KVsnap.tla defines SetToSeq as CHOOSE f \in [1..n -> S] : IsInjective(f)
    // which is O(n^n) — enumerates ALL functions to find an injective one.
    // The builtin iterates S in TLC-normalized order in O(n).
    if matches!((name, arg_count), ("SetToSeq", 1)) {
        return true;
    }
    false
}

pub fn has_complete_builtin_override(name: &str, arg_count: usize, ctx: &EvalCtx) -> bool {
    has_module_scoped_complete_builtin_override(name, arg_count, ctx)
        || has_unconditional_complete_builtin_override(name, arg_count)
}

pub(crate) fn should_prefer_builtin_override(
    name: &str,
    def: &OperatorDef,
    arg_count: usize,
    ctx: &EvalCtx,
) -> bool {
    // Module-scoped builtin overrides must not hijack same-named operators
    // defined in the main module. The main spec is always lowered as FileId(0).
    let main_module_shadow = def.name.span.file == FileId(0)
        && has_module_scoped_complete_builtin_override(name, arg_count, ctx);
    if !main_module_shadow && has_complete_builtin_override(name, arg_count, ctx) {
        return true;
    }

    matches!(builtin_placeholder_arity(name), Some(arity) if arity == arg_count)
        && is_placeholder_override_body(&def.body)
}

/// Evaluate built-in operators from the standard library
pub(crate) fn eval_builtin(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    // Core operators that are too small to justify a separate file
    match name {
        // === Built-in operator symbols (callable via Apply / operator replacement) ===
        "+" | "-" | "*" | "/" | "%" | "^" | "\\div" | "\\cup" | "\\cap" | "\\" => {
            check_arity(name, args, 2, span)?;
            let left = eval(ctx, &args[0])?;
            let right = eval(ctx, &args[1])?;
            return Ok(Some(apply_builtin_binary_op(name, left, right, span)?));
        }

        // Apalache assignment operator: x' := e is equivalent to x' = e in BFS mode.
        // Part of #3760: Apalache uses := as an annotation for variable assignments.
        // In explicit-state model checking, this is just equality.
        ":=" => {
            check_arity(name, args, 2, span)?;
            let left = eval(ctx, &args[0])?;
            let right = eval(ctx, &args[1])?;
            let eq = super::set_semantics::values_equal(ctx, &left, &right, span)?;
            return Ok(Some(Value::Bool(eq)));
        }

        // === Naturals/Integers/Reals ===
        "Nat" => return Ok(Some(Value::try_model_value("Nat")?)),
        "Int" => return Ok(Some(Value::try_model_value("Int")?)),
        "Real" => return Ok(Some(Value::try_model_value("Real")?)),
        "Infinity" => return Ok(Some(Value::try_model_value("Infinity")?)),
        "BOOLEAN" => return Ok(Some(boolean_set())),
        _ => {}
    }

    // Dispatch to domain-specific builtin evaluators.
    // Each returns Ok(Some(v)) if it handled the name, Ok(None) if not.
    macro_rules! try_domain {
        ($func:ident) => {
            if let Some(v) = $func(ctx, name, args, span)? {
                return Ok(Some(v));
            }
        };
    }

    try_domain!(eval_builtin_sequences);
    try_domain!(eval_builtin_sequences_ext);
    try_domain!(eval_builtin_sequences_ext_ops);
    try_domain!(eval_builtin_finite_sets);
    try_domain!(eval_builtin_stdlib_ext);
    try_domain!(eval_builtin_tlc);
    try_domain!(eval_builtin_tlcext);
    try_domain!(eval_builtin_functions);
    try_domain!(eval_builtin_functions_ext);
    try_domain!(eval_builtin_fold);
    try_domain!(eval_builtin_bags);
    try_domain!(eval_builtin_bagsext);
    try_domain!(eval_builtin_graphs);
    try_domain!(eval_builtin_relation);
    try_domain!(eval_builtin_io);
    try_domain!(eval_builtin_vector_clocks);
    try_domain!(eval_builtin_misc);
    try_domain!(eval_builtin_svg);
    try_domain!(eval_builtin_apalache);
    try_domain!(eval_builtin_variants);

    // Not a built-in
    Ok(None)
}

pub(crate) fn check_arity(
    name: &str,
    args: &[Spanned<Expr>],
    expected: usize,
    span: Option<Span>,
) -> EvalResult<()> {
    if args.len() != expected {
        Err(EvalError::ArityMismatch {
            op: name.into(),
            expected,
            got: args.len(),
            span,
        })
    } else {
        Ok(())
    }
}

/// Generate all permutation functions on a set (used by TLC!Permutations for symmetry)
/// Each permutation is a bijective function [S -> S]
pub(crate) fn generate_permutation_functions(
    domain: &[Value],       // Original domain elements (sorted order)
    range_prefix: &[usize], // Current permutation indices being built
    result: &mut Vec<Value>,
) {
    let n = domain.len();

    if range_prefix.len() == n {
        // Complete permutation: build the function from sorted entries
        // domain is sorted, so entries will be in sorted order
        let entries: Vec<(Value, Value)> = range_prefix
            .iter()
            .enumerate()
            .map(|(i, &j)| (domain[i].clone(), domain[j].clone()))
            .collect();
        result.push(Value::Func(Arc::new(FuncValue::from_sorted_entries(
            entries,
        ))));
        return;
    }

    // Try each unused index for the next position
    for j in 0..n {
        if !range_prefix.contains(&j) {
            let mut new_prefix = range_prefix.to_vec();
            new_prefix.push(j);
            generate_permutation_functions(domain, &new_prefix, result);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn ctx_with_modules(modules: &[&str]) -> EvalCtx {
        let mut ctx = EvalCtx::new();
        let shared = Arc::make_mut(&mut ctx.stable_mut().shared);
        for m in modules {
            shared.extended_module_names.insert(m.to_string());
        }
        ctx
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn dyadic_rationals_override_requires_module() {
        let ctx_none = EvalCtx::new();
        assert!(!has_complete_builtin_override("Add", 2, &ctx_none));
        assert!(!has_complete_builtin_override("Half", 1, &ctx_none));
        let ctx_dr = ctx_with_modules(&["DyadicRationals"]);
        assert!(has_complete_builtin_override("Add", 2, &ctx_dr));
        assert!(has_complete_builtin_override("Half", 1, &ctx_dr));
        assert!(!has_complete_builtin_override("Add", 1, &ctx_dr)); // wrong arity
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn functions_fold_override_requires_module() {
        let ctx_none = EvalCtx::new();
        assert!(!has_complete_builtin_override("FoldFunction", 3, &ctx_none));
        let ctx_fn = ctx_with_modules(&["Functions"]);
        assert!(has_complete_builtin_override("FoldFunction", 3, &ctx_fn));
        assert!(has_complete_builtin_override(
            "FoldFunctionOnSet",
            4,
            &ctx_fn
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn fold_set_override_requires_finite_sets_ext() {
        let ctx_none = EvalCtx::new();
        // After fix: FoldSet is NOT overridden without FiniteSetsExt
        assert!(!has_complete_builtin_override("FoldSet", 3, &ctx_none));
        let ctx_fse = ctx_with_modules(&["FiniteSetsExt"]);
        assert!(has_complete_builtin_override("FoldSet", 3, &ctx_fse));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn fold_seq_left_right_override_requires_sequences_ext() {
        let ctx_none = EvalCtx::new();
        // After fix: these are NOT overridden without SequencesExt
        assert!(!has_complete_builtin_override("FoldSeq", 3, &ctx_none));
        assert!(!has_complete_builtin_override("FoldLeft", 3, &ctx_none));
        assert!(!has_complete_builtin_override("FoldRight", 3, &ctx_none));
        assert!(!has_complete_builtin_override(
            "FoldLeftDomain",
            3,
            &ctx_none
        ));
        assert!(!has_complete_builtin_override(
            "FoldRightDomain",
            3,
            &ctx_none
        ));
        let ctx_se = ctx_with_modules(&["SequencesExt"]);
        assert!(has_complete_builtin_override("FoldSeq", 3, &ctx_se));
        assert!(has_complete_builtin_override("FoldLeft", 3, &ctx_se));
        assert!(has_complete_builtin_override("FoldRight", 3, &ctx_se));
        assert!(has_complete_builtin_override("FoldLeftDomain", 3, &ctx_se));
        assert!(has_complete_builtin_override("FoldRightDomain", 3, &ctx_se));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn unknown_operators_never_overridden() {
        let ctx_all = ctx_with_modules(&[
            "DyadicRationals",
            "Functions",
            "FiniteSetsExt",
            "SequencesExt",
        ]);
        assert!(!has_complete_builtin_override("MyCustomOp", 2, &ctx_all));
        assert!(!has_complete_builtin_override("UserFold", 3, &ctx_all));
    }
}
