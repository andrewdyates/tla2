// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::live_expr::ExprLevel;
use super::super::core::AstToLive;
use crate::eval::{apply_substitutions, EvalCtx};

/// Recognize well-known TLA+ standard library operators that are handled
/// natively by the evaluator's builtin dispatch chain. These operators
/// may not appear in the ops map (when the .tla file is not loaded) or
/// in the env (builtins bypass the env entirely). All are constant-level:
/// pure functions with no state variable references.
///
/// This mirrors TLC's knowledge of its Java override classes: the standard
/// library operators are known to be constant-level without inspecting their
/// TLA+ definitions (which are often dummy/placeholder bodies).
fn is_stdlib_builtin(name: &str) -> bool {
    matches!(
        name,
        // Sequences module
        "Seq" | "Len" | "Head" | "Tail" | "Append" | "SubSeq" | "SelectSeq"
        // FiniteSets module
        | "Cardinality" | "IsFiniteSet"
        // Naturals/Integers/Reals
        | "Nat" | "Int" | "Real" | "Infinity"
        // Booleans
        | "BOOLEAN"
        // TLC module
        | "Print" | "PrintT" | "Assert" | "JavaTime" | "TLCGet" | "TLCSet"
        | "TLCEval" | "Permutations" | "SortSeq" | "ToString" | "TLCModelValue"
        | "RandomElement" | "Any" | "ANY"
        // Bags module
        | "EmptyBag" | "IsABag" | "BagToSet" | "SetToBag" | "BagIn"
        | "CopiesIn" | "BagCardinality" | "BagCup" | "BagDiff" | "BagUnion"
        | "BagOfAll" | "SubBag" | "SqSubseteq"
        // SequencesExt module
        | "Reverse" | "Front" | "Last" | "SetToSeq" | "SetToSortSeq"
        | "ToSet" | "Cons" | "Contains" | "IsPrefix" | "IsSuffix"
        | "IsStrictPrefix" | "IsStrictSuffix" | "Snoc" | "FlattenSeq"
        | "Zip" | "LongestCommonPrefix" | "CommonPrefixes"
        | "FoldLeftDomain" | "FoldRightDomain"
        // FiniteSetsExt module
        | "Quantify" | "Ksubsets" | "SymDiff" | "Flatten" | "Choose"
        | "Sum" | "Product" | "ReduceSet" | "Mean" | "MapThenSumSet"
        | "Choices" | "ChooseUnique"
        // Functions module
        | "Restrict" | "IsInjective" | "IsSurjective" | "IsBijection"
        | "Inverse" | "Injection" | "Surjection" | "Bijection"
        | "ExistsInjection" | "ExistsSurjection" | "ExistsBijection"
        // TLCExt module
        | "AssertEq" | "AssertError" | "TLCDefer" | "TLCNoOp"
        // Builtin operator symbols (callable via Apply / operator replacement)
        | "+" | "-" | "*" | "/" | "%" | "^" | "\\div"
        | "\\cup" | "\\cap" | "\\"
        // BoundedSeq (community module)
        | "BoundedSeq"
        // Folds module
        | "MapThenFoldSet" | "FoldSet" | "FoldSeq" | "FoldFunction"
        | "FoldLeft" | "FoldRight"
    )
}

impl AstToLive {
    /// Classify an `Expr::Ident` with full context-aware operator resolution.
    ///
    /// Handles:
    /// - recursion-cycle guard (`visited.contains(name)`)
    /// - AST-level bound variable tracking from enclosing binders
    /// - config constants (CONSTANT declarations from model config)
    /// - operator replacement resolution (e.g. `Seq <- LimitedSeq`)
    /// - operator-body lookup via `ctx.get_op(name)`
    /// - operator parameter tracking (params are constant within body)
    /// - #2434: only apply instance substitutions to local-ops identifiers
    /// - bound-variable fallback via `ctx.has_local_binding(name)`
    /// - env-constant fallback for names in the evaluation environment
    /// - stdlib builtin fallback for natively-dispatched operators
    pub(super) fn level_ident_with_ctx(
        &self,
        ctx: &EvalCtx,
        name: &str,
        visited: &mut std::collections::HashSet<String>,
        bound_vars: &mut std::collections::HashSet<String>,
    ) -> ExprLevel {
        if visited.contains(name) {
            return ExprLevel::State;
        }
        // Check AST-level bound variables from enclosing binders (SetFilter,
        // Forall, Exists, Choose, SetBuilder, FuncDef, Lambda). These are
        // constant within their scope — they don't reference state variables.
        if bound_vars.contains(name) {
            return ExprLevel::Constant;
        }
        // Config constants (CONSTANT declarations from model config, e.g.
        // Values = {1,2,3,4,5}, MaxSeqLen = 8) are constant level by definition.
        if ctx.is_config_constant(name) {
            return ExprLevel::Constant;
        }

        // Apply operator replacement (e.g. `Seq <- LimitedSeq` from config).
        // This matches the evaluator's resolve_op_name() call. Without this,
        // the level analyzer looks up the unreplaced name (e.g. "Seq") which
        // may not be in the ops map, causing it to fall to the State default.
        let resolved = ctx.resolve_op_name(name);

        if let Some(op) = ctx.get_op(resolved) {
            visited.insert(resolved.to_owned());
            // #2434: only substitute instanced-module (local_ops) operators
            let from_local = ctx
                .local_ops()
                .as_ref()
                .is_some_and(|l| l.contains_key(resolved));
            let body = match (from_local, ctx.instance_substitutions()) {
                (true, Some(subs)) => apply_substitutions(&op.body, subs),
                _ => op.body.clone(),
            };
            // Track operator parameters as bound variables within the body.
            // Parameters like `S` in `LimitedSeq(S) == UNION {[1..n -> S] : ...}`
            // are constant within the operator body — they don't reference state.
            let added_params: Vec<String> = op
                .params
                .iter()
                .filter(|p| bound_vars.insert(p.name.node.clone()))
                .map(|p| p.name.node.clone())
                .collect();
            let level = self.get_level_with_ctx_inner(ctx, &body.node, visited, bound_vars);
            for p in &added_params {
                bound_vars.remove(p);
            }
            visited.remove(resolved);
            level
        } else {
            // Check if identifier is bound in the BindingChain (quantifier variable).
            // Liveness quantifier expansion binds variables to concrete values via
            // with_liveness_bindings(). These are effectively constants at conversion
            // time. Part of #3208.
            if ctx.has_local_binding(name) {
                return ExprLevel::Constant;
            }
            // Check if the identifier exists in the evaluation environment.
            // After state var resolution (which converts state variable Ident nodes
            // to StateVar nodes), remaining env entries are config constants, standard
            // module definitions, or other non-state bindings — all constant level.
            if ctx.env().contains_key(name) {
                return ExprLevel::Constant;
            }
            // Recognize well-known TLA+ standard library operators that are handled
            // natively by the evaluator's builtin dispatch chain. These operators
            // may not appear in the ops map (e.g., when the standard module .tla
            // file is not loaded) or in the env (builtins bypass the env entirely).
            // All stdlib builtins are constant-level: they are pure functions with
            // no state variable references.
            if is_stdlib_builtin(name) {
                return ExprLevel::Constant;
            }
            ExprLevel::State
        }
    }
}
