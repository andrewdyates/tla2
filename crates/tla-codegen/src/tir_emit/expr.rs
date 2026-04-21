// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR expression to Rust source translation.
//!
//! Translates `TirExpr` nodes into Rust source text. Parallels the AST-based
//! `emit/expr/mod.rs` but operates on the typed intermediate representation.

use super::util::to_snake_case;
use crate::types::struct_registry::{self, StructRegistry};
use tla_tir::{
    TirActionSubscriptKind, TirArithOp, TirBoolOp, TirBoundVar, TirCmpOp, TirExceptPathElement,
    TirExceptSpec, TirExpr, TirNameKind, TirSetOp,
};
use tla_value::Value;

/// Stack overflow protection for recursive tree walks.
///
/// Uses `stacker::maybe_grow` with canonical constants matching the evaluator
/// (1MB red zone, 16MB growth). Prevents stack overflow on deeply nested TIR
/// expressions produced by operator inlining (e.g., SyncStateMachine with 14
/// actions, 9 variables, nested EXCEPT/quantifiers — ~480 line specs).
#[inline(always)]
fn stack_safe<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(1024 * 1024, 16 * 1024 * 1024, f)
}

/// Scope context for expression translation.
pub(super) struct ExprScope<'a> {
    /// Whether to prefix state variable access with `state.`
    pub(super) prefix_state: bool,
    /// The identifier used for current state (e.g., "state", "old")
    pub(super) state_ref: &'a str,
    /// Optional identifier for primed state (e.g., "new")
    pub(super) prime_state_ref: Option<&'a str>,
    /// Set of TLA+ variable names that are state variables.
    /// Used to resolve Name references that are state variables vs local bindings.
    pub(super) state_vars: &'a std::collections::HashSet<String>,
    /// Set of constant names from the .cfg file. These are emitted as functions,
    /// so references need `()` appended.
    pub(super) constant_names: &'a std::collections::HashSet<String>,
    /// Set of helper operator names that are emitted as `Self::` methods.
    /// When an Apply references one of these, it gets `Self::` prefix.
    pub(super) helper_names: &'a std::collections::HashSet<String>,
    /// Helpers that transitively reference state variables and need `state` passed.
    pub(super) helpers_needing_state: &'a std::collections::HashSet<String>,
    /// Recursive helpers that take a `__depth` argument.
    pub(super) recursive_helper_names: &'a std::collections::HashSet<String>,
    /// Parameter counts for helper operators (name -> param count).
    /// Used to distinguish zero-arg calls from higher-order operator references.
    pub(super) helper_param_counts: &'a std::collections::HashMap<String, usize>,
    /// Current recursion depth variable inside a recursive helper body.
    pub(super) recursive_depth_var: Option<&'a str>,
    /// State variables whose type is a sequence (Vec<T>), for FuncApply indexing.
    pub(super) seq_vars: &'a std::collections::HashSet<String>,
    /// Optional struct registry for type-specialized record codegen.
    /// When present, records with known fields emit struct construction/access.
    pub(super) struct_registry: Option<&'a StructRegistry>,
    /// Inferred variable types, used to resolve record access targets to struct types.
    pub(super) var_types: Option<&'a std::collections::HashMap<String, crate::types::TlaType>>,
    /// Invariant operator names. Calls to these get a `check_` prefix because
    /// invariant operators are emitted as `check_{name}(state)` methods.
    pub(super) invariant_names: &'a std::collections::HashSet<String>,
}

impl<'a> ExprScope<'a> {
    pub(super) fn with_state(
        state_vars: &'a std::collections::HashSet<String>,
        constant_names: &'a std::collections::HashSet<String>,
        helper_names: &'a std::collections::HashSet<String>,
        helpers_needing_state: &'a std::collections::HashSet<String>,
        recursive_helper_names: &'a std::collections::HashSet<String>,
        seq_vars: &'a std::collections::HashSet<String>,
    ) -> Self {
        static EMPTY_MAP: std::sync::LazyLock<std::collections::HashMap<String, usize>> =
            std::sync::LazyLock::new(std::collections::HashMap::new);
        static EMPTY_SET: std::sync::LazyLock<std::collections::HashSet<String>> =
            std::sync::LazyLock::new(std::collections::HashSet::new);
        ExprScope {
            prefix_state: true,
            state_ref: "state",
            prime_state_ref: None,
            state_vars,
            constant_names,
            helper_names,
            helpers_needing_state,
            recursive_helper_names,
            helper_param_counts: &EMPTY_MAP,
            recursive_depth_var: None,
            seq_vars,
            struct_registry: None,
            var_types: None,
            invariant_names: &EMPTY_SET,
        }
    }

    pub(super) fn bare(
        state_vars: &'a std::collections::HashSet<String>,
        constant_names: &'a std::collections::HashSet<String>,
        helper_names: &'a std::collections::HashSet<String>,
        helpers_needing_state: &'a std::collections::HashSet<String>,
        recursive_helper_names: &'a std::collections::HashSet<String>,
        seq_vars: &'a std::collections::HashSet<String>,
    ) -> Self {
        static EMPTY_MAP: std::sync::LazyLock<std::collections::HashMap<String, usize>> =
            std::sync::LazyLock::new(std::collections::HashMap::new);
        static EMPTY_SET: std::sync::LazyLock<std::collections::HashSet<String>> =
            std::sync::LazyLock::new(std::collections::HashSet::new);
        ExprScope {
            prefix_state: false,
            state_ref: "state",
            prime_state_ref: None,
            state_vars,
            constant_names,
            helper_names,
            helpers_needing_state,
            recursive_helper_names,
            helper_param_counts: &EMPTY_MAP,
            recursive_depth_var: None,
            seq_vars,
            struct_registry: None,
            var_types: None,
            invariant_names: &EMPTY_SET,
        }
    }

    pub(super) fn with_recursive_depth(mut self, recursive_depth_var: &'a str) -> Self {
        self.recursive_depth_var = Some(recursive_depth_var);
        self
    }

    /// Set helper operator parameter counts for higher-order operator reference codegen.
    pub(super) fn with_helper_param_counts(
        mut self,
        counts: &'a std::collections::HashMap<String, usize>,
    ) -> Self {
        self.helper_param_counts = counts;
        self
    }

    /// Set the struct registry for type-specialized record codegen.
    pub(super) fn with_struct_registry(mut self, registry: &'a StructRegistry) -> Self {
        self.struct_registry = Some(registry);
        self
    }

    /// Set inferred variable types for struct-aware record access resolution.
    pub(super) fn with_var_types(
        mut self,
        var_types: &'a std::collections::HashMap<String, crate::types::TlaType>,
    ) -> Self {
        self.var_types = Some(var_types);
        self
    }

    /// Set invariant names so operator calls to invariants emit `check_` prefix.
    pub(super) fn with_invariant_names(
        mut self,
        invariant_names: &'a std::collections::HashSet<String>,
    ) -> Self {
        self.invariant_names = invariant_names;
        self
    }

}

/// Translate a TIR expression to Rust source text.
pub(super) fn tir_expr_to_rust(expr: &TirExpr, scope: &ExprScope<'_>) -> String {
    stack_safe(|| tir_expr_to_rust_inner(expr, scope))
}

fn tir_expr_to_rust_inner(expr: &TirExpr, scope: &ExprScope<'_>) -> String {
    match expr {
        // === Constants ===
        TirExpr::Const { value, .. } => value_to_rust(value),

        // === Names ===
        TirExpr::Name(name_ref) => {
            let name = &name_ref.name;
            // Check if this identifier is a state variable (either by TirNameKind
            // or by membership in state_vars set — the AST may not tag variables
            // with StateVar kind when they come through the codegen lowering path)
            let is_state_var = matches!(name_ref.kind, TirNameKind::StateVar { .. })
                || scope.state_vars.contains(name);
            if is_state_var && scope.prefix_state {
                format!("{}.{}.clone()", scope.state_ref, to_snake_case(name))
            } else if scope.constant_names.contains(name) {
                // Config constants are emitted as functions, call them
                format!("{}()", to_snake_case(name))
            } else if scope.invariant_names.contains(name) {
                // Invariant operators are emitted as check_{name}(state)
                let fn_name = to_snake_case(name);
                format!("Self::check_{fn_name}({})", scope.state_ref)
            } else if scope.helper_names.contains(name) {
                // Zero-arg operator reference: emit as Self::method(state) or Self::method()
                let fn_name = to_snake_case(name);
                let needs_state =
                    scope.helpers_needing_state.contains(name) && scope.prefix_state;
                if scope.recursive_helper_names.contains(name) {
                    let depth_arg = scope
                        .recursive_depth_var
                        .map_or_else(|| "0".to_string(), |var| format!("{var} + 1"));
                    if needs_state {
                        format!("Self::{fn_name}({}, {depth_arg})", scope.state_ref)
                    } else {
                        format!("Self::{fn_name}({depth_arg})")
                    }
                } else if needs_state {
                    format!("Self::{fn_name}({})", scope.state_ref)
                } else {
                    format!("Self::{fn_name}()")
                }
            } else {
                // Check built-in constants and standard module names
                match name.as_str() {
                    "TRUE" => "true".to_string(),
                    "FALSE" => "false".to_string(),
                    "BOOLEAN" => "boolean_set()".to_string(),
                    // Standard module sets (infinite — panic at runtime if enumerated)
                    "Nat" => "/* Nat: infinite set */ panic!(\"Cannot enumerate Nat\")".to_string(),
                    "Int" => "/* Int: infinite set */ panic!(\"Cannot enumerate Int\")".to_string(),
                    "STRING" => "/* STRING: infinite set */ panic!(\"Cannot enumerate STRING\")".to_string(),
                    "REAL" | "Real" => "/* Real: infinite set */ panic!(\"Cannot enumerate Real\")".to_string(),
                    _ => {
                        // Check if this is a known operator that was skipped
                        // (action or temporal) — emit `false` as a safe stub
                        let is_known_op = super::ALL_OPERATOR_NAMES.with(|cell| {
                            cell.borrow().contains(name)
                        });
                        if is_known_op {
                            return format!("false /* action/temporal: {name} */");
                        }
                        to_snake_case(name)
                    }
                }
            }
        }

        // === Boolean operations ===
        TirExpr::BoolBinOp { left, op, right } => {
            let l = tir_expr_to_rust(&left.node, scope);
            let r = tir_expr_to_rust(&right.node, scope);
            match op {
                TirBoolOp::And => format!("({l} && {r})"),
                TirBoolOp::Or => format!("({l} || {r})"),
                TirBoolOp::Implies => format!("(!{l} || {r})"),
                TirBoolOp::Equiv => format!("({l} == {r})"),
            }
        }
        TirExpr::BoolNot(inner) => {
            format!("!{}", tir_expr_to_rust(&inner.node, scope))
        }

        // === Comparison ===
        TirExpr::Cmp { left, op, right } => {
            let l = tir_expr_to_rust(&left.node, scope);
            let r = tir_expr_to_rust(&right.node, scope);
            let op_str = match op {
                TirCmpOp::Eq => "==",
                TirCmpOp::Neq => "!=",
                TirCmpOp::Lt => "<",
                TirCmpOp::Leq => "<=",
                TirCmpOp::Gt => ">",
                TirCmpOp::Geq => ">=",
            };
            format!("({l} {op_str} {r})")
        }

        // === Arithmetic ===
        TirExpr::ArithBinOp { left, op, right } => {
            let l = tir_expr_to_rust(&left.node, scope);
            let r = tir_expr_to_rust(&right.node, scope);
            match op {
                TirArithOp::Add => format!("({l} + {r})"),
                TirArithOp::Sub => format!("({l} - {r})"),
                TirArithOp::Mul => format!("({l} * {r})"),
                TirArithOp::Div => format!("({l} / {r})"),
                TirArithOp::IntDiv => format!(
                    "({{ let __a = {l}; let __b = {r}; let __q = __a / __b; if (__a ^ __b) < 0 && __a % __b != 0 {{ __q - 1 }} else {{ __q }} }})"
                ),
                TirArithOp::Mod => format!(
                    "({{ let __a = {l}; let __b = {r}; let __r = __a % __b; if __r < 0 {{ __r + __b }} else {{ __r }} }})"
                ),
                TirArithOp::Pow => format!("{l}.pow({r} as u32)"),
            }
        }
        TirExpr::ArithNeg(inner) => {
            format!("(-{})", tir_expr_to_rust(&inner.node, scope))
        }

        // === Range ===
        TirExpr::Range { lo, hi } => {
            format!(
                "range_set({}, {})",
                tir_expr_to_rust(&lo.node, scope),
                tir_expr_to_rust(&hi.node, scope)
            )
        }

        // === Set membership ===
        TirExpr::In { elem, set } => {
            if let TirExpr::Range { lo, hi } = &set.node {
                let e = tir_expr_to_rust(&elem.node, scope);
                let l = tir_expr_to_rust(&lo.node, scope);
                let h = tir_expr_to_rust(&hi.node, scope);
                format!(
                    "{{ let __e = {e}; let __l = {l}; let __h = {h}; (__e >= __l && __e <= __h) }}"
                )
            } else {
                let set_str = tir_expr_to_rust(&set.node, scope);
                let elem_str = tir_expr_to_rust(&elem.node, scope);
                // When the element is a purely Value-typed state var but the
                // set has concrete element types, convert the set to
                // TlaSet<Value> first. Only for pure Value types, not
                // for functions with Value keys.
                if is_pure_value_typed(&elem.node, scope) {
                    format!("{set_str}.to_value_set().contains(&{elem_str})")
                } else {
                    format!("{set_str}.contains(&{elem_str})")
                }
            }
        }
        TirExpr::Subseteq { left, right } => {
            let l = tir_expr_to_rust(&left.node, scope);
            let r = tir_expr_to_rust(&right.node, scope);
            let left_is_value = is_value_typed_target(&left.node, scope) || is_pure_value_typed(&left.node, scope);
            let right_is_value = is_value_typed_target(&right.node, scope) || is_pure_value_typed(&right.node, scope);
            if left_is_value && !right_is_value {
                // Left is Value, right is concrete set — convert right to Value
                format!("{l}.is_subset(&Value::from({r}))")
            } else if !left_is_value && right_is_value {
                // Left is concrete set, right is Value — convert right to Value set
                format!("{l}.to_value_set().is_subset(&Value::from({r}))")
            } else {
                format!("{l}.is_subset(&{r})")
            }
        }

        // === Set operations ===
        TirExpr::SetEnum(elems) => {
            if elems.is_empty() {
                // Type-annotate empty set to avoid inference failures in
                // comparisons against Value-typed state variables.
                "TlaSet::<Value>::new()".to_string()
            } else {
                let strs: Vec<_> = elems
                    .iter()
                    .map(|e| {
                        let s = tir_expr_to_rust(&e.node, scope);
                        // Wrap record/tuple literals with Value::from() so set
                        // elements are Value-typed, matching TlaSet<Value> state vars.
                        if matches!(e.node, TirExpr::Record(_) | TirExpr::Tuple(_)) {
                            format!("Value::from({s})")
                        } else {
                            s
                        }
                    })
                    .collect();
                format!("tla_set![{}]", strs.join(", "))
            }
        }
        TirExpr::SetBinOp { left, op, right } => {
            let l = tir_expr_to_rust(&left.node, scope);
            let r = tir_expr_to_rust(&right.node, scope);
            match op {
                TirSetOp::Union => format!("{l}.union(&{r})"),
                TirSetOp::Intersect => format!("{l}.intersect(&{r})"),
                TirSetOp::Minus => format!("{l}.difference(&{r})"),
            }
        }
        TirExpr::Powerset(inner) => {
            format!("powerset(&{})", tir_expr_to_rust(&inner.node, scope))
        }
        TirExpr::BigUnion(inner) => {
            format!(
                "TlaSet::from_iter({}.iter().flat_map(|__s| __s.iter().cloned()))",
                tir_expr_to_rust(&inner.node, scope)
            )
        }
        TirExpr::KSubset { base, k } => {
            format!(
                "k_subsets(&{}, {})",
                tir_expr_to_rust(&base.node, scope),
                tir_expr_to_rust(&k.node, scope)
            )
        }

        // === Set filter: {x \in S : P(x)} ===
        TirExpr::SetFilter { var, body } => {
            let var_name = to_snake_case(&var.name);
            let domain = var
                .domain
                .as_ref()
                .map(|d| tir_expr_to_rust(&d.node, scope))
                .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
            let pred = tir_expr_to_rust(&body.node, scope);
            format!(
                "TlaSet::from_iter({domain}.iter().filter(|__{var_name}| {{ let {var_name} = (*__{var_name}).clone(); {pred} }}).cloned())"
            )
        }

        // === Set builder: {expr : x \in S} ===
        TirExpr::SetBuilder { body, vars } => {
            if vars.len() == 1 {
                let v = &vars[0];
                let var_name = to_snake_case(&v.name);
                let domain = v
                    .domain
                    .as_ref()
                    .map(|d| tir_expr_to_rust(&d.node, scope))
                    .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
                let body_str = tir_expr_to_rust(&body.node, scope);
                format!(
                    "TlaSet::from_iter({domain}.iter().map(|__{var_name}| {{ let {var_name} = __{var_name}.clone(); {body_str} }}))"
                )
            } else {
                emit_multi_bound_set_builder(vars, body, scope)
            }
        }

        // === Quantifiers ===
        TirExpr::Forall { vars, body } => emit_quantifier(vars, body, "all", scope),
        TirExpr::Exists { vars, body } => emit_quantifier(vars, body, "any", scope),
        TirExpr::Choose { var, body } => {
            let var_name = to_snake_case(&var.name);
            let domain = var
                .domain
                .as_ref()
                .map(|d| tir_expr_to_rust(&d.node, scope))
                .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
            let pred = tir_expr_to_rust(&body.node, scope);
            format!(
                "{domain}.iter().find(|__{var_name}| {{ let {var_name} = (*__{var_name}).clone(); {pred} }}).cloned()\
                .expect(\"CHOOSE: no element satisfies predicate\")"
            )
        }

        // === Functions ===
        TirExpr::FuncDef { vars, body } => {
            if vars.len() == 1 {
                let v = &vars[0];
                let var_name = to_snake_case(&v.name);
                let domain = v
                    .domain
                    .as_ref()
                    .map(|d| tir_expr_to_rust(&d.node, scope))
                    .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
                let body_str = tir_expr_to_rust(&body.node, scope);
                format!(
                    "TlaFunc::from_iter({domain}.iter().map(|__{var_name}| {{ let {var_name} = __{var_name}.clone(); ({var_name}.clone(), {body_str}) }}))"
                )
            } else {
                emit_multi_bound_func_def(vars, body, scope)
            }
        }
        TirExpr::FuncApply { func, arg } => {
            // Detect sequence indexing: if the function is a sequence variable,
            // emit Vec indexing instead of TlaFunc::apply.
            let is_seq = match &func.node {
                TirExpr::Name(name_ref) => scope.seq_vars.contains(&name_ref.name),
                _ => false,
            };
            if is_seq {
                let seq_str = tir_expr_to_rust(&func.node, scope);
                let idx_str = tir_expr_to_rust(&arg.node, scope);
                // TLA+ sequences are 1-indexed; Rust Vec is 0-indexed
                return format!("{seq_str}[({idx_str} as usize) - 1].clone()");
            }
            // Detect tuple element access: func[1], func[2] with constant integer index.
            // This arises from patterns like `entry[1]` where entry is a local tuple binding.
            if let TirExpr::Const {
                value: Value::SmallInt(n),
                ..
            } = &arg.node
            {
                let idx = *n as usize;
                // TLA+ tuple indexing is 1-based; Rust tuple fields are 0-based
                if idx >= 1 && idx <= 10 {
                    let func_str = tir_expr_to_rust(&func.node, scope);
                    return format!("{func_str}.{}", idx - 1);
                }
            }
            // Value::Int (BigInt) tuple indexing not needed; SmallInt covers all practical cases
            // Wrap arg with Value::from() when target is a Value-typed state variable,
            // since Value::apply takes &Value but the arg may be a concrete type like i64.
            let needs_value_wrap = is_value_typed_target(&func.node, scope);
            let arg_str = tir_expr_to_rust(&arg.node, scope);
            let arg_expr = if needs_value_wrap {
                // Clone before converting to avoid moving variables that may
                // be used again (e.g., in nested quantifiers)
                format!("Value::from({}.clone())", arg_str)
            } else {
                arg_str
            };
            format!(
                "{}.apply(&{}).cloned().expect(\"function application requires key in domain\")",
                tir_expr_to_rust(&func.node, scope),
                arg_expr
            )
        }
        TirExpr::FuncSet { domain, range } => {
            let d = tir_expr_to_rust(&domain.node, scope);
            let r = tir_expr_to_rust(&range.node, scope);
            format!(
                r#"{{
    let __domain: Vec<_> = ({d}).iter().cloned().collect();
    let __range: Vec<_> = ({r}).iter().cloned().collect();
    let __dom_len = __domain.len();
    let __range_len = __range.len();
    if __dom_len > 10 || __range_len.checked_pow(__dom_len as u32).map_or(true, |n| n > 10000) {{
        panic!("FuncSet too large: domain_size={{}}, range_size={{}}", __dom_len, __range_len);
    }}
    let mut __result = TlaSet::new();
    let __total = __range_len.pow(__dom_len as u32);
    for __i in 0..__total {{
        let mut __f_entries = Vec::new();
        let mut __n = __i;
        for __d in &__domain {{
            __f_entries.push((__d.clone(), __range[__n % __range_len].clone()));
            __n /= __range_len;
        }}
        __result.insert(TlaFunc::from_iter(__f_entries));
    }}
    __result
}}"#
            )
        }
        TirExpr::Domain(inner) => {
            format!("{}.domain()", tir_expr_to_rust(&inner.node, scope))
        }

        // === Tuples ===
        TirExpr::Tuple(elems) => {
            if elems.is_empty() {
                "vec![]".to_string()
            } else {
                let strs: Vec<_> = elems
                    .iter()
                    .map(|e| tir_expr_to_rust(&e.node, scope))
                    .collect();
                format!("({})", strs.join(", "))
            }
        }
        TirExpr::Times(sets) => emit_times(sets, scope),

        // === Records ===
        TirExpr::Record(fields) => {
            // Try struct-based emission if registry is available
            if let Some(struct_name) = try_struct_for_record(fields, scope) {
                emit_struct_construction(&struct_name, fields, scope)
            } else {
                let field_strs: Vec<_> = fields
                    .iter()
                    .map(|(f, v)| {
                        let val = tir_expr_to_rust(&v.node, scope);
                        // Wrap typed values in Value::from() for TlaRecord<Value>
                        format!(
                            "(\"{}\".to_string(), Value::from({}))",
                            f.name,
                            val,
                        )
                    })
                    .collect();
                format!("TlaRecord::from_fields([{}])", field_strs.join(", "))
            }
        }
        TirExpr::RecordAccess { record, field } => {
            // Try struct field access if registry is available
            if let Some(_) = try_struct_for_record_access(record, scope) {
                let snake = struct_registry::field_to_snake_case(&field.name);
                format!(
                    "{}.{}.clone()",
                    tir_expr_to_rust(&record.node, scope),
                    snake
                )
            } else {
                format!(
                    "{}.get(\"{}\").cloned().expect(\"record field access\")",
                    tir_expr_to_rust(&record.node, scope),
                    field.name
                )
            }
        }
        TirExpr::RecordSet(fields) => {
            if fields.is_empty() {
                "tla_set![TlaRecord::new()]".to_string()
            } else if let Some(struct_name) = try_struct_for_record(fields, scope) {
                // Struct-based RecordSet: emit nested loops building structs
                let mut result = String::new();
                result.push_str("{\n");
                result.push_str("    let mut __records = TlaSet::new();\n");
                let field_names: Vec<_> = fields.iter().map(|(f, _)| f.name.clone()).collect();
                for (i, (_, v)) in fields.iter().enumerate() {
                    result.push_str(&format!(
                        "    for __f{i} in {} {{\n",
                        tir_expr_to_rust(&v.node, scope)
                    ));
                }
                result.push_str(&format!("    __records.insert({struct_name} {{"));
                for (i, name) in field_names.iter().enumerate() {
                    let snake = struct_registry::field_to_snake_case(name);
                    if i > 0 {
                        result.push_str(",");
                    }
                    result.push_str(&format!(" {snake}: __f{i}.clone()"));
                }
                result.push_str(" });\n");
                for _ in fields {
                    result.push_str("    }\n");
                }
                result.push_str("    __records\n}");
                result
            } else {
                let mut result = String::new();
                result.push_str("{\n");
                result.push_str("    let mut __records = TlaSet::new();\n");
                let field_names: Vec<_> = fields.iter().map(|(f, _)| f.name.clone()).collect();
                for (i, (_, v)) in fields.iter().enumerate() {
                    result.push_str(&format!(
                        "    for __f{i} in {} {{\n",
                        tir_expr_to_rust(&v.node, scope)
                    ));
                }
                // Wrap records as Value so the set is TlaSet<Value>,
                // matching Value-typed state vars.
                result.push_str("    __records.insert(Value::from(TlaRecord::from_fields([");
                for (i, name) in field_names.iter().enumerate() {
                    if i > 0 {
                        result.push_str(", ");
                    }
                    result.push_str(&format!("(\"{name}\".to_string(), Value::from(__f{i}.clone()))"));
                }
                result.push_str("])));\n");
                for _ in fields {
                    result.push_str("    }\n");
                }
                result.push_str("    __records\n}");
                result
            }
        }

        // === EXCEPT ===
        TirExpr::Except { base, specs } => emit_except(base, specs, scope),

        // === Control flow ===
        TirExpr::If { cond, then_, else_ } => {
            format!(
                "if {} {{ {} }} else {{ {} }}",
                tir_expr_to_rust(&cond.node, scope),
                tir_expr_to_rust(&then_.node, scope),
                tir_expr_to_rust(&else_.node, scope)
            )
        }
        TirExpr::Case { arms, other } => {
            let mut result = String::new();
            for (i, arm) in arms.iter().enumerate() {
                let cond = tir_expr_to_rust(&arm.guard.node, scope);
                let body = tir_expr_to_rust(&arm.body.node, scope);
                if i == 0 {
                    result.push_str(&format!("if {cond} {{ {body} }}"));
                } else {
                    result.push_str(&format!(" else if {cond} {{ {body} }}"));
                }
            }
            if let Some(other) = other {
                let other_str = tir_expr_to_rust(&other.node, scope);
                result.push_str(&format!(" else {{ {other_str} }}"));
            } else {
                result.push_str(" else { panic!(\"CASE: no matching arm\") }");
            }
            result
        }
        TirExpr::Let { defs, body } => {
            let mut result = "{\n".to_string();
            for def in defs {
                let name = to_snake_case(&def.name);
                if def.params.is_empty() {
                    let val = tir_expr_to_rust(&def.body.node, scope);
                    result.push_str(&format!("    let {name} = {val};\n"));
                } else {
                    let params: Vec<_> = def
                        .params
                        .iter()
                        .map(|p| format!("{}: _", to_snake_case(p)))
                        .collect();
                    let body_str = tir_expr_to_rust(&def.body.node, scope);
                    result.push_str(&format!(
                        "    let {name} = |{}| {body_str};\n",
                        params.join(", ")
                    ));
                }
            }
            let body_str = tir_expr_to_rust(&body.node, scope);
            result.push_str(&format!("    {body_str}\n}}"));
            result
        }

        // === Prime ===
        TirExpr::Prime(inner) => {
            if let TirExpr::Name(name_ref) = &inner.node {
                if let Some(prime_ref) = scope.prime_state_ref {
                    format!("{prime_ref}.{}.clone()", to_snake_case(&name_ref.name))
                } else {
                    format!("{}_next", to_snake_case(&name_ref.name))
                }
            } else {
                format!("/* unsupported prime expression */")
            }
        }

        // === UNCHANGED ===
        TirExpr::Unchanged(_) => {
            // UNCHANGED is analyzed at action level, not emitted as expression
            "true /* UNCHANGED handled at action level */".to_string()
        }

        // === Label (transparent) ===
        TirExpr::Label { body, .. } => tir_expr_to_rust(&body.node, scope),

        // === Lambda ===
        TirExpr::Lambda { params, body, .. } => {
            let param_strs: Vec<_> = params
                .iter()
                .map(|p| format!("{}: _", to_snake_case(p)))
                .collect();
            let body_str = tir_expr_to_rust(&body.node, scope);
            format!("|{}| {body_str}", param_strs.join(", "))
        }

        // === Apply (generic operator application) ===
        TirExpr::Apply { op, args } => {
            // Try to detect stdlib operators
            if let TirExpr::Name(name_ref) = &op.node {
                return translate_stdlib_apply(&name_ref.name, args, scope);
            }
            let op_str = tir_expr_to_rust(&op.node, scope);
            let args_str: Vec<_> = args
                .iter()
                .map(|a| tir_expr_to_rust(&a.node, scope))
                .collect();
            format!("{op_str}({})", args_str.join(", "))
        }

        // === Operator reference ===
        TirExpr::OperatorRef(op_ref) => emit_operator_ref(op_ref, scope),
        TirExpr::OpRef(name) => translate_operator_ref_to_closure(name),
        // ExceptAt is replaced during EXCEPT emission — reaching here means
        // the @ appeared outside an EXCEPT context, which is a TIR error.
        TirExpr::ExceptAt => "Value::Bool(false) /* EXCEPT @ outside EXCEPT context */".to_string(),

        // === Temporal operators ===
        TirExpr::Always(inner) => {
            let p = tir_expr_to_rust(&inner.node, scope);
            format!("TemporalProp::Always(Box::new(move |__state: &Self::State| {p}))")
        }
        TirExpr::Eventually(inner) => {
            let p = tir_expr_to_rust(&inner.node, scope);
            format!("TemporalProp::Eventually(Box::new(move |__state: &Self::State| {p}))")
        }
        TirExpr::LeadsTo { left, right } => {
            let p = tir_expr_to_rust(&left.node, scope);
            let q = tir_expr_to_rust(&right.node, scope);
            format!(
                "TemporalProp::LeadsTo(\
                    Box::new(move |__state: &Self::State| {p}), \
                    Box::new(move |__state: &Self::State| {q}))"
            )
        }
        TirExpr::WeakFair { vars, action } => {
            let v = tir_expr_to_rust(&vars.node, scope);
            let a = tir_expr_to_rust(&action.node, scope);
            format!(
                "TemporalProp::WeakFairness(\
                    Box::new(move |__state: &Self::State| {{ let _ = {v}; {a} }}))"
            )
        }
        TirExpr::StrongFair { vars, action } => {
            let v = tir_expr_to_rust(&vars.node, scope);
            let a = tir_expr_to_rust(&action.node, scope);
            format!(
                "TemporalProp::StrongFairness(\
                    Box::new(move |__state: &Self::State| {{ let _ = {v}; {a} }}))"
            )
        }
        TirExpr::Enabled(inner) => {
            let a = tir_expr_to_rust(&inner.node, scope);
            format!("/* ENABLED: action has successors */ !{{ let _ = {a}; false }}")
        }
        TirExpr::ActionSubscript { kind, action, subscript } => {
            let a = tir_expr_to_rust(&action.node, scope);
            let v = tir_expr_to_rust(&subscript.node, scope);
            match kind {
                TirActionSubscriptKind::Box => {
                    if let Some(prime_ref) = scope.prime_state_ref {
                        format!("({a} || ({prime_ref} == {v}))")
                    } else {
                        format!(
                            "TemporalProp::BoxAction(\
                                Box::new(move |__state: &Self::State| {a}), \
                                Box::new(move |__state: &Self::State| {v}))"
                        )
                    }
                }
                TirActionSubscriptKind::Angle => {
                    if let Some(prime_ref) = scope.prime_state_ref {
                        format!("({a} && ({prime_ref} != {v}))")
                    } else {
                        format!(
                            "TemporalProp::AngleAction(\
                                Box::new(move |__state: &Self::State| {a}), \
                                Box::new(move |__state: &Self::State| {v}))"
                        )
                    }
                }
            }
        }
    }
}

/// Emit a `TirExpr::OperatorRef` as Rust code.
///
/// `OperatorRef` carries a module path, operator name, and arguments. Three
/// cases arise in code generation:
///
/// 1. **With args** (e.g., `I!Scale(5)` or `Helper(x)`): emit as a function
///    call, mirroring the `Apply(Name(...), args)` path in `translate_stdlib_apply`.
/// 2. **Zero args, zero-arity operator** (e.g., `I!Init`): emit as a zero-arg
///    function call, same as the `Name` handler for helpers.
/// 3. **Zero args, parameterized operator** (e.g., passing `Add` to a
///    higher-order function): emit as a Rust closure wrapping the operator,
///    so the reference can be passed as a value.
fn emit_operator_ref(op_ref: &tla_tir::TirOperatorRef, scope: &ExprScope<'_>) -> String {
    let op_name = &op_ref.operator;
    let fn_name = to_snake_case(op_name);

    // Case 1: OperatorRef with arguments — emit as a function call.
    if !op_ref.args.is_empty() {
        return translate_stdlib_apply(op_name, &op_ref.args, scope);
    }

    // Zero-arg OperatorRef: check if the operator is a known helper.
    let is_helper = scope.helper_names.contains(op_name);

    if is_helper {
        // Check whether the target operator has parameters. If so, this is a
        // higher-order reference (the operator is being passed as a value, not
        // called). Emit a closure that wraps the helper method.
        let param_count = scope.helper_param_counts.get(op_name).copied().unwrap_or(0);

        if param_count > 0 {
            // Case 3: Higher-order reference to a parameterized operator.
            // Emit: |__p0, __p1, ...| Self::helper(&__p0, &__p1, ...)
            let closure_params: Vec<String> =
                (0..param_count).map(|i| format!("__p{i}")).collect();
            let closure_param_list = closure_params
                .iter()
                .map(|p| format!("{p}: _"))
                .collect::<Vec<_>>()
                .join(", ");

            let mut call_args: Vec<String> = Vec::new();
            let needs_state =
                scope.helpers_needing_state.contains(op_name) && scope.prefix_state;
            if needs_state {
                call_args.push(scope.state_ref.to_string());
            }
            for p in &closure_params {
                call_args.push(format!("&{p}"));
            }
            if scope.recursive_helper_names.contains(op_name) {
                let depth_arg = scope
                    .recursive_depth_var
                    .map_or_else(|| "0".to_string(), |var| format!("{var} + 1"));
                call_args.push(depth_arg);
            }
            format!(
                "|{closure_param_list}| Self::{fn_name}({})",
                call_args.join(", ")
            )
        } else {
            // Case 2: Zero-arg reference to a zero-arity helper — call it.
            let needs_state =
                scope.helpers_needing_state.contains(op_name) && scope.prefix_state;
            if scope.recursive_helper_names.contains(op_name) {
                let depth_arg = scope
                    .recursive_depth_var
                    .map_or_else(|| "0".to_string(), |var| format!("{var} + 1"));
                if needs_state {
                    format!("Self::{fn_name}({}, {depth_arg})", scope.state_ref)
                } else {
                    format!("Self::{fn_name}({depth_arg})")
                }
            } else if needs_state {
                format!("Self::{fn_name}({})", scope.state_ref)
            } else {
                format!("Self::{fn_name}()")
            }
        }
    } else if scope.constant_names.contains(op_name) {
        // Config constant — emit as function call.
        format!("{fn_name}()")
    } else {
        // Try stdlib closure (for higher-order refs like `+`, `Len`),
        // falls back to snake_case identifier for LET-bound/local operators.
        translate_operator_ref_to_closure(op_name)
    }
}

fn emit_quantifier(
    vars: &[TirBoundVar],
    body: &tla_core::Spanned<TirExpr>,
    method: &str,
    scope: &ExprScope<'_>,
) -> String {
    if vars.len() == 1 {
        let v = &vars[0];
        let var_name = to_snake_case(&v.name);
        let domain = v
            .domain
            .as_ref()
            .map(|d| tir_expr_to_rust(&d.node, scope))
            .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
        let body_str = tir_expr_to_rust(&body.node, scope);
        // iter() yields &T; clone into owned binding for the body
        format!(
            "{domain}.iter().{method}(|__{var_name}| {{ let {var_name} = __{var_name}.clone(); {body_str} }})"
        )
    } else {
        let mut result = String::new();
        for v in vars {
            let var_name = to_snake_case(&v.name);
            let domain = v
                .domain
                .as_ref()
                .map(|d| tir_expr_to_rust(&d.node, scope))
                .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
            result.push_str(&format!(
                "{domain}.iter().{method}(|__{var_name}| {{ let {var_name} = __{var_name}.clone(); "
            ));
        }
        result.push_str(&tir_expr_to_rust(&body.node, scope));
        for _ in vars {
            result.push_str(" })");
        }
        result
    }
}

fn emit_multi_bound_set_builder(
    vars: &[TirBoundVar],
    body: &tla_core::Spanned<TirExpr>,
    scope: &ExprScope<'_>,
) -> String {
    let mut iter_chain = String::new();
    for (i, v) in vars.iter().enumerate() {
        let var_name = to_snake_case(&v.name);
        let domain = v
            .domain
            .as_ref()
            .map(|d| tir_expr_to_rust(&d.node, scope))
            .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
        let method = if i == vars.len() - 1 {
            "map"
        } else {
            "flat_map"
        };
        iter_chain.push_str(&format!(
            "{domain}.iter().{method}(|__{var_name}| {{ let {var_name} = __{var_name}.clone(); "
        ));
    }
    iter_chain.push_str(&tir_expr_to_rust(&body.node, scope));
    for _ in vars {
        iter_chain.push_str(" })");
    }
    format!("TlaSet::from_iter({iter_chain})")
}

/// Emit a multi-bound function definition: `[x \in S, y \in T |-> expr]`.
///
/// TLA+ multi-bound FuncDef produces a function whose domain is `S \X T` (the
/// Cartesian product of the bound domains). Each key is a tuple of the bound
/// variable values, and the value is the body expression evaluated with those
/// bindings.
///
/// Generated code uses nested `flat_map`/`map` chains (same pattern as
/// `emit_multi_bound_set_builder`) but wraps the body in a `(key_tuple, body)`
/// pair for `TlaFunc::from_iter`.
fn emit_multi_bound_func_def(
    vars: &[TirBoundVar],
    body: &tla_core::Spanned<TirExpr>,
    scope: &ExprScope<'_>,
) -> String {
    let mut iter_chain = String::new();
    let var_names: Vec<String> = vars.iter().map(|v| to_snake_case(&v.name)).collect();

    for (i, v) in vars.iter().enumerate() {
        let var_name = &var_names[i];
        let domain = v
            .domain
            .as_ref()
            .map(|d| tir_expr_to_rust(&d.node, scope))
            .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
        let method = if i == vars.len() - 1 {
            "map"
        } else {
            "flat_map"
        };
        iter_chain.push_str(&format!(
            "{domain}.iter().{method}(|__{var_name}| {{ let {var_name} = __{var_name}.clone(); "
        ));
    }

    // Build the tuple key from all bound variables
    let key_tuple = if var_names.len() == 1 {
        format!("{}.clone()", var_names[0])
    } else {
        let parts: Vec<String> = var_names.iter().map(|n| format!("{n}.clone()")).collect();
        format!("({})", parts.join(", "))
    };

    let body_str = tir_expr_to_rust(&body.node, scope);
    iter_chain.push_str(&format!("({key_tuple}, {body_str})"));

    for _ in vars {
        iter_chain.push_str(" })");
    }
    format!("TlaFunc::from_iter({iter_chain})")
}

/// Emit an N-way Cartesian product: `S1 \X S2 \X ... \X Sn`.
///
/// Each element of the resulting set is a tuple `(e1, e2, ..., en)` where
/// `ei \in Si`. Generated code uses nested `flat_map` chains with the
/// innermost layer using `map` to construct the tuple.
fn emit_times(sets: &[tla_core::Spanned<TirExpr>], scope: &ExprScope<'_>) -> String {
    if sets.is_empty() {
        return "tla_set![()]".to_string();
    }
    if sets.len() == 1 {
        // Degenerate case: single-set Times is just a set of 1-tuples
        let s = tir_expr_to_rust(&sets[0].node, scope);
        return format!(
            "TlaSet::from_iter({s}.iter().map(|__t0| (__t0.clone(),)))"
        );
    }

    let mut iter_chain = String::new();
    for (i, set) in sets.iter().enumerate() {
        let set_str = tir_expr_to_rust(&set.node, scope);
        let var = format!("__t{i}");
        let method = if i == sets.len() - 1 { "map" } else { "flat_map" };
        if i == 0 {
            iter_chain.push_str(&format!("{set_str}.iter().{method}(|{var}| {{ let {var} = {var}.clone(); "));
        } else {
            iter_chain.push_str(&format!("{set_str}.iter().{method}(move |{var}| {{ let {var} = {var}.clone(); "));
        }
    }

    // Build the tuple from all variables
    let parts: Vec<String> = (0..sets.len()).map(|i| format!("__t{i}.clone()")).collect();
    iter_chain.push_str(&format!("({})", parts.join(", ")));

    for _ in sets {
        iter_chain.push_str(" })");
    }
    format!("TlaSet::from_iter({iter_chain})")
}

fn emit_except(
    base: &tla_core::Spanned<TirExpr>,
    specs: &[TirExceptSpec],
    scope: &ExprScope<'_>,
) -> String {
    let base_str = tir_expr_to_rust(&base.node, scope);
    // Determine if the base is a struct-typed record for field EXCEPT optimization.
    let is_struct = try_struct_for_record_access(base, scope).is_some();
    let needs_value_wrap = is_value_typed_target(&base.node, scope);
    if specs.len() == 1 && specs[0].path.len() == 1 {
        let spec = &specs[0];
        // Compute the old-value expression for EXCEPT @ substitution:
        // For single-path [f EXCEPT ![k] = @+1], @ means f[k].
        let at_str = except_at_string_inner(&base_str, &spec.path, scope, is_struct, needs_value_wrap);
        let val = tir_expr_to_rust_with_except_at(&spec.value.node, scope, &at_str);
        match &spec.path[0] {
            TirExceptPathElement::Index(idx) => {
                let key = tir_expr_to_rust(&idx.node, scope);
                // Clone key/val to avoid move conflicts when variables are
                // also used in other struct fields (e.g., Append push in trail)
                let needs_wrap = is_value_typed_target(&base.node, scope);
                let is_pure_value = is_pure_value_typed(&base.node, scope);
                let key_expr = if needs_wrap {
                    format!("Value::from({key}.clone())")
                } else {
                    format!("{key}.clone()")
                };
                let val_expr = if is_pure_value {
                    format!("Value::from({val}.clone())")
                } else {
                    format!("{val}.clone()")
                };
                format!("{base_str}.except({key_expr}, {val_expr})")
            }
            TirExceptPathElement::Field(field) => {
                if is_struct {
                    let snake = struct_registry::field_to_snake_case(&field.name);
                    format!(
                        "{{ let mut __r = {base_str}.clone(); __r.{snake} = {val}; __r }}"
                    )
                } else {
                    format!(
                        "{{ let mut __r = {base_str}.clone(); __r.set(\"{}\", {val}); __r }}",
                        field.name
                    )
                }
            }
        }
    } else {
        // Multi-spec EXCEPT: apply in order
        let mut result = format!("{{ let mut __base = {base_str}.clone();\n");
        for spec in specs {
            if spec.path.len() == 1 {
                // Single-path spec within multi-spec EXCEPT
                let at_str = except_at_string_inner("__base", &spec.path, scope, is_struct, needs_value_wrap);
                let val = tir_expr_to_rust_with_except_at(&spec.value.node, scope, &at_str);
                match &spec.path[0] {
                    TirExceptPathElement::Index(idx) => {
                        let key = tir_expr_to_rust(&idx.node, scope);
                        result.push_str(&format!("    __base.update({key}, {val});\n"));
                    }
                    TirExceptPathElement::Field(field) => {
                        if is_struct {
                            let snake = struct_registry::field_to_snake_case(&field.name);
                            result.push_str(&format!("    __base.{snake} = {val};\n"));
                        } else {
                            result.push_str(&format!(
                                "    __base.set(\"{}\", {val});\n",
                                field.name
                            ));
                        }
                    }
                }
            } else {
                // Multi-path spec (e.g., ![a][b] = v or !.x.y = v)
                emit_except_nested_path(&mut result, "__base", spec, scope);
            }
        }
        result.push_str("    __base\n}");
        result
    }
}

/// Build the Rust expression for `@` (the old value at the EXCEPT path).
///
/// For `[f EXCEPT ![k] = @ + 1]`, `@` means `f[k]`, so we chain accessor
/// calls along the full path starting from the base expression.
/// When `is_struct` is true, field access uses struct field syntax instead of
/// BTreeMap `.get()`.
fn except_at_string(
    base_str: &str,
    path: &[TirExceptPathElement],
    scope: &ExprScope<'_>,
    is_struct: bool,
) -> String {
    except_at_string_inner(base_str, path, scope, is_struct, true)
}

fn except_at_string_inner(
    base_str: &str,
    path: &[TirExceptPathElement],
    scope: &ExprScope<'_>,
    is_struct: bool,
    value_typed_base: bool,
) -> String {
    let mut current = base_str.to_string();
    for elem in path {
        current = match elem {
            TirExceptPathElement::Index(idx) => {
                let key = tir_expr_to_rust(&idx.node, scope);
                if value_typed_base {
                    format!(
                        "{current}.apply(&Value::from({key})).cloned()\
                         .expect(\"EXCEPT @ requires key in domain\")"
                    )
                } else {
                    format!(
                        "{current}.apply(&{key}).cloned()\
                         .expect(\"EXCEPT @ requires key in domain\")"
                    )
                }
            }
            TirExceptPathElement::Field(field) => {
                if is_struct {
                    let snake = struct_registry::field_to_snake_case(&field.name);
                    format!("{current}.{snake}.clone()")
                } else {
                    format!(
                        "{current}.get(\"{}\").cloned()\
                         .expect(\"EXCEPT @ requires existing field\")",
                        field.name
                    )
                }
            }
        };
    }
    current
}

/// Translate a TIR expression, substituting `TirExpr::ExceptAt` with the given
/// Rust expression string. All other nodes delegate to `tir_expr_to_rust`.
fn tir_expr_to_rust_with_except_at(
    expr: &TirExpr,
    scope: &ExprScope<'_>,
    at_replacement: &str,
) -> String {
    stack_safe(|| tir_expr_to_rust_with_except_at_inner(expr, scope, at_replacement))
}

fn tir_expr_to_rust_with_except_at_inner(
    expr: &TirExpr,
    scope: &ExprScope<'_>,
    at_replacement: &str,
) -> String {
    match expr {
        TirExpr::ExceptAt => at_replacement.to_string(),
        // Recurse into sub-expressions that may contain ExceptAt.
        // Stop recursion at nested Except nodes — inner @ is scoped to inner EXCEPT.
        TirExpr::ArithBinOp { left, op, right } => {
            let l = tir_expr_to_rust_with_except_at(&left.node, scope, at_replacement);
            let r = tir_expr_to_rust_with_except_at(&right.node, scope, at_replacement);
            match op {
                TirArithOp::Add => format!("({l} + {r})"),
                TirArithOp::Sub => format!("({l} - {r})"),
                TirArithOp::Mul => format!("({l} * {r})"),
                TirArithOp::Div => format!("({l} / {r})"),
                TirArithOp::IntDiv => format!(
                    "({{ let __a = {l}; let __b = {r}; let __q = __a / __b; if (__a ^ __b) < 0 && __a % __b != 0 {{ __q - 1 }} else {{ __q }} }})"
                ),
                TirArithOp::Mod => format!(
                    "({{ let __a = {l}; let __b = {r}; let __r = __a % __b; if __r < 0 {{ __r + __b }} else {{ __r }} }})"
                ),
                TirArithOp::Pow => format!("{l}.pow({r} as u32)"),
            }
        }
        TirExpr::ArithNeg(inner) => {
            format!(
                "(-{})",
                tir_expr_to_rust_with_except_at(&inner.node, scope, at_replacement)
            )
        }
        TirExpr::BoolBinOp { left, op, right } => {
            let l = tir_expr_to_rust_with_except_at(&left.node, scope, at_replacement);
            let r = tir_expr_to_rust_with_except_at(&right.node, scope, at_replacement);
            match op {
                TirBoolOp::And => format!("({l} && {r})"),
                TirBoolOp::Or => format!("({l} || {r})"),
                TirBoolOp::Implies => format!("(!{l} || {r})"),
                TirBoolOp::Equiv => format!("({l} == {r})"),
            }
        }
        TirExpr::BoolNot(inner) => {
            format!(
                "!{}",
                tir_expr_to_rust_with_except_at(&inner.node, scope, at_replacement)
            )
        }
        TirExpr::If { cond, then_, else_ } => {
            format!(
                "if {} {{ {} }} else {{ {} }}",
                tir_expr_to_rust_with_except_at(&cond.node, scope, at_replacement),
                tir_expr_to_rust_with_except_at(&then_.node, scope, at_replacement),
                tir_expr_to_rust_with_except_at(&else_.node, scope, at_replacement)
            )
        }
        TirExpr::Cmp { left, op, right } => {
            let l = tir_expr_to_rust_with_except_at(&left.node, scope, at_replacement);
            let r = tir_expr_to_rust_with_except_at(&right.node, scope, at_replacement);
            let op_str = match op {
                TirCmpOp::Eq => "==",
                TirCmpOp::Neq => "!=",
                TirCmpOp::Lt => "<",
                TirCmpOp::Leq => "<=",
                TirCmpOp::Gt => ">",
                TirCmpOp::Geq => ">=",
            };
            format!("({l} {op_str} {r})")
        }
        TirExpr::FuncApply { func, arg } => {
            let f = tir_expr_to_rust_with_except_at(&func.node, scope, at_replacement);
            let a = tir_expr_to_rust_with_except_at(&arg.node, scope, at_replacement);
            let needs_wrap = is_value_typed_target(&func.node, scope);
            let arg_expr = if needs_wrap { format!("Value::from({a}.clone())") } else { a };
            format!("{f}.apply(&{arg_expr}).cloned().expect(\"function application requires key in domain\")")
        }
        TirExpr::RecordAccess { record, field } => {
            // Use struct field access if the record target is a known struct type.
            if try_struct_for_record_access(record, scope).is_some() {
                let r = tir_expr_to_rust_with_except_at(&record.node, scope, at_replacement);
                let snake = struct_registry::field_to_snake_case(&field.name);
                format!("{r}.{snake}.clone()")
            } else {
                let r = tir_expr_to_rust_with_except_at(&record.node, scope, at_replacement);
                format!(
                    "{r}.get(\"{}\").cloned().expect(\"record field access\")",
                    field.name
                )
            }
        }
        TirExpr::SetEnum(elems) => {
            let strs: Vec<_> = elems
                .iter()
                .map(|e| tir_expr_to_rust_with_except_at(&e.node, scope, at_replacement))
                .collect();
            if strs.is_empty() {
                "TlaSet::new()".to_string()
            } else {
                format!("tla_set![{}]", strs.join(", "))
            }
        }
        TirExpr::Tuple(elems) => {
            let strs: Vec<_> = elems
                .iter()
                .map(|e| tir_expr_to_rust_with_except_at(&e.node, scope, at_replacement))
                .collect();
            if strs.is_empty() {
                "vec![]".to_string()
            } else {
                format!("({})", strs.join(", "))
            }
        }
        // Nested Except: @ inside is scoped to the inner EXCEPT, so delegate
        // to the standard emitter (which will compute its own @ replacement).
        TirExpr::Except { base, specs } => emit_except(base, specs, scope),
        // For all other expression types, no ExceptAt can appear, so delegate
        // to the standard emitter.
        _ => tir_expr_to_rust(expr, scope),
    }
}

/// Emit a nested multi-path EXCEPT spec (e.g., `![a][b] = v` or `!.x.y = v`).
///
/// Strategy: walk the path from outermost to innermost, reading each intermediate
/// value. Then apply the update at the innermost level and propagate back out.
fn emit_except_nested_path(
    result: &mut String,
    base_var: &str,
    spec: &TirExceptSpec,
    scope: &ExprScope<'_>,
) {
    let n = spec.path.len();
    assert!(n >= 2, "emit_except_nested_path called with path.len() < 2");

    // Convert path elements to typed enum for code generation
    #[derive(Clone)]
    enum PathElem {
        Index(String),
        Field(String),
    }

    let path_elems: Vec<PathElem> = spec
        .path
        .iter()
        .map(|elem| match elem {
            TirExceptPathElement::Index(idx) => PathElem::Index(tir_expr_to_rust(&idx.node, scope)),
            TirExceptPathElement::Field(f) => PathElem::Field(f.name.clone()),
        })
        .collect();

    // Emit key bindings for index path elements to avoid re-evaluation
    for (i, elem) in path_elems.iter().enumerate() {
        if let PathElem::Index(idx_str) = elem {
            result.push_str(&format!("    let __key_{i} = {idx_str};\n"));
        }
    }

    // Read intermediate values along the path (all except the last element)
    for (i, elem) in path_elems.iter().enumerate().take(n - 1) {
        let prev = if i == 0 {
            base_var.to_string()
        } else {
            format!("__inner_{}", i - 1)
        };
        let accessor = match elem {
            PathElem::Index(_) => {
                format!(
                    "{prev}.apply(&Value::from(__key_{i}.clone())).cloned()\
                     .expect(\"EXCEPT index path requires key in domain\")"
                )
            }
            PathElem::Field(f) => {
                format!(
                    "{prev}.get(\"{f}\").cloned()\
                     .expect(\"EXCEPT field path requires existing field\")"
                )
            }
        };
        result.push_str(&format!("    let __inner_{i} = {accessor};\n"));
    }

    // Compute the old-value expression for @ substitution in this spec.
    // The @ refers to the value at the full path, i.e., base[p0][p1]...[pN-1].
    // In nested EXCEPT paths, assume Value-typed base to be safe
    let at_str = except_at_string_inner(base_var, &spec.path, scope, false, true);
    let val = tir_expr_to_rust_with_except_at(&spec.value.node, scope, &at_str);

    // Apply the update at the innermost level
    let inner_idx = n - 2;
    let update_code = match &path_elems[n - 1] {
        PathElem::Index(_) => {
            format!(
                "{{ let mut __t = __inner_{inner_idx}.clone(); \
                 __t.update(__key_{}, {val}); __t }}",
                n - 1
            )
        }
        PathElem::Field(f) => {
            format!(
                "{{ let mut __t = __inner_{inner_idx}.clone(); \
                 __t.set(\"{f}\", {val}); __t }}"
            )
        }
    };
    result.push_str(&format!("    let __updated_{inner_idx} = {update_code};\n"));

    // Propagate the update back outward
    for i in (0..inner_idx).rev() {
        let updated_child = format!("__updated_{}", i + 1);
        let update_code = match &path_elems[i + 1] {
            PathElem::Index(_) => {
                format!(
                    "{{ let mut __t = __inner_{i}.clone(); \
                     __t.update(__key_{}, {updated_child}); __t }}",
                    i + 1
                )
            }
            PathElem::Field(f) => {
                format!(
                    "{{ let mut __t = __inner_{i}.clone(); \
                     __t.set(\"{f}\", {updated_child}); __t }}"
                )
            }
        };
        result.push_str(&format!("    let __updated_{i} = {update_code};\n"));
    }

    // Apply the outermost update to the base
    let final_updated = "__updated_0";
    match &path_elems[0] {
        PathElem::Index(_) => {
            result.push_str(&format!(
                "    {base_var}.update(__key_0, {final_updated});\n"
            ));
        }
        PathElem::Field(f) => {
            result.push_str(&format!(
                "    {base_var}.set(\"{f}\", {final_updated});\n"
            ));
        }
    }
}

/// Translate a bare operator reference to a Rust closure expression.
fn translate_operator_ref_to_closure(name: &str) -> String {
    match name {
        "+" => "|__a, __b| __a + __b".to_string(),
        "-" => "|__a, __b| __a - __b".to_string(),
        "*" => "|__a, __b| __a * __b".to_string(),
        "=" => "|__a: &_, __b: &_| __a == __b".to_string(),
        "/=" | "#" => "|__a: &_, __b: &_| __a != __b".to_string(),
        "<" => "|__a, __b| __a < __b".to_string(),
        ">" => "|__a, __b| __a > __b".to_string(),
        "<=" | "\\leq" => "|__a, __b| __a <= __b".to_string(),
        ">=" | "\\geq" => "|__a, __b| __a >= __b".to_string(),
        "/\\\\" | "\\land" => "|__a: bool, __b: bool| __a && __b".to_string(),
        "\\/" | "\\lor" => "|__a: bool, __b: bool| __a || __b".to_string(),
        "~" | "\\lnot" | "\\neg" => "|__a: bool| !__a".to_string(),
        "Len" => "|__s: &[_]| __s.len() as i64".to_string(),
        "Head" => "|__s: &[_]| __s.first().cloned().expect(\"Head of empty sequence\")".to_string(),
        "Tail" => "|__s: &[_]| __s.get(1..).unwrap_or_default().to_vec()".to_string(),
        "Append" => "|__s: &[_], __e| { let mut __r = __s.to_vec(); __r.push(__e); __r }".to_string(),
        "Cardinality" => "|__s: &TlaSet<_>| __s.len() as i64".to_string(),
        "DOMAIN" => "|__f: &TlaFunc<_, _>| __f.domain()".to_string(),
        "\\o" | "\\circ" => "|__a: Vec<_>, __b: Vec<_>| { let mut __r = __a; __r.extend(__b); __r }".to_string(),
        "Max" => "|__s: &TlaSet<_>| __s.iter().max().cloned().expect(\"Max requires non-empty set\")".to_string(),
        "Min" => "|__s: &TlaSet<_>| __s.iter().min().cloned().expect(\"Min requires non-empty set\")".to_string(),
        "Reverse" => "|__s: &[_]| { let mut __r = __s.to_vec(); __r.reverse(); __r }".to_string(),
        "@@" => "|__f: &TlaFunc<_, _>, __g: &TlaFunc<_, _>| func_merge(__f, __g)".to_string(),
        _ => to_snake_case(name),
    }
}

/// Translate stdlib operator applications.
fn translate_stdlib_apply(
    name: &str,
    args: &[tla_core::Spanned<TirExpr>],
    scope: &ExprScope<'_>,
) -> String {
    match name {
        "Len" if args.len() == 1 => {
            format!("({}.len() as i64)", tir_expr_to_rust(&args[0].node, scope))
        }
        "Append" if args.len() == 2 => {
            let seq = tir_expr_to_rust(&args[0].node, scope);
            let elem = tir_expr_to_rust(&args[1].node, scope);
            format!("{{ let mut __s = {seq}.clone(); __s.push({elem}); __s }}")
        }
        "Head" if args.len() == 1 => {
            format!(
                "{}.first().cloned().expect(\"Head of empty sequence\")",
                tir_expr_to_rust(&args[0].node, scope)
            )
        }
        "Tail" if args.len() == 1 => {
            format!(
                "{}.get(1..).unwrap_or_default().to_vec()",
                tir_expr_to_rust(&args[0].node, scope)
            )
        }
        "Cardinality" if args.len() == 1 => {
            format!("({}.len() as i64)", tir_expr_to_rust(&args[0].node, scope))
        }
        "SubSeq" if args.len() == 3 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            let m = tir_expr_to_rust(&args[1].node, scope);
            let n = tir_expr_to_rust(&args[2].node, scope);
            format!("{s}[({m} as usize - 1)..({n} as usize)].to_vec()")
        }
        "SelectSeq" if args.len() == 2 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            let test = tir_expr_to_rust(&args[1].node, scope);
            format!("{s}.iter().filter(|__x| ({test})(__x)).cloned().collect::<Vec<_>>()")
        }
        "Permutations" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("permutations(&{s})")
        }
        "DOMAIN" if args.len() == 1 => {
            let f = tir_expr_to_rust(&args[0].node, scope);
            format!("{f}.domain()")
        }
        "ToString" if args.len() == 1 => {
            let v = tir_expr_to_rust(&args[0].node, scope);
            format!("format!(\"{{:?}}\", {v})")
        }
        "IsFiniteSet" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("is_finite_set({s})")
        }
        "RandomElement" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("random_element(&{s})")
        }
        "Print" | "PrintT" if args.len() == 2 => {
            let msg = tir_expr_to_rust(&args[0].node, scope);
            let val = tir_expr_to_rust(&args[1].node, scope);
            format!("{{ eprintln!(\"{{:?}}\", {msg}); {val} }}")
        }
        "Print" | "PrintT" if args.len() == 1 => {
            let msg = tir_expr_to_rust(&args[0].node, scope);
            format!("{{ eprintln!(\"{{:?}}\", {msg}); true }}")
        }
        "Assert" if args.len() == 2 => {
            let cond = tir_expr_to_rust(&args[0].node, scope);
            let msg = tir_expr_to_rust(&args[1].node, scope);
            format!("{{ assert!({cond}, \"{{:?}}\", {msg}); true }}")
        }
        "TLCGet" if args.len() == 1 => {
            // TLC state counter — not meaningful in codegen
            "0_i64".to_string()
        }
        "TLCSet" if args.len() == 2 => {
            // TLC state counter — not meaningful in codegen
            "true".to_string()
        }
        "Seq" if args.len() == 1 => {
            // Seq(S) — the set of all sequences over S. Used in type constraints.
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("seq_set(&{s})")
        }

        // ===== Sequence concatenation: \o and \circ =====
        "\\o" | "\\circ" if args.len() == 2 => {
            let a = tir_expr_to_rust(&args[0].node, scope);
            let b = tir_expr_to_rust(&args[1].node, scope);
            format!("{{ let mut __s = {a}.clone(); __s.extend({b}.clone()); __s }}")
        }

        // ===== SequencesExt (community module) =====
        "Reverse" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("{{ let mut __s = {s}.clone(); __s.reverse(); __s }}")
        }
        "Front" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("{s}[..{s}.len() - 1].to_vec()")
        }
        "Last" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!(
                "{s}.last().cloned().expect(\"Last requires non-empty sequence\")"
            )
        }
        "Cons" if args.len() == 2 => {
            let elem = tir_expr_to_rust(&args[0].node, scope);
            let seq = tir_expr_to_rust(&args[1].node, scope);
            format!("{{ let mut __s = vec![{elem}]; __s.extend({seq}.clone()); __s }}")
        }
        "Contains" if args.len() == 2 => {
            let seq = tir_expr_to_rust(&args[0].node, scope);
            let elem = tir_expr_to_rust(&args[1].node, scope);
            format!("{seq}.contains(&{elem})")
        }
        // ToSet/Range(s) — convert sequence to set
        "ToSet" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("{s}.iter().cloned().collect::<TlaSet<_>>()")
        }
        // Indices(s) — {1, .., Len(s)}
        "Indices" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("range_set(1, {s}.len() as i64)")
        }
        // SortSeq(s, cmp) — sort sequence by comparator
        "SortSeq" if args.len() == 2 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            let cmp = tir_expr_to_rust(&args[1].node, scope);
            format!("{{ let mut __s = {s}.clone(); __s.sort_by(|a, b| if ({cmp})(a, b) {{ std::cmp::Ordering::Less }} else {{ std::cmp::Ordering::Greater }}); __s }}")
        }
        // SetToSeq(S) — convert set to sequence (in sorted order)
        "SetToSeq" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("{s}.iter().cloned().collect::<Vec<_>>()")
        }

        // ===== FiniteSetsExt (community module) =====
        "Max" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!(
                "{s}.iter().max().cloned().expect(\"Max requires non-empty set\")"
            )
        }
        "Min" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!(
                "{s}.iter().min().cloned().expect(\"Min requires non-empty set\")"
            )
        }
        "Sum" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("{s}.iter().sum::<i64>()")
        }
        "Product" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("{s}.iter().product::<i64>()")
        }
        "SymDiff" if args.len() == 2 => {
            let a = tir_expr_to_rust(&args[0].node, scope);
            let b = tir_expr_to_rust(&args[1].node, scope);
            format!("{a}.difference(&{b}).union(&{b}.difference(&{a}))")
        }
        "Flatten" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!("{s}.iter().fold(TlaSet::new(), |acc, s| acc.union(s))")
        }
        // Choose(S) — 1-arg form: pick arbitrary element from set
        "Choose" if args.len() == 1 => {
            let s = tir_expr_to_rust(&args[0].node, scope);
            format!(
                "{s}.iter().next().cloned().expect(\"Choose requires non-empty set\")"
            )
        }

        // ===== Functions module (community) =====
        // @@ — function merge: f @@ g
        "@@" if args.len() == 2 => {
            let f = tir_expr_to_rust(&args[0].node, scope);
            let g = tir_expr_to_rust(&args[1].node, scope);
            format!("func_merge(&{f}, &{g})")
        }
        // Restrict(f, S) — restrict function domain
        "Restrict" if args.len() == 2 => {
            let f = tir_expr_to_rust(&args[0].node, scope);
            let s = tir_expr_to_rust(&args[1].node, scope);
            format!(
                "TlaFunc::from_iter({f}.iter().filter(|(k, _)| {s}.contains(k)).map(|(k, v)| (k.clone(), v.clone())))"
            )
        }
        // IsInjective(f) — check if function is injective
        "IsInjective" if args.len() == 1 => {
            let f = tir_expr_to_rust(&args[0].node, scope);
            format!(
                "{{ let __vals: Vec<_> = {f}.iter().map(|(_, v)| v.clone()).collect(); \
                 __vals.len() == __vals.iter().collect::<std::collections::HashSet<_>>().len() }}"
            )
        }
        // FoldFunction(op, base, f) — fold over function values
        "FoldFunction" if args.len() == 3 => {
            let op = tir_expr_to_rust(&args[0].node, scope);
            let base = tir_expr_to_rust(&args[1].node, scope);
            let f = tir_expr_to_rust(&args[2].node, scope);
            format!(
                "{f}.iter().fold({base}, |__acc, (_, __v)| ({op})(__acc, __v.clone()))"
            )
        }
        // FoldSet(op, base, S) — fold over set elements
        "FoldSet" if args.len() == 3 => {
            let op = tir_expr_to_rust(&args[0].node, scope);
            let base = tir_expr_to_rust(&args[1].node, scope);
            let s = tir_expr_to_rust(&args[2].node, scope);
            format!(
                "{s}.iter().fold({base}, |__acc, __e| ({op})(__acc, __e.clone()))"
            )
        }
        // FoldSeq(op, base, seq) — fold over sequence elements
        "FoldSeq" if args.len() == 3 => {
            let op = tir_expr_to_rust(&args[0].node, scope);
            let base = tir_expr_to_rust(&args[1].node, scope);
            let seq = tir_expr_to_rust(&args[2].node, scope);
            format!(
                "{seq}.iter().fold({base}, |__acc, __e| ({op})(__acc, __e.clone()))"
            )
        }

        // ===== TLC module extras =====
        "JavaTime" if args.is_empty() => {
            "std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)\
             .expect(\"system clock should be at or after UNIX_EPOCH\")\
             .as_millis() as i64"
                .to_string()
        }

        // ===== Bags module =====
        "EmptyBag" if args.is_empty() => "TlaFunc::new()".to_string(),

        _ => {
            // Check if this is a reference to an invariant operator
            if scope.invariant_names.contains(name) {
                let fn_name = to_snake_case(name);
                // Invariant operators are emitted as check_{name}(state)
                return format!("Self::check_{fn_name}({})", scope.state_ref);
            }
            // Unknown operator: emit as function call.
            // If it's a known helper on the struct, prefix with `Self::`.
            let fn_name = to_snake_case(name);
            let is_helper = scope.helper_names.contains(name);
            if !is_helper {
                // Non-helper operator: either a known action/temporal op
                // (contains primes, failed EXTENDS import, etc.), or a
                // community module function we can't resolve. Emit `false`
                // stub to produce compilable code. This is correct for
                // action operators in Next disjuncts (the action's state
                // update is what matters, and the guard is handled by the
                // action decomposition).
                return format!("false /* unresolved op: {name} */");
            }

            let mut call_args: Vec<String> = Vec::new();
            // If the helper needs state, pass it as the first argument
            if scope.helpers_needing_state.contains(name) && scope.prefix_state {
                call_args.push(scope.state_ref.to_string());
            }
            // Helper parameters use & (borrow) for value args
            for a in args {
                let arg_str = tir_expr_to_rust(&a.node, scope);
                call_args.push(format!("&{arg_str}"));
            }
            if scope.recursive_helper_names.contains(name) {
                let depth_arg = scope
                    .recursive_depth_var
                    .map_or_else(|| "0".to_string(), |var| format!("{var} + 1"));
                call_args.push(depth_arg);
            }
            format!("Self::{fn_name}({})", call_args.join(", "))
        }
    }
}

/// Convert a TLA+ runtime `Value` to Rust source text.
pub(super) fn value_to_rust(value: &Value) -> String {
    match value {
        Value::Bool(b) => b.to_string(),
        Value::SmallInt(n) => format!("{n}_i64"),
        Value::Int(n) => format!("{n}_i64"),
        Value::String(s) => format!("{s:?}.to_string()"),

        // Set literal: TlaSet::from([elem1, elem2, ...])
        Value::Set(sorted_set) => {
            let elems: Vec<_> = sorted_set.iter().map(value_to_rust).collect();
            if elems.is_empty() {
                "TlaSet::new()".to_string()
            } else {
                format!("tla_set![{}]", elems.join(", "))
            }
        }

        // Tuple literal: (a, b, c)
        Value::Tuple(elements) => {
            if elements.is_empty() {
                "()".to_string()
            } else {
                let strs: Vec<_> = elements.iter().map(value_to_rust).collect();
                format!("({})", strs.join(", "))
            }
        }

        // Record literal: TlaRecord::from_fields([("field", value), ...])
        Value::Record(record) => {
            let field_strs: Vec<_> = record
                .iter_str()
                .map(|(name, val)| {
                    format!("(\"{}\".to_string(), Value::from({}))", name, value_to_rust(val))
                })
                .collect();
            if field_strs.is_empty() {
                "TlaRecord::new()".to_string()
            } else {
                format!("TlaRecord::from_fields([{}])", field_strs.join(", "))
            }
        }

        // Sequence literal: vec![elem1, elem2, ...]
        Value::Seq(seq) => {
            let elems: Vec<_> = seq.iter().map(value_to_rust).collect();
            if elems.is_empty() {
                "vec![]".to_string()
            } else {
                format!("vec![{}]", elems.join(", "))
            }
        }

        // Model value: emitted as a string constant
        Value::ModelValue(name) => format!("{name:?}.to_string()"),

        _ => format!(
            "/* unsupported constant: {:?} */",
            std::mem::discriminant(value)
        ),
    }
}

/// Try to find a registered struct name for a record literal's fields.
/// Returns `Some(struct_name)` if the scope has a struct registry and all
/// field names in the record are found in a registered struct.
fn try_struct_for_record(
    fields: &[(tla_tir::TirFieldName, tla_core::Spanned<TirExpr>)],
    scope: &ExprScope<'_>,
) -> Option<String> {
    let registry = scope.struct_registry?;
    // Build a TlaType::Record-compatible field list from TIR field names.
    // We don't know field types from the TIR expression alone, so we use a
    // name-only lookup: check if any registered struct has exactly these field names.
    for gs in registry.all_structs() {
        let mut gs_names: Vec<_> = gs.fields.iter().map(|(n, _)| n.as_str()).collect();
        gs_names.sort();
        let mut rec_names: Vec<_> = fields.iter().map(|(f, _)| f.name.as_str()).collect();
        rec_names.sort();
        if gs_names == rec_names {
            return Some(gs.name.clone());
        }
    }
    None
}

/// Try to determine if a RecordAccess target is a known struct type.
/// Returns `Some(struct_name)` if the record expression appears to be a struct.
fn try_struct_for_record_access(
    record: &tla_core::Spanned<TirExpr>,
    scope: &ExprScope<'_>,
) -> Option<String> {
    let registry = scope.struct_registry?;
    // Check if the record expression is itself a Record literal
    if let TirExpr::Record(fields) = &record.node {
        return try_struct_for_record(fields, scope);
    }
    // For Name references that are state variables, look up their inferred type
    // in var_types and resolve the record type to a registered struct.
    if let TirExpr::Name(name_ref) = &record.node {
        if scope.state_vars.contains(&name_ref.name) {
            if let Some(var_types) = scope.var_types {
                if let Some(ty) = var_types.get(&name_ref.name) {
                    if let Some(fields) = ty.as_record_fields() {
                        return registry.lookup_record(fields).map(|gs| gs.name.clone());
                    }
                }
            }
            // Fallback: if there's exactly one registered struct, use it
            if registry.all_structs().len() == 1 {
                return Some(registry.all_structs()[0].name.clone());
            }
        }
    }
    None
}

/// Emit struct construction: `StructName { field1: expr1, field2: expr2 }`.
fn emit_struct_construction(
    struct_name: &str,
    fields: &[(tla_tir::TirFieldName, tla_core::Spanned<TirExpr>)],
    scope: &ExprScope<'_>,
) -> String {
    let mut result = format!("{struct_name} {{ ");
    let mut first = true;
    // Sort fields by name for deterministic output matching the struct definition
    let mut sorted_fields: Vec<_> = fields.iter().collect();
    sorted_fields.sort_by(|a, b| a.0.name.cmp(&b.0.name));
    for (f, v) in &sorted_fields {
        if !first {
            result.push_str(", ");
        }
        first = false;
        let snake = struct_registry::field_to_snake_case(&f.name);
        let val = tir_expr_to_rust(&v.node, scope);
        result.push_str(&format!("{snake}: {val}"));
    }
    result.push_str(" }");
    result
}

/// Check whether a TIR expression resolves to a `Value`-typed state variable.
///
/// Returns `true` when the expression is (or chains from) a state variable
/// whose inferred type is `Unknown` (`Value`).  This is used to decide whether
/// arguments to `.apply()`, `.except()`, `.get()` etc. need a `Value::from()`
/// wrapper so that concrete typed arguments (like `i64`) are converted to the
/// `Value` that the runtime method expects.
/// Check if the expression is purely Value-typed (the entire type is Unknown/Value,
/// not just a function with Value key). Used for except value wrapping.
fn is_pure_value_typed(expr: &TirExpr, scope: &ExprScope<'_>) -> bool {
    match expr {
        TirExpr::Name(name_ref) => {
            if scope.state_vars.contains(&name_ref.name) {
                if let Some(var_types) = scope.var_types {
                    return matches!(
                        var_types.get(&name_ref.name),
                        None | Some(crate::types::TlaType::Unknown)
                    );
                }
                return true;
            }
            false
        }
        TirExpr::FuncApply { func, .. } => is_pure_value_typed(&func.node, scope),
        TirExpr::RecordAccess { record, .. } => is_pure_value_typed(&record.node, scope),
        _ => false,
    }
}

/// Check if the expression targets a Value-typed variable or a function with
/// Value key. Used for wrapping apply/except keys with Value::from().
fn is_value_typed_target(expr: &TirExpr, scope: &ExprScope<'_>) -> bool {
    match expr {
        TirExpr::Name(name_ref) => {
            if scope.state_vars.contains(&name_ref.name) {
                // Check if this state variable is Value-typed or has a
                // function type with Value (Unknown) key
                if let Some(var_types) = scope.var_types {
                    match var_types.get(&name_ref.name) {
                        None | Some(crate::types::TlaType::Unknown) => return true,
                        Some(crate::types::TlaType::Func(k, _)) => {
                            return matches!(**k, crate::types::TlaType::Unknown);
                        }
                        _ => return false,
                    }
                }
                // No type info available — assume Value-typed to be safe
                return true;
            }
            false
        }
        // state.x.clone() patterns — unwrap the clone
        TirExpr::FuncApply { func, .. } => is_value_typed_target(&func.node, scope),
        TirExpr::RecordAccess { record, .. } => is_value_typed_target(&record.node, scope),
        _ => false,
    }
}
