// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression translation: converts TLA+ AST expressions to Rust source text.
//! Handles literals, operators, quantifiers, set comprehensions, stdlib calls, etc.

mod builders;
mod except;
mod stdlib;
#[cfg(test)]
mod tests;

use super::{to_snake_case, ExceptPathElement, Expr, RustEmitter, Spanned};

fn emit_floor_int_div(lhs: String, rhs: String) -> String {
    format!(
        "({{ let __a = {lhs}; let __b = {rhs}; let __q = __a / __b; if (__a ^ __b) < 0 && __a % __b != 0 {{ __q - 1 }} else {{ __q }} }})"
    )
}

fn emit_floor_int_mod(lhs: String, rhs: String) -> String {
    // TLA+ % requires positive divisor (b > 0) per TLC semantics.
    // Euclidean mod: let r = a % b; if r < 0 { r + b } else { r }
    format!(
        "({{ let __a = {lhs}; let __b = {rhs}; let __r = __a % __b; if __r < 0 {{ __r + __b }} else {{ __r }} }})"
    )
}

impl<'a> RustEmitter<'a> {
    pub(in crate::emit) fn emit_membership_with_scope(
        &self,
        elem: &Expr,
        set: &Expr,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        if let Expr::Range(start, end) = set {
            let elem_str =
                self.expr_to_rust_with_scope(elem, prefix_state, state_ref, prime_state_ref);
            let start_str =
                self.expr_to_rust_with_scope(&start.node, prefix_state, state_ref, prime_state_ref);
            let end_str =
                self.expr_to_rust_with_scope(&end.node, prefix_state, state_ref, prime_state_ref);
            format!(
                "{{ let __elem = {elem_str}; let __start = {start_str}; let __end = {end_str}; (__elem >= __start && __elem <= __end) }}"
            )
        } else {
            format!(
                "{}.contains(&{})",
                self.expr_to_rust_with_scope(set, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(elem, prefix_state, state_ref, prime_state_ref)
            )
        }
    }

    pub(in crate::emit) fn emit_non_membership_with_scope(
        &self,
        elem: &Expr,
        set: &Expr,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        if let Expr::Range(start, end) = set {
            let elem_str =
                self.expr_to_rust_with_scope(elem, prefix_state, state_ref, prime_state_ref);
            let start_str =
                self.expr_to_rust_with_scope(&start.node, prefix_state, state_ref, prime_state_ref);
            let end_str =
                self.expr_to_rust_with_scope(&end.node, prefix_state, state_ref, prime_state_ref);
            format!(
                "{{ let __elem = {elem_str}; let __start = {start_str}; let __end = {end_str}; (__elem < __start || __elem > __end) }}"
            )
        } else {
            format!(
                "!{}.contains(&{})",
                self.expr_to_rust_with_scope(set, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(elem, prefix_state, state_ref, prime_state_ref)
            )
        }
    }

    /// Convert a TLA+ expression to Rust code
    pub(super) fn expr_to_rust(&self, expr: &Expr) -> String {
        self.expr_to_rust_with_scope(expr, false, "state", None)
    }

    /// Convert expression to Rust, optionally prefixing state variable access
    pub(in crate::emit) fn expr_to_rust_with_state(
        &self,
        expr: &Expr,
        prefix_state: bool,
    ) -> String {
        self.expr_to_rust_with_scope(expr, prefix_state, "state", None)
    }

    /// Convert expression to Rust, optionally prefixing state variable access
    /// with a different base identifier and mapping primed state variables to a
    /// separate base identifier.
    pub(in crate::emit) fn expr_to_rust_with_scope(
        &self,
        expr: &Expr,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        match expr {
            // Literals
            Expr::Bool(b) => b.to_string(),
            Expr::Int(n) => format!("{}_i64", n),
            Expr::String(s) => format!("{:?}.to_string()", s),

            // Variables
            Expr::Ident(name, _) => {
                if self.state_vars.contains(name) && prefix_state {
                    format!("{state_ref}.{}", to_snake_case(name))
                } else {
                    // Check for built-in constants
                    match name.as_str() {
                        "TRUE" => "true".to_string(),
                        "FALSE" => "false".to_string(),
                        "BOOLEAN" => "boolean_set()".to_string(),
                        _ => to_snake_case(name),
                    }
                }
            }

            // Logic
            Expr::And(a, b) => format!(
                "({} && {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Or(a, b) => format!(
                "({} || {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Not(a) => format!(
                "!{}",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Implies(a, b) => format!(
                "(!{} || {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Equiv(a, b) => format!(
                "({} == {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),

            // Comparison
            Expr::Eq(a, b) => format!(
                "({} == {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Neq(a, b) => format!(
                "({} != {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Lt(a, b) => format!(
                "({} < {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Leq(a, b) => format!(
                "({} <= {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Gt(a, b) => format!(
                "({} > {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Geq(a, b) => format!(
                "({} >= {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),

            // Arithmetic
            Expr::Add(a, b) => format!(
                "({} + {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Sub(a, b) => format!(
                "({} - {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Mul(a, b) => format!(
                "({} * {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Div(a, b) => format!(
                "({} / {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::IntDiv(a, b) => emit_floor_int_div(
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref),
            ),
            Expr::Mod(a, b) => emit_floor_int_mod(
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref),
            ),
            Expr::Pow(a, b) => format!(
                "{}.pow({} as u32)",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Neg(a) => format!(
                "-{}",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Range(a, b) => format!(
                "range_set({}, {})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),

            // Sets
            Expr::SetEnum(elems) => {
                if elems.is_empty() {
                    "TlaSet::new()".to_string()
                } else {
                    let elem_strs: Vec<_> = elems
                        .iter()
                        .map(|e| {
                            self.expr_to_rust_with_scope(
                                &e.node,
                                prefix_state,
                                state_ref,
                                prime_state_ref,
                            )
                        })
                        .collect();
                    format!("tla_set![{}]", elem_strs.join(", "))
                }
            }
            Expr::In(elem, set) => self.emit_membership_with_scope(
                &elem.node,
                &set.node,
                prefix_state,
                state_ref,
                prime_state_ref,
            ),
            Expr::NotIn(elem, set) => self.emit_non_membership_with_scope(
                &elem.node,
                &set.node,
                prefix_state,
                state_ref,
                prime_state_ref,
            ),
            Expr::Subseteq(a, b) => format!(
                "{}.is_subset(&{})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Union(a, b) => format!(
                "{}.union(&{})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Intersect(a, b) => format!(
                "{}.intersect(&{})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::SetMinus(a, b) => format!(
                "{}.difference(&{})",
                self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&b.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Powerset(s) => format!(
                "powerset(&{})",
                self.expr_to_rust_with_scope(&s.node, prefix_state, state_ref, prime_state_ref)
            ),

            // Tuples
            Expr::Tuple(elems) => {
                let elem_strs: Vec<_> = elems
                    .iter()
                    .map(|e| {
                        self.expr_to_rust_with_scope(
                            &e.node,
                            prefix_state,
                            state_ref,
                            prime_state_ref,
                        )
                    })
                    .collect();
                format!("({})", elem_strs.join(", "))
            }

            // Functions
            Expr::FuncApply(func, arg) => format!(
                "{}.apply(&{}).cloned().expect(\"function application requires key in domain\")",
                self.expr_to_rust_with_scope(&func.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(&arg.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::Domain(func) => format!(
                "{}.domain()",
                self.expr_to_rust_with_scope(&func.node, prefix_state, state_ref, prime_state_ref)
            ),
            Expr::FuncDef(bounds, body) => {
                self.emit_func_def_expr(bounds, body, prefix_state, state_ref, prime_state_ref)
            }
            Expr::FuncSet(domain, range) => {
                self.emit_func_set_expr(domain, range, prefix_state, state_ref, prime_state_ref)
            }

            // Records
            Expr::Record(fields) => {
                // [a |-> 1, b |-> 2] translates to TlaRecord::from_fields([...])
                let field_strs: Vec<_> = fields
                    .iter()
                    .map(|(k, v)| {
                        format!(
                            "(\"{}\".to_string(), {})",
                            k.node,
                            self.expr_to_rust_with_scope(
                                &v.node,
                                prefix_state,
                                state_ref,
                                prime_state_ref,
                            )
                        )
                    })
                    .collect();
                format!("TlaRecord::from_fields([{}])", field_strs.join(", "))
            }
            Expr::RecordAccess(rec, field) => {
                format!(
                    "{}.get(\"{}\").cloned().expect(\"record access requires existing field\")",
                    self.expr_to_rust_with_scope(
                        &rec.node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    ),
                    field.name.node
                )
            }
            Expr::RecordSet(fields) => {
                // [a: S, b: T] is a set of records - Cartesian product of field values
                // For small field sets, enumerate all combinations
                if fields.is_empty() {
                    "tla_set![TlaRecord::new()]".to_string()
                } else {
                    // Generate nested loops for Cartesian product
                    let mut result = String::new();
                    result.push_str("{\n");
                    result.push_str("    let mut __records = TlaSet::new();\n");

                    // Generate nested for loops
                    let field_names: Vec<_> = fields.iter().map(|(k, _)| k.node.clone()).collect();
                    for (i, (_, v)) in fields.iter().enumerate() {
                        let var_name = format!("__f{}", i);
                        result.push_str(&format!(
                            "    for {} in {} {{\n",
                            var_name,
                            self.expr_to_rust_with_scope(
                                &v.node,
                                prefix_state,
                                state_ref,
                                prime_state_ref,
                            )
                        ));
                    }

                    // Build the record
                    result.push_str("    __records.insert(TlaRecord::from_fields([");
                    for (i, name) in field_names.iter().enumerate() {
                        if i > 0 {
                            result.push_str(", ");
                        }
                        result.push_str(&format!("(\"{}\".to_string(), __f{}.clone())", name, i));
                    }
                    result.push_str("]));\n");

                    // Close the loops
                    for _ in fields {
                        result.push_str("    }\n");
                    }

                    result.push_str("    __records\n}");
                    result
                }
            }

            // Control
            Expr::If(cond, then_e, else_e) => format!(
                "if {} {{ {} }} else {{ {} }}",
                self.expr_to_rust_with_scope(&cond.node, prefix_state, state_ref, prime_state_ref),
                self.expr_to_rust_with_scope(
                    &then_e.node,
                    prefix_state,
                    state_ref,
                    prime_state_ref,
                ),
                self.expr_to_rust_with_scope(
                    &else_e.node,
                    prefix_state,
                    state_ref,
                    prime_state_ref,
                )
            ),

            // Prime (for Next actions)
            Expr::Prime(inner) => {
                if let Expr::Ident(name, _) = &inner.node {
                    if let Some(prime_state_ref) = prime_state_ref {
                        format!("{prime_state_ref}.{}.clone()", to_snake_case(name))
                    } else {
                        format!("{}_next", to_snake_case(name))
                    }
                } else {
                    format!(
                        "/* {}' */",
                        self.expr_to_rust_with_scope(
                            &inner.node,
                            prefix_state,
                            state_ref,
                            prime_state_ref,
                        )
                    )
                }
            }

            // Function application - handle stdlib operators
            Expr::Apply(op_expr, args) => {
                if let Expr::Ident(name, _) = &op_expr.node {
                    self.translate_stdlib_apply(
                        name,
                        args,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    )
                } else {
                    // Operator expression isn't an identifier, try translating as function call
                    let op_str = self.expr_to_rust_with_scope(
                        &op_expr.node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    let args_str: Vec<_> = args
                        .iter()
                        .map(|a| {
                            self.expr_to_rust_with_scope(
                                &a.node,
                                prefix_state,
                                state_ref,
                                prime_state_ref,
                            )
                        })
                        .collect();
                    format!("{}({})", op_str, args_str.join(", "))
                }
            }

            // EXCEPT - function update [f EXCEPT ![a] = b]
            Expr::Except(func, specs) => {
                self.emit_except_expr(func, specs, prefix_state, state_ref, prime_state_ref)
            }

            // Quantifiers
            Expr::Forall(bounds, body) => {
                self.emit_forall_expr(bounds, body, prefix_state, state_ref, prime_state_ref)
            }
            Expr::Exists(bounds, body) => {
                self.emit_exists_expr(bounds, body, prefix_state, state_ref, prime_state_ref)
            }
            Expr::Choose(bound, pred) => {
                self.emit_choose_expr(bound, pred, prefix_state, state_ref, prime_state_ref)
            }

            // Set comprehensions
            Expr::SetBuilder(body, bounds) => {
                self.emit_set_builder_expr(body, bounds, prefix_state, state_ref, prime_state_ref)
            }
            Expr::SetFilter(bound, pred) => {
                self.emit_set_filter_expr(bound, pred, prefix_state, state_ref, prime_state_ref)
            }

            // LET x == e1 IN e2 -> { let x = e1; e2 }
            Expr::Let(defs, body) => {
                let mut result = "{\n".to_string();
                for def in defs {
                    let name = to_snake_case(&def.name.node);
                    if def.params.is_empty() {
                        // Simple let binding
                        let val_str = self.expr_to_rust_with_scope(
                            &def.body.node,
                            prefix_state,
                            state_ref,
                            prime_state_ref,
                        );
                        result.push_str(&format!("    let {} = {};\n", name, val_str));
                    } else {
                        // Function definition in LET
                        let params: Vec<_> = def
                            .params
                            .iter()
                            .map(|p| format!("{}: _", to_snake_case(&p.name.node)))
                            .collect();
                        let body_str = self.expr_to_rust_with_scope(
                            &def.body.node,
                            prefix_state,
                            state_ref,
                            prime_state_ref,
                        );
                        result.push_str(&format!(
                            "    let {} = |{}| {};\n",
                            name,
                            params.join(", "),
                            body_str
                        ));
                    }
                }
                let body_str = self.expr_to_rust_with_scope(
                    &body.node,
                    prefix_state,
                    state_ref,
                    prime_state_ref,
                );
                result.push_str(&format!("    {}\n}}", body_str));
                result
            }

            // CASE arm1 [] arm2 [] OTHER -> expr
            // -> if cond1 { e1 } else if cond2 { e2 } else { default }
            Expr::Case(arms, other) => {
                let mut result = String::new();
                for (i, arm) in arms.iter().enumerate() {
                    let cond_str = self.expr_to_rust_with_scope(
                        &arm.guard.node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    let body_str = self.expr_to_rust_with_scope(
                        &arm.body.node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    if i == 0 {
                        result.push_str(&format!("if {} {{ {} }}", cond_str, body_str));
                    } else {
                        result.push_str(&format!(" else if {} {{ {} }}", cond_str, body_str));
                    }
                }
                if let Some(default) = other {
                    let default_str = self.expr_to_rust_with_scope(
                        &default.node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    result.push_str(&format!(" else {{ {} }}", default_str));
                } else {
                    result.push_str(" else { panic!(\"CASE: no matching arm\") }");
                }
                result
            }

            // Cartesian product: S \\X T -> cross product enumeration
            Expr::Times(sets) => {
                if sets.len() == 2 {
                    let left_str = self.expr_to_rust_with_scope(
                        &sets[0].node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    let right_str = self.expr_to_rust_with_scope(
                        &sets[1].node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    format!(
                        "TlaSet::from_iter({}.iter().flat_map(|__a| {}.iter().map(move |__b| (__a.clone(), __b.clone()))))",
                        left_str, right_str
                    )
                } else {
                    // For more than 2 sets, nest the products
                    let first_str = self.expr_to_rust_with_scope(
                        &sets[0].node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    let mut result = first_str;
                    for (i, set) in sets.iter().enumerate().skip(1) {
                        let set_str = self.expr_to_rust_with_scope(
                            &set.node,
                            prefix_state,
                            state_ref,
                            prime_state_ref,
                        );
                        result = format!(
                            "TlaSet::from_iter({}.iter().flat_map(|__a{}| {}.iter().map(move |__b{}| (__a{}.clone(), __b{}.clone()))))",
                            result, i, set_str, i, i, i
                        );
                    }
                    result
                }
            }

            // BigUnion: UNION S -> flatten a set of sets
            Expr::BigUnion(s) => {
                format!(
                    "TlaSet::from_iter({}.iter().flat_map(|__s| __s.iter().cloned()))",
                    self.expr_to_rust_with_scope(&s.node, prefix_state, state_ref, prime_state_ref)
                )
            }

            // Lambda: LAMBDA x, y : body -> closure
            Expr::Lambda(params, body) => {
                let param_strs: Vec<_> = params
                    .iter()
                    .map(|p| format!("{}: _", to_snake_case(&p.node)))
                    .collect();
                let body_str = self.expr_to_rust_with_scope(
                    &body.node,
                    prefix_state,
                    state_ref,
                    prime_state_ref,
                );
                format!("|{}| {}", param_strs.join(", "), body_str)
            }

            // SubstIn is a transparent wrapper after codegen-time INSTANCE expansion.
            Expr::SubstIn(_, body) => {
                self.expr_to_rust_with_scope(&body.node, prefix_state, state_ref, prime_state_ref)
            }

            // These should have been eliminated during preprocessing/expansion.
            Expr::ModuleRef(_, _, _) => "/* unsupported module reference */".to_string(),
            Expr::InstanceExpr(_, _) => "/* unsupported instance expression */".to_string(),

            // Default - generate a placeholder
            _ => format!("/* unsupported: {:?} */", std::mem::discriminant(expr)),
        }
    }
}
