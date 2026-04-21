// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier, set-builder, and function-builder helpers for the Rust emitter.

use super::*;

impl<'a> RustEmitter<'a> {
    /// Emit \A quantifier expression
    pub(super) fn emit_forall_expr(
        &self,
        bounds: &[tla_core::ast::BoundVar],
        body: &Spanned<Expr>,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        self.emit_bounded_quantifier(
            bounds,
            body,
            "all",
            prefix_state,
            state_ref,
            prime_state_ref,
        )
    }

    /// Emit \E quantifier expression
    pub(super) fn emit_exists_expr(
        &self,
        bounds: &[tla_core::ast::BoundVar],
        body: &Spanned<Expr>,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        self.emit_bounded_quantifier(
            bounds,
            body,
            "any",
            prefix_state,
            state_ref,
            prime_state_ref,
        )
    }

    /// Shared logic for \A (all) and \E (any) quantifiers
    fn emit_bounded_quantifier(
        &self,
        bounds: &[tla_core::ast::BoundVar],
        body: &Spanned<Expr>,
        method: &str,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        if bounds.len() == 1 {
            let bound = &bounds[0];
            let var_name = to_snake_case(&bound.name.node);
            let domain_str = bound
                .domain
                .as_ref()
                .map(|s| {
                    self.expr_to_rust_with_scope(&s.node, prefix_state, state_ref, prime_state_ref)
                })
                .unwrap_or_else(|| "/* no domain */".to_string());
            let body_str =
                self.expr_to_rust_with_scope(&body.node, prefix_state, state_ref, prime_state_ref);
            format!(
                "{}.iter().{}(|{}| {})",
                domain_str, method, var_name, body_str
            )
        } else {
            let mut result = String::new();
            for bound in bounds {
                let var_name = to_snake_case(&bound.name.node);
                let domain_str = bound
                    .domain
                    .as_ref()
                    .map(|s| {
                        self.expr_to_rust_with_scope(
                            &s.node,
                            prefix_state,
                            state_ref,
                            prime_state_ref,
                        )
                    })
                    .unwrap_or_else(|| "/* no domain */".to_string());
                result.push_str(&format!("{}.iter().{}(|{}| ", domain_str, method, var_name));
            }
            result.push_str(&self.expr_to_rust_with_scope(
                &body.node,
                prefix_state,
                state_ref,
                prime_state_ref,
            ));
            for _ in bounds {
                result.push(')');
            }
            result
        }
    }

    /// Emit CHOOSE expression
    pub(super) fn emit_choose_expr(
        &self,
        bound: &tla_core::ast::BoundVar,
        pred: &Spanned<Expr>,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        let var_name = to_snake_case(&bound.name.node);
        let domain_str = bound
            .domain
            .as_ref()
            .map(|s| {
                self.expr_to_rust_with_scope(&s.node, prefix_state, state_ref, prime_state_ref)
            })
            .unwrap_or_else(|| "/* no domain */".to_string());
        let pred_str =
            self.expr_to_rust_with_scope(&pred.node, prefix_state, state_ref, prime_state_ref);
        format!(
            "{}.iter().find(|{}| {}).cloned().expect(\"CHOOSE: no element satisfies predicate\")",
            domain_str, var_name, pred_str
        )
    }

    /// Emit set builder expression: {expr : x \in S}
    pub(super) fn emit_set_builder_expr(
        &self,
        body: &Spanned<Expr>,
        bounds: &[tla_core::ast::BoundVar],
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        if bounds.len() == 1 {
            let bound = &bounds[0];
            let var_name = to_snake_case(&bound.name.node);
            let domain_str = bound
                .domain
                .as_ref()
                .map(|s| {
                    self.expr_to_rust_with_scope(&s.node, prefix_state, state_ref, prime_state_ref)
                })
                .unwrap_or_else(|| "/* no domain */".to_string());
            let body_str =
                self.expr_to_rust_with_scope(&body.node, prefix_state, state_ref, prime_state_ref);
            format!(
                "TlaSet::from_iter({}.iter().map(|{}| {}))",
                domain_str, var_name, body_str
            )
        } else {
            let mut iter_chain = String::new();
            for (i, bound) in bounds.iter().enumerate() {
                let var_name = to_snake_case(&bound.name.node);
                let domain_str = bound
                    .domain
                    .as_ref()
                    .map(|s| {
                        self.expr_to_rust_with_scope(
                            &s.node,
                            prefix_state,
                            state_ref,
                            prime_state_ref,
                        )
                    })
                    .unwrap_or_else(|| "/* no domain */".to_string());
                if i == bounds.len() - 1 {
                    iter_chain.push_str(&format!("{}.iter().map(|{}| ", domain_str, var_name));
                } else {
                    iter_chain.push_str(&format!("{}.iter().flat_map(|{}| ", domain_str, var_name));
                }
            }
            let body_str =
                self.expr_to_rust_with_scope(&body.node, prefix_state, state_ref, prime_state_ref);
            iter_chain.push_str(&body_str);
            for _ in bounds {
                iter_chain.push(')');
            }
            format!("TlaSet::from_iter({})", iter_chain)
        }
    }

    /// Emit set filter expression: {x \in S : P(x)}
    pub(super) fn emit_set_filter_expr(
        &self,
        bound: &tla_core::ast::BoundVar,
        pred: &Spanned<Expr>,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        let var_name = to_snake_case(&bound.name.node);
        let domain_str = bound
            .domain
            .as_ref()
            .map(|s| {
                self.expr_to_rust_with_scope(&s.node, prefix_state, state_ref, prime_state_ref)
            })
            .unwrap_or_else(|| "/* no domain */".to_string());
        let pred_str =
            self.expr_to_rust_with_scope(&pred.node, prefix_state, state_ref, prime_state_ref);
        format!(
            "TlaSet::from_iter({}.iter().filter(|{}| {}).cloned())",
            domain_str, var_name, pred_str
        )
    }

    /// Emit function definition: [x \in S |-> expr]
    pub(super) fn emit_func_def_expr(
        &self,
        bounds: &[tla_core::ast::BoundVar],
        body: &Spanned<Expr>,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        if bounds.len() == 1 {
            let bound = &bounds[0];
            let var_name = to_snake_case(&bound.name.node);
            let domain_str = bound
                .domain
                .as_ref()
                .map(|s| {
                    self.expr_to_rust_with_scope(&s.node, prefix_state, state_ref, prime_state_ref)
                })
                .unwrap_or_else(|| "/* no domain */".to_string());
            let body_str =
                self.expr_to_rust_with_scope(&body.node, prefix_state, state_ref, prime_state_ref);
            format!(
                "TlaFunc::from_iter({}.iter().map(|{}| ({}.clone(), {})))",
                domain_str, var_name, var_name, body_str
            )
        } else {
            let body_str =
                self.expr_to_rust_with_scope(&body.node, prefix_state, state_ref, prime_state_ref);
            let var_names: Vec<_> = bounds.iter().map(|b| to_snake_case(&b.name.node)).collect();
            let domain_strs: Vec<_> = bounds
                .iter()
                .map(|b| {
                    b.domain
                        .as_ref()
                        .map(|d| {
                            self.expr_to_rust_with_scope(
                                &d.node,
                                prefix_state,
                                state_ref,
                                prime_state_ref,
                            )
                        })
                        .unwrap_or_else(|| "/* no domain */".to_string())
                })
                .collect();

            let key_tuple = format!(
                "({})",
                var_names
                    .iter()
                    .map(|v| format!("{}.clone()", v))
                    .collect::<Vec<_>>()
                    .join(", ")
            );

            let n = bounds.len();
            let mut result = format!(
                "{}.iter().map(|{}| ({}, {}))",
                domain_strs[n - 1],
                var_names[n - 1],
                key_tuple,
                body_str
            );

            for i in (0..n - 1).rev() {
                result = format!(
                    "{}.iter().flat_map(|{}| {})",
                    domain_strs[i], var_names[i], result
                );
            }

            format!("TlaFunc::from_iter({})", result)
        }
    }

    /// Emit function set expression: [S -> T]
    pub(super) fn emit_func_set_expr(
        &self,
        domain: &Spanned<Expr>,
        range: &Spanned<Expr>,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        let domain_str =
            self.expr_to_rust_with_scope(&domain.node, prefix_state, state_ref, prime_state_ref);
        let range_str =
            self.expr_to_rust_with_scope(&range.node, prefix_state, state_ref, prime_state_ref);
        format!(
            r#"{{
    let __domain: Vec<_> = ({}).iter().cloned().collect();
    let __range: Vec<_> = ({}).iter().cloned().collect();
    let __dom_len = __domain.len();
    let __range_len = __range.len();
    if __dom_len > 10 || __range_len.checked_pow(__dom_len as u32).map_or(true, |n| n > 10000) {{
        panic!("FuncSet [{{}}->{{}}) too large: domain_size={{}}, range_size={{}}", __dom_len, __range_len, __dom_len, __range_len);
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
}}"#,
            domain_str, range_str
        )
    }
}
