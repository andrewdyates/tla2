// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! EXCEPT expression helpers for the Rust emitter.

use super::*;
use tla_core::{ExprFold, SubstituteAt};

impl<'a> RustEmitter<'a> {
    /// Emit EXCEPT expression: [f EXCEPT ![a] = b]
    pub(super) fn emit_except_expr(
        &self,
        func: &Spanned<Expr>,
        specs: &[tla_core::ast::ExceptSpec],
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        let func_str =
            self.expr_to_rust_with_scope(&func.node, prefix_state, state_ref, prime_state_ref);
        let mut result = format!("{{\n    let mut __tmp = {}.clone();\n", func_str);
        for spec in specs {
            if spec.path.len() == 1 {
                if let ExceptPathElement::Index(idx) = &spec.path[0] {
                    let key_str = self.expr_to_rust_with_scope(
                        &idx.node,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    let val_str = self.emit_except_value_expr(
                        func,
                        spec,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    result.push_str(&format!("    __tmp.update({}, {});\n", key_str, val_str));
                } else if let ExceptPathElement::Field(f) = &spec.path[0] {
                    let val_str = self.emit_except_value_expr(
                        func,
                        spec,
                        prefix_state,
                        state_ref,
                        prime_state_ref,
                    );
                    result.push_str(&format!(
                        "    __tmp.set(\"{}\", {});\n",
                        f.name.node, val_str
                    ));
                }
            } else {
                self.emit_except_nested_path(
                    &mut result,
                    func,
                    spec,
                    prefix_state,
                    state_ref,
                    prime_state_ref,
                );
            }
        }
        result.push_str("    __tmp\n}");
        result
    }

    /// Emit nested EXCEPT path: [f EXCEPT ![a][b] = v]
    fn emit_except_nested_path(
        &self,
        result: &mut String,
        func: &Spanned<Expr>,
        spec: &tla_core::ast::ExceptSpec,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) {
        let val_str =
            self.emit_except_value_expr(func, spec, prefix_state, state_ref, prime_state_ref);
        let n = spec.path.len();

        #[derive(Clone)]
        enum PathElem {
            Index(String),
            Field(String),
        }

        let path_elems: Vec<PathElem> = spec
            .path
            .iter()
            .map(|elem| match elem {
                ExceptPathElement::Index(idx) => PathElem::Index(self.expr_to_rust_with_scope(
                    &idx.node,
                    prefix_state,
                    state_ref,
                    prime_state_ref,
                )),
                ExceptPathElement::Field(f) => PathElem::Field(f.name.node.clone()),
            })
            .collect();

        for (i, elem) in path_elems.iter().enumerate() {
            if let PathElem::Index(idx_str) = elem {
                result.push_str(&format!("    let __key_{} = {};\n", i, idx_str));
            }
        }

        for (i, elem) in path_elems.iter().enumerate().take(n - 1) {
            let prev = if i == 0 {
                "__tmp".to_string()
            } else {
                format!("__inner_{}", i - 1)
            };
            let accessor = match elem {
                PathElem::Index(_) => {
                    format!(
                        "{}.apply(&__key_{}).cloned().expect(\"EXCEPT index path requires key in domain\")",
                        prev, i
                    )
                }
                PathElem::Field(f) => {
                    format!(
                        "{}.get(\"{}\").cloned().expect(\"EXCEPT field path requires existing field\")",
                        prev, f
                    )
                }
            };
            result.push_str(&format!("    let __inner_{} = {};\n", i, accessor));
        }

        let inner_idx = n - 2;
        let update_code = match &path_elems[n - 1] {
            PathElem::Index(_) => {
                format!(
                    "{{ let mut __t = __inner_{}; __t.update(__key_{}, {}); __t }}",
                    inner_idx,
                    n - 1,
                    val_str
                )
            }
            PathElem::Field(f) => {
                format!(
                    "{{ let mut __t = __inner_{}; __t.set(\"{}\", {}); __t }}",
                    inner_idx, f, val_str
                )
            }
        };
        result.push_str(&format!(
            "    let __inner_{} = {};\n",
            inner_idx, update_code
        ));

        for i in (0..inner_idx).rev() {
            let update_code = match &path_elems[i + 1] {
                PathElem::Index(_) => {
                    format!(
                        "{{ let mut __t = __inner_{}; __t.update(__key_{}, __inner_{}); __t }}",
                        i,
                        i + 1,
                        i + 1
                    )
                }
                PathElem::Field(f) => {
                    format!(
                        "{{ let mut __t = __inner_{}; __t.set(\"{}\", __inner_{}); __t }}",
                        i,
                        f,
                        i + 1
                    )
                }
            };
            result.push_str(&format!("    let __inner_{} = {};\n", i, update_code));
        }

        let final_update = match &path_elems[0] {
            PathElem::Index(_) => "    __tmp.update(__key_0, __inner_0);\n".to_string(),
            PathElem::Field(f) => format!("    __tmp.set(\"{}\", __inner_0);\n", f),
        };
        result.push_str(&final_update);
    }

    fn emit_except_value_expr(
        &self,
        func: &Spanned<Expr>,
        spec: &tla_core::ast::ExceptSpec,
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        let replacement = self.except_path_expr(func, &spec.path);
        let mut substitute_at = SubstituteAt {
            replacement: &replacement,
        };
        let value = substitute_at.fold_expr(spec.value.clone());
        self.expr_to_rust_with_scope(&value.node, prefix_state, state_ref, prime_state_ref)
    }

    fn except_path_expr(&self, func: &Spanned<Expr>, path: &[ExceptPathElement]) -> Spanned<Expr> {
        let mut current = func.clone();
        for elem in path {
            current = match elem {
                ExceptPathElement::Index(idx) => {
                    Spanned::dummy(Expr::FuncApply(Box::new(current), Box::new(idx.clone())))
                }
                ExceptPathElement::Field(field) => {
                    Spanned::dummy(Expr::RecordAccess(Box::new(current), field.clone()))
                }
            };
        }
        current
    }
}
