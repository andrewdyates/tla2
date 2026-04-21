// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CHC expression lowering via `TranslateExpr` trait.
//!
//! Beyond the shared bool/int dispatcher hooks, CHC needs custom lowering for
//! function-valued state, finite quantifiers, set membership, and string/model
//! values represented as interned integers.

use std::collections::HashMap;
use std::sync::Arc;

use tla_core::ast::{BoundVar, ExceptPathElement, Expr, RecordFieldName};
use tla_core::{dispatch_translate_bool, dispatch_translate_int, ExprFold, SpanPolicy, Spanned};
use tla_core::{SubstituteExpr, TranslateExpr};
use z4_chc::{ChcExpr, ChcOp, ChcVar};

use super::support::{
    and_all, expr_to_domain_key, extract_finite_domain_keys, key_to_ast_expr, or_all,
};
use super::ChcTranslator;
use crate::error::{Z4Error, Z4Result};
use crate::TlaSort;

#[derive(Clone)]
struct ChcFunctionValue {
    domain_keys: Vec<String>,
    range_sort: TlaSort,
    elements: HashMap<String, ChcExpr>,
}

#[derive(Clone)]
struct ChcRecordValue {
    field_sorts: Vec<(String, TlaSort)>,
    fields: HashMap<String, ChcExpr>,
}

#[derive(Clone)]
enum ChcValue {
    Scalar { expr: ChcExpr, sort: TlaSort },
    Function(ChcFunctionValue),
    Record(ChcRecordValue),
}

impl ChcTranslator {
    fn intern_tagged_atom(&mut self, tag: &str, value: &str) -> Z4Result<i64> {
        let key = format!("{tag}:{value}");
        if let Some(id) = self.atom_intern.get(&key) {
            return Ok(*id);
        }

        let next_id = i64::try_from(self.atom_intern.len() + 1)
            .map_err(|_| Z4Error::IntegerOverflow("too many interned CHC atoms".to_string()))?;
        self.atom_intern.insert(key, next_id);
        Ok(next_id)
    }

    fn scalar_var_expr(&self, var: &ChcVar) -> ChcExpr {
        ChcExpr::var(var.clone())
    }

    fn lookup_declared_value(&self, name: &str) -> Z4Result<ChcValue> {
        let sort = self
            .var_sorts
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(name.to_string()))?
            .clone();

        match sort.clone() {
            TlaSort::Bool | TlaSort::Int | TlaSort::String => {
                let vars = if self.use_primed_vars {
                    &self.next_vars
                } else {
                    &self.vars
                };
                let var = vars
                    .get(name)
                    .ok_or_else(|| Z4Error::UnknownVariable(name.to_string()))?;
                Ok(ChcValue::Scalar {
                    expr: self.scalar_var_expr(var),
                    sort,
                })
            }
            TlaSort::Function { .. } => {
                let info = self
                    .func_vars
                    .get(name)
                    .ok_or_else(|| Z4Error::UnknownVariable(name.to_string()))?;
                let vars = if self.use_primed_vars {
                    &info.element_next_vars
                } else {
                    &info.element_vars
                };

                let mut elements = HashMap::new();
                for key in &info.domain_keys {
                    let var = vars
                        .get(key)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("{name}[{key}]")))?;
                    elements.insert(key.clone(), self.scalar_var_expr(var));
                }

                Ok(ChcValue::Function(ChcFunctionValue {
                    domain_keys: info.domain_keys.clone(),
                    range_sort: info.range_sort.clone(),
                    elements,
                }))
            }
            TlaSort::Record { .. } => {
                let info = self
                    .record_vars
                    .get(name)
                    .ok_or_else(|| Z4Error::UnknownVariable(name.to_string()))?;
                let vars = if self.use_primed_vars {
                    &info.field_next_vars
                } else {
                    &info.field_vars
                };

                let mut fields = HashMap::new();
                for (field_name, _) in &info.field_sorts {
                    let var = vars
                        .get(field_name)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("{name}.{field_name}")))?;
                    fields.insert(field_name.clone(), self.scalar_var_expr(var));
                }

                Ok(ChcValue::Record(ChcRecordValue {
                    field_sorts: info.field_sorts.clone(),
                    fields,
                }))
            }
            TlaSort::Tuple { .. } => Err(Z4Error::UnsupportedOp(
                "tuple-valued CHC state is not supported".to_string(),
            )),
            TlaSort::Set { .. } => Err(Z4Error::UnsupportedOp(
                "set-valued CHC state is not yet supported".to_string(),
            )),
            TlaSort::Sequence { .. } => Err(Z4Error::UnsupportedOp(
                "sequence-valued CHC state is not yet supported".to_string(),
            )),
        }
    }

    fn scalar_eq(
        &self,
        left_expr: ChcExpr,
        left_sort: &TlaSort,
        right_expr: ChcExpr,
        right_sort: &TlaSort,
    ) -> ChcExpr {
        if left_sort == right_sort {
            ChcExpr::eq(left_expr, right_expr)
        } else {
            ChcExpr::Bool(false)
        }
    }

    /// Inline-substitute all zero-parameter LET definitions, returning the
    /// body with every `name` occurrence replaced by its definition.
    fn inline_let_defs(
        &self,
        defs: &[tla_core::ast::OperatorDef],
        body: &Spanned<Expr>,
    ) -> Z4Result<Spanned<Expr>> {
        let mut result = body.clone();
        for def in defs {
            if !def.params.is_empty() {
                return Err(Z4Error::UnsupportedOp(
                    "CHC LET does not support parameterized operator definitions".to_string(),
                ));
            }
            result = self.substitute_expr(&result, &def.name.node, &def.body);
        }
        Ok(result)
    }

    fn translate_value(&mut self, expr: &Spanned<Expr>) -> Z4Result<ChcValue> {
        match &expr.node {
            Expr::Label(label) => self.translate_value(&label.body),
            Expr::Let(defs, body) => {
                let inlined = self.inline_let_defs(defs, body)?;
                self.translate_value(&inlined)
            }
            Expr::Prime(inner) => {
                if !self.allow_primed {
                    return Err(Z4Error::UntranslatableExpr(
                        "primed variables not allowed in Init/Safety".to_string(),
                    ));
                }
                let old = self.use_primed_vars;
                self.use_primed_vars = true;
                let result = self.translate_value(inner);
                self.use_primed_vars = old;
                result
            }
            Expr::Bool(b) => Ok(ChcValue::Scalar {
                expr: ChcExpr::Bool(*b),
                sort: TlaSort::Bool,
            }),
            Expr::Int(n) => {
                let val: i64 = n
                    .try_into()
                    .map_err(|_| Z4Error::IntegerOverflow(format!("integer {n} too large")))?;
                Ok(ChcValue::Scalar {
                    expr: ChcExpr::Int(val),
                    sort: TlaSort::Int,
                })
            }
            Expr::String(s) => Ok(ChcValue::Scalar {
                expr: ChcExpr::Int(self.intern_tagged_atom("str", s)?),
                sort: TlaSort::String,
            }),
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                if self.var_sorts.contains_key(name) {
                    self.lookup_declared_value(name)
                } else {
                    Ok(ChcValue::Scalar {
                        expr: ChcExpr::Int(self.intern_tagged_atom("id", name)?),
                        sort: TlaSort::String,
                    })
                }
            }
            Expr::If(cond, then_branch, else_branch) => {
                let cond = dispatch_translate_bool(self, cond)?;
                let then_val = self.translate_value(then_branch)?;
                let else_val = self.translate_value(else_branch)?;
                self.merge_ite_values(cond, then_val, else_val)
            }
            Expr::Record(fields) => self.translate_record_expr(fields),
            Expr::RecordAccess(base, field) => self.translate_record_access_value(base, field),
            Expr::FuncApply(func, arg) => self.translate_func_apply_value(func, arg),
            Expr::FuncDef(bounds, body) => self.translate_function_expr(bounds, body),
            Expr::Except(base, specs) => self.translate_except_expr(base, specs),
            _ => {
                // Try Int before Bool: translate_bool_extended redirects arithmetic
                // (Add/Sub/etc.) through dispatch_translate_int, which would cause
                // the result to be misclassified as TlaSort::Bool if we tried Bool first.
                if let Ok(int_expr) = dispatch_translate_int(self, expr) {
                    return Ok(ChcValue::Scalar {
                        expr: int_expr,
                        sort: TlaSort::Int,
                    });
                }
                if let Ok(bool_expr) = dispatch_translate_bool(self, expr) {
                    return Ok(ChcValue::Scalar {
                        expr: bool_expr,
                        sort: TlaSort::Bool,
                    });
                }
                Err(Z4Error::UntranslatableExpr(format!(
                    "unsupported CHC value expression: {:?}",
                    expr.node
                )))
            }
        }
    }

    fn merge_ite_values(
        &self,
        cond: ChcExpr,
        then_val: ChcValue,
        else_val: ChcValue,
    ) -> Z4Result<ChcValue> {
        match (then_val, else_val) {
            (
                ChcValue::Scalar {
                    expr: then_expr,
                    sort: then_sort,
                },
                ChcValue::Scalar {
                    expr: else_expr,
                    sort: else_sort,
                },
            ) => {
                if then_sort != else_sort {
                    return Err(Z4Error::TypeMismatch {
                        name: "ITE".to_string(),
                        expected: format!("{then_sort}"),
                        actual: format!("{else_sort}"),
                    });
                }
                Ok(ChcValue::Scalar {
                    expr: ChcExpr::ite(cond, then_expr, else_expr),
                    sort: then_sort,
                })
            }
            (ChcValue::Function(then_fun), ChcValue::Function(else_fun)) => {
                if then_fun.domain_keys != else_fun.domain_keys
                    || then_fun.range_sort != else_fun.range_sort
                {
                    return Err(Z4Error::TypeMismatch {
                        name: "ITE".to_string(),
                        expected: format!(
                            "[{:?} -> {}]",
                            then_fun.domain_keys, then_fun.range_sort
                        ),
                        actual: format!("[{:?} -> {}]", else_fun.domain_keys, else_fun.range_sort),
                    });
                }

                let mut elements = HashMap::new();
                for key in &then_fun.domain_keys {
                    let then_elem = then_fun
                        .elements
                        .get(key)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("ITE[{key}]")))?;
                    let else_elem = else_fun
                        .elements
                        .get(key)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("ITE[{key}]")))?;
                    elements.insert(
                        key.clone(),
                        ChcExpr::ite(cond.clone(), then_elem.clone(), else_elem.clone()),
                    );
                }

                Ok(ChcValue::Function(ChcFunctionValue {
                    domain_keys: then_fun.domain_keys,
                    range_sort: then_fun.range_sort,
                    elements,
                }))
            }
            (ChcValue::Record(then_record), ChcValue::Record(else_record)) => {
                if then_record.field_sorts != else_record.field_sorts {
                    return Err(Z4Error::TypeMismatch {
                        name: "ITE".to_string(),
                        expected: format!(
                            "{}",
                            TlaSort::Record {
                                field_sorts: then_record.field_sorts.clone(),
                            }
                        ),
                        actual: format!(
                            "{}",
                            TlaSort::Record {
                                field_sorts: else_record.field_sorts.clone(),
                            }
                        ),
                    });
                }

                let mut fields = HashMap::new();
                for (field_name, _) in &then_record.field_sorts {
                    let then_field = then_record
                        .fields
                        .get(field_name)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("ITE.{field_name}")))?;
                    let else_field = else_record
                        .fields
                        .get(field_name)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("ITE.{field_name}")))?;
                    fields.insert(
                        field_name.clone(),
                        ChcExpr::ite(cond.clone(), then_field.clone(), else_field.clone()),
                    );
                }

                Ok(ChcValue::Record(ChcRecordValue {
                    field_sorts: then_record.field_sorts,
                    fields,
                }))
            }
            _ => Err(Z4Error::TypeMismatch {
                name: "ITE".to_string(),
                expected: "matching then/else shapes".to_string(),
                actual: "mismatched scalar/function/record branches".to_string(),
            }),
        }
    }

    fn try_expr_to_key(&self, expr: &Spanned<Expr>) -> Option<String> {
        expr_to_domain_key(expr)
    }

    fn translate_func_apply_value(
        &mut self,
        func: &Spanned<Expr>,
        arg: &Spanned<Expr>,
    ) -> Z4Result<ChcValue> {
        let func_val = self.translate_value(func)?;
        let ChcValue::Function(func_val) = func_val else {
            return Err(Z4Error::UnsupportedOp(
                "function application requires a function-valued expression".to_string(),
            ));
        };

        if func_val.domain_keys.is_empty() {
            return Err(Z4Error::UnsupportedOp(
                "function application on empty domain".to_string(),
            ));
        }

        if let Some(key) = self.try_expr_to_key(arg) {
            let elem = func_val
                .elements
                .get(&key)
                .ok_or_else(|| Z4Error::UnknownVariable(format!("f[{key}]")))?;
            return Ok(ChcValue::Scalar {
                expr: elem.clone(),
                sort: func_val.range_sort,
            });
        }

        let arg_val = self.translate_value(arg)?;
        let ChcValue::Scalar {
            expr: arg_expr,
            sort,
        } = arg_val
        else {
            return Err(Z4Error::UnsupportedOp(
                "function application index must be scalar".to_string(),
            ));
        };

        let mut keys = func_val.domain_keys.iter().rev();
        let last_key = keys.next().ok_or_else(|| {
            Z4Error::UnsupportedOp("function application on empty domain".to_string())
        })?;
        let mut result = func_val
            .elements
            .get(last_key)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("f[{last_key}]")))?
            .clone();

        for key in keys {
            let key_value = self.translate_value(&key_to_ast_expr(key))?;
            let ChcValue::Scalar {
                expr: key_expr,
                sort: key_sort,
            } = key_value
            else {
                return Err(Z4Error::UnsupportedOp(
                    "function domain keys must be scalar".to_string(),
                ));
            };

            let cond = self.scalar_eq(arg_expr.clone(), &sort, key_expr, &key_sort);
            let elem = func_val
                .elements
                .get(key)
                .ok_or_else(|| Z4Error::UnknownVariable(format!("f[{key}]")))?
                .clone();
            result = ChcExpr::ite(cond, elem, result);
        }

        Ok(ChcValue::Scalar {
            expr: result,
            sort: func_val.range_sort,
        })
    }

    fn translate_function_expr(
        &mut self,
        bounds: &[BoundVar],
        body: &Spanned<Expr>,
    ) -> Z4Result<ChcValue> {
        if bounds.len() != 1 {
            return Err(Z4Error::UnsupportedOp(
                "CHC function definitions currently support exactly one bound variable".to_string(),
            ));
        }

        let bound = &bounds[0];
        if let Some(pattern) = &bound.pattern {
            return Err(Z4Error::UnsupportedOp(format!(
                "CHC function definitions do not support destructuring patterns: {pattern:?}"
            )));
        }
        let domain = bound.domain.as_ref().ok_or_else(|| {
            Z4Error::UnsupportedOp("FuncDef without finite domain is not supported".to_string())
        })?;
        let domain_keys = extract_finite_domain_keys(domain)?;

        let mut range_sort: Option<TlaSort> = None;
        let mut elements = HashMap::new();
        for key in &domain_keys {
            let replacement = key_to_ast_expr(key);
            let substituted = self.substitute_expr(body, &bound.name.node, &replacement);
            let value = self.translate_value(&substituted)?;
            let ChcValue::Scalar { expr, sort } = value else {
                return Err(Z4Error::UnsupportedOp(
                    "nested function values are not supported in CHC FuncDef".to_string(),
                ));
            };
            if let Some(expected) = &range_sort {
                if expected != &sort {
                    return Err(Z4Error::TypeMismatch {
                        name: "FuncDef".to_string(),
                        expected: format!("{expected}"),
                        actual: format!("{sort}"),
                    });
                }
            } else {
                range_sort = Some(sort.clone());
            }
            elements.insert(key.clone(), expr);
        }

        Ok(ChcValue::Function(ChcFunctionValue {
            domain_keys,
            range_sort: range_sort.unwrap_or(TlaSort::Int),
            elements,
        }))
    }

    fn translate_record_expr(
        &mut self,
        fields: &[(Spanned<String>, Spanned<Expr>)],
    ) -> Z4Result<ChcValue> {
        let mut field_sorts = Vec::with_capacity(fields.len());
        let mut field_values = HashMap::new();

        for (field_name, field_expr) in fields {
            let value = self.translate_value(field_expr)?;
            let ChcValue::Scalar { expr, sort } = value else {
                return Err(Z4Error::UnsupportedOp(
                    "CHC record literals currently require scalar field values".to_string(),
                ));
            };
            field_sorts.push((field_name.node.clone(), sort.clone()));
            field_values.insert(field_name.node.clone(), expr);
        }

        let TlaSort::Record { field_sorts } = (TlaSort::Record { field_sorts }).canonicalized()
        else {
            unreachable!("record sort canonicalization preserves record shape");
        };

        Ok(ChcValue::Record(ChcRecordValue {
            field_sorts,
            fields: field_values,
        }))
    }

    fn translate_record_access_value(
        &mut self,
        base: &Spanned<Expr>,
        field: &RecordFieldName,
    ) -> Z4Result<ChcValue> {
        let base_value = self.translate_value(base)?;
        let ChcValue::Record(record) = base_value else {
            return Err(Z4Error::UnsupportedOp(
                "record access requires a record-valued expression".to_string(),
            ));
        };

        let field_name = field.name.node.clone();
        let field_sort = record
            .field_sorts
            .iter()
            .find(|(name, _)| name == &field_name)
            .map(|(_, sort)| sort.clone())
            .ok_or_else(|| Z4Error::UnknownVariable(format!("record field {field_name}")))?;
        let field_expr = record
            .fields
            .get(&field_name)
            .cloned()
            .ok_or_else(|| Z4Error::UnknownVariable(format!("record field {field_name}")))?;

        Ok(ChcValue::Scalar {
            expr: field_expr,
            sort: field_sort,
        })
    }

    fn substitute_except_at(
        &self,
        base: &Spanned<Expr>,
        path: &ExceptPathElement,
        value: &Spanned<Expr>,
    ) -> Spanned<Expr> {
        let replacement = match path {
            ExceptPathElement::Index(index) => Spanned::dummy(Expr::FuncApply(
                Box::new(base.clone()),
                Box::new(index.clone()),
            )),
            ExceptPathElement::Field(field) => {
                Spanned::dummy(Expr::RecordAccess(Box::new(base.clone()), field.clone()))
            }
        };

        self.substitute_expr(value, "@", &replacement)
    }

    fn translate_except_expr(
        &mut self,
        base: &Spanned<Expr>,
        specs: &[tla_core::ast::ExceptSpec],
    ) -> Z4Result<ChcValue> {
        let mut base_value = self.translate_value(base)?;

        for spec in specs {
            if spec.path.len() != 1 {
                return Err(Z4Error::UnsupportedOp(
                    "CHC EXCEPT currently supports exactly one path element".to_string(),
                ));
            }

            let substituted_value = self.substitute_except_at(base, &spec.path[0], &spec.value);
            let value = self.translate_value(&substituted_value)?;
            let ChcValue::Scalar {
                expr: value_expr,
                sort: value_sort,
            } = value
            else {
                return Err(Z4Error::UnsupportedOp(
                    "CHC EXCEPT values must be scalar".to_string(),
                ));
            };

            match (&spec.path[0], &mut base_value) {
                (ExceptPathElement::Index(index), ChcValue::Function(func)) => {
                    if value_sort != func.range_sort {
                        return Err(Z4Error::TypeMismatch {
                            name: "EXCEPT".to_string(),
                            expected: format!("{}", func.range_sort),
                            actual: format!("{value_sort}"),
                        });
                    }

                    for key in &func.domain_keys {
                        let key_expr = key_to_ast_expr(key);
                        let cond = self.translate_eq_internal(index, &key_expr)?;
                        let old_expr = func
                            .elements
                            .get(key)
                            .ok_or_else(|| Z4Error::UnknownVariable(format!("EXCEPT[{key}]")))?
                            .clone();
                        func.elements.insert(
                            key.clone(),
                            ChcExpr::ite(cond, value_expr.clone(), old_expr),
                        );
                    }
                }
                (ExceptPathElement::Field(field), ChcValue::Record(record)) => {
                    let field_name = field.name.node.clone();
                    let expected_sort = record
                        .field_sorts
                        .iter()
                        .find(|(name, _)| name == &field_name)
                        .map(|(_, sort)| sort.clone())
                        .ok_or_else(|| {
                            Z4Error::UnknownVariable(format!("record field {field_name}"))
                        })?;
                    if value_sort != expected_sort {
                        return Err(Z4Error::TypeMismatch {
                            name: "EXCEPT".to_string(),
                            expected: format!("{expected_sort}"),
                            actual: format!("{value_sort}"),
                        });
                    }
                    record.fields.insert(field_name, value_expr);
                }
                (ExceptPathElement::Index(_), _) => {
                    return Err(Z4Error::UnsupportedOp(
                        "EXCEPT index path requires a function-valued base".to_string(),
                    ));
                }
                (ExceptPathElement::Field(_), _) => {
                    return Err(Z4Error::UnsupportedOp(
                        "EXCEPT record-field path requires a record-valued base".to_string(),
                    ));
                }
            }
        }

        Ok(base_value)
    }

    fn translate_quantifier(
        &mut self,
        bounds: &[BoundVar],
        body: &Spanned<Expr>,
        is_forall: bool,
    ) -> Z4Result<ChcExpr> {
        if bounds.is_empty() {
            return dispatch_translate_bool(self, body);
        }

        let bound = &bounds[0];
        if let Some(pattern) = &bound.pattern {
            return Err(Z4Error::UnsupportedOp(format!(
                "CHC quantifiers do not support destructuring patterns: {pattern:?}"
            )));
        }

        let domain = bound.domain.as_ref().ok_or_else(|| {
            Z4Error::UnsupportedOp("unbounded CHC quantifiers are not supported".to_string())
        })?;

        if let Expr::SetFilter(filter_bound, pred) = &domain.node {
            let inner_domain = filter_bound.domain.as_ref().ok_or_else(|| {
                Z4Error::UnsupportedOp("SetFilter without domain not supported".to_string())
            })?;
            let replacement = Spanned::dummy(Expr::Ident(
                bound.name.node.clone(),
                tla_core::name_intern::NameId::INVALID,
            ));
            let pred_subst = self.substitute_expr(pred, &filter_bound.name.node, &replacement);
            let new_body = if is_forall {
                Spanned::dummy(Expr::Implies(Box::new(pred_subst), Box::new(body.clone())))
            } else {
                Spanned::dummy(Expr::And(Box::new(pred_subst), Box::new(body.clone())))
            };

            let new_bound = BoundVar {
                name: bound.name.clone(),
                domain: Some(inner_domain.clone()),
                pattern: None,
            };
            let mut nested = vec![new_bound];
            nested.extend_from_slice(&bounds[1..]);
            return self.translate_quantifier(&nested, &new_body, is_forall);
        }

        let domain_keys = extract_finite_domain_keys(domain)?;
        if let Expr::Range(lo, hi) = &domain.node {
            let lo_val: i64 = match &lo.node {
                Expr::Int(n) => n.try_into().map_err(|_| {
                    Z4Error::IntegerOverflow("range lower bound too large".to_string())
                })?,
                _ => 0,
            };
            let hi_val: i64 = match &hi.node {
                Expr::Int(n) => n.try_into().map_err(|_| {
                    Z4Error::IntegerOverflow("range upper bound too large".to_string())
                })?,
                _ => 0,
            };
            if hi_val >= lo_val && (hi_val - lo_val + 1) > 100 {
                return Err(Z4Error::UnsupportedOp(
                    "quantifier range too large for finite CHC expansion (>100)".to_string(),
                ));
            }
        }

        let mut expanded = Vec::new();
        for key in &domain_keys {
            let replacement = key_to_ast_expr(key);
            let substituted = self.substitute_expr(body, &bound.name.node, &replacement);
            expanded.push(self.translate_quantifier(&bounds[1..], &substituted, is_forall)?);
        }

        Ok(if is_forall {
            and_all(expanded)
        } else {
            or_all(expanded)
        })
    }

    fn translate_scalar_membership(
        &mut self,
        elem_expr: ChcExpr,
        elem_sort: &TlaSort,
        set: &Spanned<Expr>,
    ) -> Z4Result<ChcExpr> {
        match &set.node {
            Expr::Ident(name, _) if name == "BOOLEAN" => {
                if *elem_sort == TlaSort::Bool {
                    Ok(ChcExpr::eq(elem_expr.clone(), elem_expr))
                } else {
                    Ok(ChcExpr::Bool(false))
                }
            }
            Expr::Ident(name, _) if name == "Int" => {
                if *elem_sort == TlaSort::Int {
                    Ok(ChcExpr::eq(elem_expr.clone(), elem_expr))
                } else {
                    Ok(ChcExpr::Bool(false))
                }
            }
            Expr::Ident(name, _) if name == "Nat" => {
                if *elem_sort == TlaSort::Int {
                    Ok(ChcExpr::ge(elem_expr, ChcExpr::Int(0)))
                } else {
                    Ok(ChcExpr::Bool(false))
                }
            }
            Expr::SetEnum(elements) => {
                if elements.is_empty() {
                    return Ok(ChcExpr::Bool(false));
                }

                let mut disjuncts = Vec::new();
                for element in elements {
                    let value = self.translate_value(element)?;
                    let ChcValue::Scalar {
                        expr: rhs_expr,
                        sort: rhs_sort,
                    } = value
                    else {
                        return Err(Z4Error::UnsupportedOp(
                            "CHC set membership over function-valued set elements is unsupported"
                                .to_string(),
                        ));
                    };
                    disjuncts.push(self.scalar_eq(
                        elem_expr.clone(),
                        elem_sort,
                        rhs_expr,
                        &rhs_sort,
                    ));
                }
                Ok(or_all(disjuncts))
            }
            Expr::Range(lo, hi) => {
                if *elem_sort != TlaSort::Int {
                    return Ok(ChcExpr::Bool(false));
                }
                let lo = dispatch_translate_int(self, lo)?;
                let hi = dispatch_translate_int(self, hi)?;
                Ok(ChcExpr::and(
                    ChcExpr::ge(elem_expr.clone(), lo),
                    ChcExpr::le(elem_expr, hi),
                ))
            }
            _ => Err(Z4Error::UnsupportedOp(format!(
                "unsupported CHC scalar membership over {:?}",
                set.node
            ))),
        }
    }

    fn translate_func_set_membership(
        &mut self,
        elem: &Spanned<Expr>,
        domain: &Spanned<Expr>,
        range: &Spanned<Expr>,
    ) -> Z4Result<ChcExpr> {
        let value = self.translate_value(elem)?;
        let ChcValue::Function(func) = value else {
            return Ok(ChcExpr::Bool(false));
        };

        let domain_keys = extract_finite_domain_keys(domain)?;
        if func.domain_keys.len() != domain_keys.len()
            || domain_keys
                .iter()
                .any(|key| !func.elements.contains_key(key))
        {
            return Ok(ChcExpr::Bool(false));
        }

        let mut conjuncts = Vec::new();
        for key in &domain_keys {
            let elem_expr = func
                .elements
                .get(key)
                .ok_or_else(|| Z4Error::UnknownVariable(format!("f[{key}]")))?
                .clone();
            conjuncts.push(self.translate_scalar_membership(elem_expr, &func.range_sort, range)?);
        }
        Ok(and_all(conjuncts))
    }

    fn translate_record_set_membership(
        &mut self,
        elem: &Spanned<Expr>,
        fields: &[(Spanned<String>, Spanned<Expr>)],
    ) -> Z4Result<ChcExpr> {
        let value = self.translate_value(elem)?;
        let ChcValue::Record(record) = value else {
            return Ok(ChcExpr::Bool(false));
        };

        if record.field_sorts.len() != fields.len() {
            return Ok(ChcExpr::Bool(false));
        }

        let mut conjuncts = Vec::new();
        for (field_name, domain) in fields {
            let Some(field_expr) = record.fields.get(&field_name.node) else {
                return Ok(ChcExpr::Bool(false));
            };
            let Some((_, field_sort)) = record
                .field_sorts
                .iter()
                .find(|(name, _)| name == &field_name.node)
            else {
                return Ok(ChcExpr::Bool(false));
            };
            conjuncts.push(self.translate_scalar_membership(
                field_expr.clone(),
                field_sort,
                domain,
            )?);
        }

        Ok(and_all(conjuncts))
    }

    fn translate_membership(
        &mut self,
        elem: &Spanned<Expr>,
        set: &Spanned<Expr>,
    ) -> Z4Result<ChcExpr> {
        match &set.node {
            Expr::FuncSet(domain, range) => self.translate_func_set_membership(elem, domain, range),
            Expr::RecordSet(fields) => self.translate_record_set_membership(elem, fields),
            Expr::SetFilter(bound, pred) => {
                let domain = bound.domain.as_ref().ok_or_else(|| {
                    Z4Error::UnsupportedOp("SetFilter without domain not supported".to_string())
                })?;
                let in_domain = self.translate_membership(elem, domain)?;
                let pred_subst = self.substitute_expr(pred, &bound.name.node, elem);
                let pred = dispatch_translate_bool(self, &pred_subst)?;
                Ok(ChcExpr::and(in_domain, pred))
            }
            Expr::SetBuilder(body, bounds) => {
                let eq_body = Spanned::dummy(Expr::Eq(Box::new(elem.clone()), body.clone()));
                self.translate_quantifier(bounds, &eq_body, false)
            }
            _ => {
                let elem_value = self.translate_value(elem)?;
                let ChcValue::Scalar { expr, sort } = elem_value else {
                    return Err(Z4Error::UnsupportedOp(
                        "CHC membership only supports scalar elements or function-set tests"
                            .to_string(),
                    ));
                };
                self.translate_scalar_membership(expr, &sort, set)
            }
        }
    }

    fn translate_eq_internal(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Z4Result<ChcExpr> {
        let left = self.translate_value(left)?;
        let right = self.translate_value(right)?;

        match (left, right) {
            (
                ChcValue::Scalar {
                    expr: left_expr,
                    sort: left_sort,
                },
                ChcValue::Scalar {
                    expr: right_expr,
                    sort: right_sort,
                },
            ) => Ok(self.scalar_eq(left_expr, &left_sort, right_expr, &right_sort)),
            (ChcValue::Function(left_fun), ChcValue::Function(right_fun)) => {
                if left_fun.domain_keys.len() != right_fun.domain_keys.len()
                    || left_fun.range_sort != right_fun.range_sort
                    || left_fun
                        .domain_keys
                        .iter()
                        .any(|key| !right_fun.elements.contains_key(key))
                {
                    return Ok(ChcExpr::Bool(false));
                }

                let mut conjuncts = Vec::new();
                for key in &left_fun.domain_keys {
                    let left_expr = left_fun
                        .elements
                        .get(key)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("lhs[{key}]")))?
                        .clone();
                    let right_expr = right_fun
                        .elements
                        .get(key)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("rhs[{key}]")))?
                        .clone();
                    conjuncts.push(self.scalar_eq(
                        left_expr,
                        &left_fun.range_sort,
                        right_expr,
                        &right_fun.range_sort,
                    ));
                }
                Ok(and_all(conjuncts))
            }
            (ChcValue::Record(left_record), ChcValue::Record(right_record)) => {
                if left_record.field_sorts != right_record.field_sorts {
                    return Ok(ChcExpr::Bool(false));
                }

                let mut conjuncts = Vec::new();
                for (field_name, field_sort) in &left_record.field_sorts {
                    let left_expr = left_record
                        .fields
                        .get(field_name)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("lhs.{field_name}")))?
                        .clone();
                    let right_expr = right_record
                        .fields
                        .get(field_name)
                        .ok_or_else(|| Z4Error::UnknownVariable(format!("rhs.{field_name}")))?
                        .clone();
                    conjuncts.push(self.scalar_eq(left_expr, field_sort, right_expr, field_sort));
                }
                Ok(and_all(conjuncts))
            }
            _ => Ok(ChcExpr::Bool(false)),
        }
    }

    fn substitute_expr(
        &self,
        expr: &Spanned<Expr>,
        var_name: &str,
        replacement: &Spanned<Expr>,
    ) -> Spanned<Expr> {
        let mut sub = SubstituteExpr {
            subs: HashMap::from([(var_name, replacement)]),
            span_policy: SpanPolicy::Preserve,
        };
        let substituted = sub.fold_expr(expr.clone());
        let mut state_var_sub = SubstituteStateVar {
            var_name,
            replacement,
        };
        state_var_sub.fold_expr(substituted)
    }
}

impl TranslateExpr for ChcTranslator {
    type Bool = ChcExpr;
    type Int = ChcExpr;
    type Error = Z4Error;

    fn bool_const(&mut self, val: bool) -> ChcExpr {
        ChcExpr::Bool(val)
    }

    fn int_const(&mut self, val: i64) -> Z4Result<ChcExpr> {
        Ok(ChcExpr::Int(val))
    }

    fn lookup_bool_var(&mut self, name: &str) -> Z4Result<ChcExpr> {
        match self.lookup_declared_value(name)? {
            ChcValue::Scalar {
                expr,
                sort: TlaSort::Bool,
            } => Ok(expr),
            ChcValue::Scalar { sort, .. } => Err(Z4Error::TypeMismatch {
                name: name.to_string(),
                expected: "Bool".to_string(),
                actual: format!("{sort}"),
            }),
            ChcValue::Function(_) => Err(Z4Error::TypeMismatch {
                name: name.to_string(),
                expected: "Bool".to_string(),
                actual: "Function".to_string(),
            }),
            ChcValue::Record(_) => Err(Z4Error::TypeMismatch {
                name: name.to_string(),
                expected: "Bool".to_string(),
                actual: "Record".to_string(),
            }),
        }
    }

    fn lookup_int_var(&mut self, name: &str) -> Z4Result<ChcExpr> {
        match self.lookup_declared_value(name)? {
            ChcValue::Scalar {
                expr,
                sort: TlaSort::Int,
            } => Ok(expr),
            ChcValue::Scalar { sort, .. } => Err(Z4Error::TypeMismatch {
                name: name.to_string(),
                expected: "Int".to_string(),
                actual: format!("{sort}"),
            }),
            ChcValue::Function(_) => Err(Z4Error::TypeMismatch {
                name: name.to_string(),
                expected: "Int".to_string(),
                actual: "Function".to_string(),
            }),
            ChcValue::Record(_) => Err(Z4Error::TypeMismatch {
                name: name.to_string(),
                expected: "Int".to_string(),
                actual: "Record".to_string(),
            }),
        }
    }

    fn and(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::and(lhs, rhs)
    }

    fn or(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::or(lhs, rhs)
    }

    fn not(&mut self, expr: ChcExpr) -> ChcExpr {
        ChcExpr::not(expr)
    }

    fn implies(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::implies(lhs, rhs)
    }

    fn iff(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::Op(ChcOp::Iff, vec![Arc::new(lhs), Arc::new(rhs)])
    }

    fn lt(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::lt(lhs, rhs)
    }

    fn le(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::le(lhs, rhs)
    }

    fn gt(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::gt(lhs, rhs)
    }

    fn ge(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::ge(lhs, rhs)
    }

    fn add(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::add(lhs, rhs)
    }

    fn sub(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::sub(lhs, rhs)
    }

    fn mul(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> Z4Result<ChcExpr> {
        Ok(ChcExpr::mul(lhs, rhs))
    }

    fn neg(&mut self, expr: ChcExpr) -> ChcExpr {
        ChcExpr::neg(expr)
    }

    fn div(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> Z4Result<ChcExpr> {
        Ok(ChcExpr::Op(ChcOp::Div, vec![Arc::new(lhs), Arc::new(rhs)]))
    }

    fn modulo(&mut self, lhs: ChcExpr, rhs: ChcExpr) -> Z4Result<ChcExpr> {
        Ok(ChcExpr::Op(ChcOp::Mod, vec![Arc::new(lhs), Arc::new(rhs)]))
    }

    fn ite_bool(&mut self, cond: ChcExpr, then_b: ChcExpr, else_b: ChcExpr) -> ChcExpr {
        ChcExpr::ite(cond, then_b, else_b)
    }

    fn ite_int(&mut self, cond: ChcExpr, then_i: ChcExpr, else_i: ChcExpr) -> ChcExpr {
        ChcExpr::ite(cond, then_i, else_i)
    }

    fn translate_eq(&mut self, left: &Spanned<Expr>, right: &Spanned<Expr>) -> Z4Result<ChcExpr> {
        self.translate_eq_internal(left, right)
    }

    fn translate_bool_extended(&mut self, expr: &Spanned<Expr>) -> Option<Z4Result<ChcExpr>> {
        match &expr.node {
            Expr::Label(label) => Some(dispatch_translate_bool(self, &label.body)),
            Expr::Let(defs, body) => Some(
                self.inline_let_defs(defs, body)
                    .and_then(|inlined| dispatch_translate_bool(self, &inlined)),
            ),
            Expr::Prime(inner) => {
                if !self.allow_primed {
                    return Some(Err(Z4Error::UntranslatableExpr(
                        "primed variables not allowed in Init/Safety".to_string(),
                    )));
                }
                let old = self.use_primed_vars;
                self.use_primed_vars = true;
                let result = dispatch_translate_bool(self, inner);
                self.use_primed_vars = old;
                Some(result)
            }
            Expr::Unchanged(var_expr) => Some(self.translate_unchanged_chc(var_expr)),
            Expr::Forall(bounds, body) => Some(self.translate_quantifier(bounds, body, true)),
            Expr::Exists(bounds, body) => Some(self.translate_quantifier(bounds, body, false)),
            Expr::In(elem, set) => Some(self.translate_membership(elem, set)),
            Expr::NotIn(elem, set) => Some(self.translate_membership(elem, set).map(ChcExpr::not)),
            Expr::FuncApply(func, arg) => Some(match self.translate_func_apply_value(func, arg) {
                Ok(ChcValue::Scalar {
                    expr,
                    sort: TlaSort::Bool,
                }) => Ok(expr),
                Ok(ChcValue::Scalar { sort, .. }) => Err(Z4Error::TypeMismatch {
                    name: "function application".to_string(),
                    expected: "Bool".to_string(),
                    actual: format!("{sort}"),
                }),
                Ok(ChcValue::Function(_)) => Err(Z4Error::TypeMismatch {
                    name: "function application".to_string(),
                    expected: "Bool".to_string(),
                    actual: "Function".to_string(),
                }),
                Ok(ChcValue::Record(_)) => Err(Z4Error::TypeMismatch {
                    name: "function application".to_string(),
                    expected: "Bool".to_string(),
                    actual: "Record".to_string(),
                }),
                Err(e) => Err(e),
            }),
            Expr::RecordAccess(base, field) => {
                Some(match self.translate_record_access_value(base, field) {
                    Ok(ChcValue::Scalar {
                        expr,
                        sort: TlaSort::Bool,
                    }) => Ok(expr),
                    Ok(ChcValue::Scalar { sort, .. }) => Err(Z4Error::TypeMismatch {
                        name: "record access".to_string(),
                        expected: "Bool".to_string(),
                        actual: format!("{sort}"),
                    }),
                    Ok(ChcValue::Function(_)) => Err(Z4Error::TypeMismatch {
                        name: "record access".to_string(),
                        expected: "Bool".to_string(),
                        actual: "Function".to_string(),
                    }),
                    Ok(ChcValue::Record(_)) => Err(Z4Error::TypeMismatch {
                        name: "record access".to_string(),
                        expected: "Bool".to_string(),
                        actual: "Record".to_string(),
                    }),
                    Err(e) => Err(e),
                })
            }
            Expr::Int(n) => {
                let val: i64 = match n.try_into() {
                    Ok(v) => v,
                    Err(_) => {
                        return Some(Err(Z4Error::IntegerOverflow(format!(
                            "integer {n} too large for CHC"
                        ))))
                    }
                };
                Some(Ok(ChcExpr::Int(val)))
            }
            Expr::Add(..)
            | Expr::Sub(..)
            | Expr::Mul(..)
            | Expr::Neg(..)
            | Expr::IntDiv(..)
            | Expr::Mod(..) => Some(dispatch_translate_int(self, expr)),
            _ => None,
        }
    }

    fn translate_int_extended(&mut self, expr: &Spanned<Expr>) -> Option<Z4Result<ChcExpr>> {
        match &expr.node {
            Expr::Label(label) => Some(dispatch_translate_int(self, &label.body)),
            Expr::Let(defs, body) => Some(
                self.inline_let_defs(defs, body)
                    .and_then(|inlined| dispatch_translate_int(self, &inlined)),
            ),
            Expr::Prime(inner) => {
                if !self.allow_primed {
                    return Some(Err(Z4Error::UntranslatableExpr(
                        "primed variables not allowed in Init/Safety".to_string(),
                    )));
                }
                let old = self.use_primed_vars;
                self.use_primed_vars = true;
                let result = dispatch_translate_int(self, inner);
                self.use_primed_vars = old;
                Some(result)
            }
            Expr::FuncApply(func, arg) => Some(match self.translate_func_apply_value(func, arg) {
                Ok(ChcValue::Scalar {
                    expr,
                    sort: TlaSort::Int,
                }) => Ok(expr),
                Ok(ChcValue::Scalar { sort, .. }) => Err(Z4Error::TypeMismatch {
                    name: "function application".to_string(),
                    expected: "Int".to_string(),
                    actual: format!("{sort}"),
                }),
                Ok(ChcValue::Function(_)) => Err(Z4Error::TypeMismatch {
                    name: "function application".to_string(),
                    expected: "Int".to_string(),
                    actual: "Function".to_string(),
                }),
                Ok(ChcValue::Record(_)) => Err(Z4Error::TypeMismatch {
                    name: "function application".to_string(),
                    expected: "Int".to_string(),
                    actual: "Record".to_string(),
                }),
                Err(e) => Err(e),
            }),
            Expr::RecordAccess(base, field) => {
                Some(match self.translate_record_access_value(base, field) {
                    Ok(ChcValue::Scalar {
                        expr,
                        sort: TlaSort::Int,
                    }) => Ok(expr),
                    Ok(ChcValue::Scalar { sort, .. }) => Err(Z4Error::TypeMismatch {
                        name: "record access".to_string(),
                        expected: "Int".to_string(),
                        actual: format!("{sort}"),
                    }),
                    Ok(ChcValue::Function(_)) => Err(Z4Error::TypeMismatch {
                        name: "record access".to_string(),
                        expected: "Int".to_string(),
                        actual: "Function".to_string(),
                    }),
                    Ok(ChcValue::Record(_)) => Err(Z4Error::TypeMismatch {
                        name: "record access".to_string(),
                        expected: "Int".to_string(),
                        actual: "Record".to_string(),
                    }),
                    Err(e) => Err(e),
                })
            }
            _ => None,
        }
    }
}

struct SubstituteStateVar<'a> {
    var_name: &'a str,
    replacement: &'a Spanned<Expr>,
}

impl ExprFold for SubstituteStateVar<'_> {
    fn fold_state_var(
        &mut self,
        name: String,
        idx: u16,
        id: tla_core::name_intern::NameId,
    ) -> Expr {
        if name == self.var_name {
            self.replacement.node.clone()
        } else {
            Expr::StateVar(name, idx, id)
        }
    }
}
