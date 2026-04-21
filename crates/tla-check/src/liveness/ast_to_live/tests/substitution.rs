// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Substitution and reification tests: ExprFold-based value substitution, validation
//!
//! Split from liveness/ast_to_live/tests.rs — Part of #2779

use super::*;

fn validate_substitution_values(
    expr: &Expr,
    subs: &HashMap<String, Value>,
    original: &Arc<Spanned<Expr>>,
) -> Result<(), ConvertError> {
    for (name, value) in subs {
        if AstToLive::expr_references_name(expr, name)
            && !value_is_reifiable_for_substitution(value)
        {
            return Err(ConvertError::UnsupportedValueReification {
                original: original.clone(),
                ident: name.clone(),
                value_variant: value_variant_name(value),
            });
        }
    }
    Ok(())
}

/// Substitute values for identifiers in an expression using ExprFold.
///
/// This is used to expand quantified temporal formulas by replacing bound
/// variables with their concrete values. This is necessary because LiveExpr
/// stores AST references that are evaluated later without the quantifier context.
fn substitute_values_in_expr(expr: &Spanned<Expr>, subs: &HashMap<String, Value>) -> Spanned<Expr> {
    let mut folder = SubstituteValues { subs: subs.clone() };
    folder.fold_expr(expr.clone())
}

/// ExprFold-based value substitution with capture avoidance for binding forms.
///
/// Replaces `Ident(name)` with `value_to_expr(subs[name])` for all names in `subs`,
/// while respecting variable shadowing in quantifiers, lambdas, and other binding forms.
struct SubstituteValues {
    subs: HashMap<String, Value>,
}

impl SubstituteValues {
    fn filtered(&self, shadowed: &HashSet<String>) -> Self {
        Self {
            subs: self
                .subs
                .iter()
                .filter(|(k, _)| !shadowed.contains(*k))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        }
    }

    fn bound_names(bounds: &[BoundVar]) -> HashSet<String> {
        let mut names = HashSet::new();
        for b in bounds {
            names.insert(b.name.node.clone());
            if let Some(BoundPattern::Tuple(vars)) = &b.pattern {
                names.extend(vars.iter().map(|v| v.node.clone()));
            } else if let Some(BoundPattern::Var(v)) = &b.pattern {
                names.insert(v.node.clone());
            }
        }
        names
    }
}

impl ExprFold for SubstituteValues {
    fn fold_ident(&mut self, name: String, name_id: tla_core::name_intern::NameId) -> Expr {
        if let Some(value) = self.subs.get(&name) {
            value_to_expr(value).expect("test value should be reifiable")
        } else {
            Expr::Ident(name, name_id)
        }
    }

    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let span = expr.span;
        let new_node = match expr.node {
            // Binding forms: filter subs to avoid capturing bound variables
            Expr::Lambda(params, body) => {
                let shadowed: HashSet<_> = params.iter().map(|p| p.node.clone()).collect();
                let mut inner = self.filtered(&shadowed);
                Expr::Lambda(params, Box::new(inner.fold_expr(*body)))
            }
            Expr::Forall(bounds, body) => {
                let shadowed = Self::bound_names(&bounds);
                let new_bounds = self.fold_bound_vars(bounds);
                let mut inner = self.filtered(&shadowed);
                Expr::Forall(new_bounds, Box::new(inner.fold_expr(*body)))
            }
            Expr::Exists(bounds, body) => {
                let shadowed = Self::bound_names(&bounds);
                let new_bounds = self.fold_bound_vars(bounds);
                let mut inner = self.filtered(&shadowed);
                Expr::Exists(new_bounds, Box::new(inner.fold_expr(*body)))
            }
            Expr::Choose(bound, body) => {
                let shadowed = Self::bound_names(std::slice::from_ref(&bound));
                let new_bound = self.fold_bound_var(bound);
                let mut inner = self.filtered(&shadowed);
                Expr::Choose(new_bound, Box::new(inner.fold_expr(*body)))
            }
            Expr::SetBuilder(body, bounds) => {
                let shadowed = Self::bound_names(&bounds);
                let new_bounds = self.fold_bound_vars(bounds);
                let mut inner = self.filtered(&shadowed);
                Expr::SetBuilder(Box::new(inner.fold_expr(*body)), new_bounds)
            }
            Expr::SetFilter(bound, pred) => {
                let shadowed = Self::bound_names(std::slice::from_ref(&bound));
                let new_bound = self.fold_bound_var(bound);
                let mut inner = self.filtered(&shadowed);
                Expr::SetFilter(new_bound, Box::new(inner.fold_expr(*pred)))
            }
            Expr::FuncDef(bounds, body) => {
                let shadowed = Self::bound_names(&bounds);
                let new_bounds = self.fold_bound_vars(bounds);
                let mut inner = self.filtered(&shadowed);
                Expr::FuncDef(new_bounds, Box::new(inner.fold_expr(*body)))
            }
            // All other variants: delegate to default ExprFold traversal
            other => {
                return Spanned {
                    node: self.fold_expr_inner(other),
                    span,
                }
            }
        };
        Spanned {
            node: new_node,
            span,
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_substitution_values_rejects_unsupported_value() {
    let expr = Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID);
    let original = Arc::new(spanned(expr.clone()));

    let mut subs = HashMap::new();
    subs.insert("x".to_string(), Value::AnySet);

    let err = validate_substitution_values(&expr, &subs, &original).unwrap_err();
    match err {
        ConvertError::UnsupportedValueReification {
            ident,
            value_variant,
            ..
        } => {
            assert_eq!(ident, "x");
            assert_eq!(value_variant, "AnySet");
        }
        other => panic!("Expected UnsupportedValueReification, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substitute_values_no_match() {
    let subs = HashMap::new();
    let expr = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let result = substitute_values_in_expr(&expr, &subs);
    match result.node {
        Expr::Ident(name, _) => assert_eq!(name, "x"),
        _ => panic!("Expected unchanged Ident"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substitute_values_match() {
    let mut subs = HashMap::new();
    subs.insert("x".to_string(), Value::SmallInt(42));
    let expr = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let result = substitute_values_in_expr(&expr, &subs);
    match result.node {
        Expr::Int(n) => assert_eq!(n, BigInt::from(42)),
        _ => panic!("Expected Int"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substitute_values_in_binary_op() {
    let mut subs = HashMap::new();
    subs.insert("x".to_string(), Value::SmallInt(1));
    let expr = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let result = substitute_values_in_expr(&expr, &subs);
    match result.node {
        Expr::Add(a, b) => {
            assert!(matches!(a.node, Expr::Int(_)));
            assert!(matches!(b.node, Expr::Int(_)));
        }
        _ => panic!("Expected Add"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substitute_values_preserves_literals() {
    let subs = HashMap::new();
    let expr = spanned(Expr::Bool(true));
    let result = substitute_values_in_expr(&expr, &subs);
    assert!(matches!(result.node, Expr::Bool(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_is_reifiable_accepts_lazy_set_variants() {
    // Verify that the 9 lazy set/function variants handled by value_to_expr
    // are also accepted by value_is_reifiable_for_substitution (#1408).

    let base_set = Value::set([Value::SmallInt(1), Value::SmallInt(2)]);

    // Subset
    let subset = Value::Subset(SubsetValue::new(base_set.clone()));
    assert!(value_is_reifiable_for_substitution(&subset));

    // FuncSet
    let funcset = FuncSetValue::new(base_set.clone(), base_set.clone());
    assert!(value_is_reifiable_for_substitution(&Value::FuncSet(
        funcset
    )));

    // RecordSet
    let rs = RecordSetValue::new([(Arc::<str>::from("a"), base_set.clone())]);
    assert!(value_is_reifiable_for_substitution(&Value::RecordSet(
        Arc::new(rs)
    )));

    // TupleSet
    let ts = TupleSetValue::new([base_set.clone()]);
    assert!(value_is_reifiable_for_substitution(&Value::TupleSet(
        Arc::new(ts)
    )));

    // SetCup
    let cup = SetCupValue::new(base_set.clone(), base_set.clone());
    assert!(value_is_reifiable_for_substitution(&Value::SetCup(cup)));

    // SetCap
    let cap = SetCapValue::new(base_set.clone(), base_set.clone());
    assert!(value_is_reifiable_for_substitution(&Value::SetCap(cap)));

    // SetDiff
    let diff = SetDiffValue::new(base_set.clone(), base_set.clone());
    assert!(value_is_reifiable_for_substitution(&Value::SetDiff(diff)));

    // BigUnion
    let union = UnionValue::new(base_set);
    assert!(value_is_reifiable_for_substitution(&Value::BigUnion(union)));

    // IntFunc
    let ifunc = IntIntervalFunc::new(1, 2, vec![Value::SmallInt(10), Value::SmallInt(20)]);
    assert!(value_is_reifiable_for_substitution(&Value::IntFunc(
        Arc::new(ifunc)
    )));

    // Non-reifiable variants should still return false
    assert!(!value_is_reifiable_for_substitution(&Value::AnySet));
    assert!(!value_is_reifiable_for_substitution(&Value::StringSet));
}
