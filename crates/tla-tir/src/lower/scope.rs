// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use tla_core::ast::{Expr, Module, OperatorDef, Substitution};
use tla_core::Spanned;

#[derive(Clone)]
pub(super) struct LoweringScope<'a>(Rc<LoweringScopeData<'a>>);

struct LoweringScopeData<'a> {
    module: &'a Module,
    bindings: HashMap<String, BoundExpr<'a>>,
    shadowed_bindings: HashSet<String>,
    operator_defs: HashMap<String, BoundOperator<'a>>,
    parent: Option<LoweringScope<'a>>,
}

#[derive(Clone)]
pub(super) struct BoundExpr<'a> {
    pub(super) scope: LoweringScope<'a>,
    pub(super) expr: Spanned<Expr>,
}

#[derive(Clone)]
pub(super) struct BoundOperator<'a> {
    pub(super) scope: LoweringScope<'a>,
    pub(super) def: &'a OperatorDef,
}

pub(super) struct ResolvedExpr<'a> {
    pub(super) scope: LoweringScope<'a>,
    pub(super) expr: Spanned<Expr>,
}

impl<'a> LoweringScope<'a> {
    pub(super) fn root(module: &'a Module) -> Self {
        Self(Rc::new(LoweringScopeData {
            module,
            bindings: HashMap::new(),
            shadowed_bindings: HashSet::new(),
            operator_defs: HashMap::new(),
            parent: None,
        }))
    }

    pub(super) fn module(&self) -> &'a Module {
        self.0.module
    }

    pub(super) fn with_module(&self, module: &'a Module) -> Self {
        Self(Rc::new(LoweringScopeData {
            module,
            bindings: HashMap::new(),
            shadowed_bindings: HashSet::new(),
            operator_defs: HashMap::new(),
            parent: Some(self.clone()),
        }))
    }

    pub(super) fn with_bindings_from<I>(
        &self,
        module: &'a Module,
        origin: &Self,
        bindings: I,
    ) -> Self
    where
        I: IntoIterator<Item = (String, Spanned<Expr>)>,
    {
        let bindings = bindings
            .into_iter()
            .map(|(name, expr)| {
                (
                    name,
                    BoundExpr {
                        scope: origin.clone(),
                        expr,
                    },
                )
            })
            .collect();

        Self(Rc::new(LoweringScopeData {
            module,
            bindings,
            shadowed_bindings: HashSet::new(),
            operator_defs: HashMap::new(),
            parent: Some(self.clone()),
        }))
    }

    pub(super) fn with_operator_defs(&self, defs: &'a [OperatorDef]) -> Self {
        let operator_defs = defs
            .iter()
            .map(|def| {
                (
                    def.name.node.clone(),
                    BoundOperator {
                        scope: self.clone(),
                        def,
                    },
                )
            })
            .collect();

        Self(Rc::new(LoweringScopeData {
            module: self.module(),
            bindings: HashMap::new(),
            shadowed_bindings: HashSet::new(),
            operator_defs,
            parent: Some(self.clone()),
        }))
    }

    pub(super) fn with_shadowed_bindings<I>(&self, names: I) -> Self
    where
        I: IntoIterator<Item = String>,
    {
        Self(Rc::new(LoweringScopeData {
            module: self.module(),
            bindings: HashMap::new(),
            shadowed_bindings: names.into_iter().collect(),
            operator_defs: HashMap::new(),
            parent: Some(self.clone()),
        }))
    }

    pub(super) fn with_same_module_substitutions(&self, substitutions: &[Substitution]) -> Self {
        self.with_bindings_from(
            self.module(),
            self,
            substitutions
                .iter()
                .map(|sub| (sub.from.node.clone(), sub.to.clone())),
        )
    }

    pub(super) fn lookup_binding(&self, name: &str) -> Option<BoundExpr<'a>> {
        if self.0.shadowed_bindings.contains(name) {
            return None;
        }
        if let Some(bound) = self.0.bindings.get(name) {
            return Some(bound.clone());
        }

        self.0
            .parent
            .as_ref()
            .and_then(|parent| parent.lookup_binding(name))
    }

    pub(super) fn lookup_operator(&self, name: &str) -> Option<BoundOperator<'a>> {
        if let Some(bound) = self.0.operator_defs.get(name) {
            return Some(bound.clone());
        }

        self.0
            .parent
            .as_ref()
            .and_then(|parent| parent.lookup_operator(name))
    }
}
