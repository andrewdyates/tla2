// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared implicit INSTANCE substitution helpers.
//!
//! Part of #3226: keep the implicit-substitution contract in one production
//! helper instead of reconstructing it separately in module-ref and liveness
//! paths.

use super::{EvalCtx, Expr};
use rustc_hash::FxHashSet;
use tla_core::ast::{Module, Substitution, Unit};
use tla_core::name_intern::intern_name;
use tla_core::Spanned;

#[must_use]
pub(crate) fn collect_implicit_instance_targets(module: &Module) -> Vec<String> {
    let mut seen = FxHashSet::default();
    let mut targets = Vec::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(names) => {
                for name in names {
                    if seen.insert(name.node.clone()) {
                        targets.push(name.node.clone());
                    }
                }
            }
            Unit::Constant(decls) => {
                for decl in decls {
                    if seen.insert(decl.name.node.clone()) {
                        targets.push(decl.name.node.clone());
                    }
                }
            }
            Unit::Operator(_)
            | Unit::Assume(_)
            | Unit::Theorem(_)
            | Unit::Instance(_)
            | Unit::Recursive(_)
            | Unit::Separator => {}
        }
    }

    targets
}

impl EvalCtx {
    fn has_visible_implicit_instance_symbol(&self, name: &str) -> bool {
        self.active_instance_substitution(name).is_some()
            || self.var_registry().get(name).is_some()
            || self.is_config_constant(name)
            || self.get_op(name).is_some_and(|def| def.params.is_empty())
    }

    #[must_use]
    pub fn compute_effective_instance_substitutions(
        &self,
        module_name: &str,
        explicit_subs: &[Substitution],
    ) -> Vec<Substitution> {
        let mut effective_subs = explicit_subs.to_vec();
        let explicit_names: FxHashSet<&str> = explicit_subs
            .iter()
            .map(|sub| sub.from.node.as_str())
            .collect();

        if let Some(targets) = self.shared.instance_implicit_targets.get(module_name) {
            for target in targets {
                let target_name = target.as_str();
                if explicit_names.contains(target_name)
                    || !self.has_visible_implicit_instance_symbol(target_name)
                {
                    continue;
                }

                effective_subs.push(Substitution {
                    from: Spanned::dummy(target.clone()),
                    to: Spanned::dummy(Expr::Ident(target.clone(), intern_name(target_name))),
                });
            }
        }

        effective_subs
    }

    pub fn active_instance_substitution(&self, name: &str) -> Option<&Substitution> {
        self.instance_substitutions()
            .and_then(|subs| subs.iter().find(|sub| sub.from.node == name))
    }

    #[inline]
    pub fn has_active_instance_substitution(&self, name: &str) -> bool {
        self.active_instance_substitution(name).is_some()
    }
}
