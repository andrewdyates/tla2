// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Init and Next action emission: analyzes TLA+ Init/Next predicates
//! and generates corresponding Rust code for state initialization
//! and transition functions.

mod init;
mod prime_check;

use super::{to_snake_case, Expr, HashSet, RustEmitter, Spanned, WRITE_TO_STRING_ERR};
use std::fmt::Write;
use tla_core::ExprFold;
use tla_core::NameId;
type CgResult = Result<(), crate::error::CodegenError>;

impl<'a> RustEmitter<'a> {
    pub(in crate::emit) fn emit_next_body(
        &mut self,
        expr: &Spanned<Expr>,
        variables: &[String],
    ) -> CgResult {
        let expanded = self.expand_operators(&expr.node);
        let actions = Self::collect_actions(&expanded);

        if actions.is_empty() {
            self.writeln_indented("// Could not parse Next action");
            self.writeln_indented("vec![]");
            return Ok(());
        }

        self.writeln_indented("let mut next_states = Vec::new();");
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        for (i, action) in actions.iter().enumerate() {
            self.writeln_indented(&format!("// Action {}", i + 1));
            self.emit_action(action, variables)?;
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        }

        self.writeln_indented("next_states");
        Ok(())
    }

    pub(in crate::emit) fn emit_for_each_next_body(
        &mut self,
        expr: &Spanned<Expr>,
        variables: &[String],
        yield_state_fn: &str,
    ) -> CgResult {
        let expanded = self.expand_operators(&expr.node);
        let actions = Self::collect_actions(&expanded);

        if actions.is_empty() {
            self.writeln_indented("// Could not parse Next action");
            self.writeln_indented(&format!("let _ = (state, &mut {});", yield_state_fn));
            self.writeln_indented("std::ops::ControlFlow::Continue(())");
            return Ok(());
        }

        for (i, action) in actions.iter().enumerate() {
            self.writeln_indented(&format!("// Action {}", i + 1));
            self.emit_action_for_each(action, variables, yield_state_fn)?;
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        }

        self.writeln_indented("std::ops::ControlFlow::Continue(())");
        Ok(())
    }

    pub(in crate::emit) fn collect_actions(expr: &Expr) -> Vec<Expr> {
        match expr {
            Expr::Or(left, right) => {
                let mut actions = Self::collect_actions(&left.node);
                actions.extend(Self::collect_actions(&right.node));
                actions
            }
            _ => vec![expr.clone()],
        }
    }

    fn emit_action(&mut self, action: &Expr, variables: &[String]) -> CgResult {
        let mut primed_assigns = std::collections::HashMap::<String, Expr>::new();
        let mut unchanged: HashSet<String> = HashSet::new();
        let mut guards = Vec::new();

        Self::analyze_action(action, &mut primed_assigns, &mut unchanged, &mut guards);

        let choices: Vec<(String, Expr)> = primed_assigns
            .iter()
            .filter_map(|(var, expr)| {
                if let Expr::In(elem, set) = expr {
                    if matches!(&elem.node, Expr::Prime(_)) {
                        return Some((var.clone(), set.node.clone()));
                    }
                }
                None
            })
            .collect();

        let loop_choices: Vec<(String, Expr)> = choices
            .into_iter()
            .filter(|(var, _set)| !unchanged.contains(var))
            .collect();
        let loop_choice_vars: HashSet<String> =
            loop_choices.iter().map(|(v, _)| v.clone()).collect();
        let mut allowed_prime_vars = loop_choice_vars.clone();
        allowed_prime_vars.extend(unchanged.iter().cloned());

        let mut guard_parts: Vec<String> = guards
            .iter()
            .map(|g| self.expr_to_rust_with_state(g, true))
            .collect();

        for var in variables {
            if !unchanged.contains(var) {
                continue;
            }
            let Some(expr) = primed_assigns.get(var) else {
                continue;
            };
            let rust_var = to_snake_case(var);
            match expr {
                Expr::In(_elem, set) => {
                    if !Self::is_next_supported_prime_uses(&set.node, &allowed_prime_vars) {
                        continue;
                    }
                    let state_var = Expr::Ident(var.clone(), NameId::INVALID);
                    guard_parts.push(
                        self.emit_membership_with_scope(&state_var, &set.node, true, "state", None),
                    );
                }
                _ => {
                    if !Self::is_next_supported_prime_uses(expr, &allowed_prime_vars) {
                        continue;
                    }
                    guard_parts.push(format!(
                        "state.{} == {}",
                        rust_var,
                        self.expr_to_rust_with_state(expr, true)
                    ));
                }
            }
        }

        if !guard_parts.is_empty() {
            self.writeln_indented(&format!("if {} {{", guard_parts.join(" && ")));
            self.indent += 1;
        }

        for var in variables {
            if unchanged.contains(var) {
                let rust_var = to_snake_case(var);
                self.writeln_indented(&format!(
                    "let {}_next = state.{}.clone();",
                    rust_var, rust_var
                ));
            }
        }

        if loop_choices.is_empty() {
            self.writeln_indented("next_states.push(Self::State {");
            self.indent += 1;
            for var in variables {
                let rust_var = to_snake_case(var);
                if unchanged.contains(var) {
                    self.writeln_indented(&format!("{}: state.{}.clone(),", rust_var, rust_var));
                } else if let Some(expr) = primed_assigns.get(var) {
                    let value = self.primed_expr_to_rust(expr);
                    self.writeln_indented(&format!("{}: {},", rust_var, value));
                } else {
                    self.writeln_indented(&format!("{}: state.{}.clone(),", rust_var, rust_var));
                }
            }
            self.indent -= 1;
            self.writeln_indented("});");
        } else {
            for (var, set_expr) in &loop_choices {
                let rust_var = to_snake_case(var);
                let set_str = self.primed_expr_to_rust(set_expr);
                self.writeln_indented(&format!("for {}_next in {} {{", rust_var, set_str));
                self.indent += 1;
            }

            self.writeln_indented("next_states.push(Self::State {");
            self.indent += 1;
            for var in variables {
                let rust_var = to_snake_case(var);
                if loop_choice_vars.contains(var) {
                    self.writeln_indented(&format!("{}: {}_next.clone(),", rust_var, rust_var));
                } else if unchanged.contains(var) {
                    self.writeln_indented(&format!("{}: state.{}.clone(),", rust_var, rust_var));
                } else if let Some(expr) = primed_assigns.get(var) {
                    let value = self.primed_expr_to_rust(expr);
                    self.writeln_indented(&format!("{}: {},", rust_var, value));
                } else {
                    self.writeln_indented(&format!("{}: state.{}.clone(),", rust_var, rust_var));
                }
            }
            self.indent -= 1;
            self.writeln_indented("});");

            for _ in &loop_choices {
                self.indent -= 1;
                self.writeln_indented("}");
            }
        }

        if !guard_parts.is_empty() {
            self.indent -= 1;
            self.writeln_indented("}");
        }

        Ok(())
    }

    fn emit_action_for_each(
        &mut self,
        action: &Expr,
        variables: &[String],
        yield_state_fn: &str,
    ) -> CgResult {
        let mut primed_assigns = std::collections::HashMap::<String, Expr>::new();
        let mut unchanged: HashSet<String> = HashSet::new();
        let mut guards = Vec::new();

        Self::analyze_action(action, &mut primed_assigns, &mut unchanged, &mut guards);

        let choices: Vec<(String, Expr)> = primed_assigns
            .iter()
            .filter_map(|(var, expr)| {
                if let Expr::In(elem, set) = expr {
                    if matches!(&elem.node, Expr::Prime(_)) {
                        return Some((var.clone(), set.node.clone()));
                    }
                }
                None
            })
            .collect();

        let loop_choices: Vec<(String, Expr)> = choices
            .into_iter()
            .filter(|(var, _set)| !unchanged.contains(var))
            .collect();
        let loop_choice_vars: HashSet<String> =
            loop_choices.iter().map(|(v, _)| v.clone()).collect();
        let mut allowed_prime_vars = loop_choice_vars.clone();
        allowed_prime_vars.extend(unchanged.iter().cloned());

        let mut guard_parts: Vec<String> = guards
            .iter()
            .map(|g| self.expr_to_rust_with_state(g, true))
            .collect();

        for var in variables {
            if !unchanged.contains(var) {
                continue;
            }
            let Some(expr) = primed_assigns.get(var) else {
                continue;
            };
            let rust_var = to_snake_case(var);
            match expr {
                Expr::In(_elem, set) => {
                    if !Self::is_next_supported_prime_uses(&set.node, &allowed_prime_vars) {
                        continue;
                    }
                    let state_var = Expr::Ident(var.clone(), NameId::INVALID);
                    guard_parts.push(
                        self.emit_membership_with_scope(&state_var, &set.node, true, "state", None),
                    );
                }
                _ => {
                    if !Self::is_next_supported_prime_uses(expr, &allowed_prime_vars) {
                        continue;
                    }
                    guard_parts.push(format!(
                        "state.{} == {}",
                        rust_var,
                        self.expr_to_rust_with_state(expr, true)
                    ));
                }
            }
        }

        if !guard_parts.is_empty() {
            self.writeln_indented(&format!("if {} {{", guard_parts.join(" && ")));
            self.indent += 1;
        }

        for var in variables {
            if unchanged.contains(var) {
                let rust_var = to_snake_case(var);
                self.writeln_indented(&format!(
                    "let {}_next = state.{}.clone();",
                    rust_var, rust_var
                ));
            }
        }

        if loop_choices.is_empty() {
            self.writeln_indented(&format!(
                "if let std::ops::ControlFlow::Break(()) = {}(Self::State {{",
                yield_state_fn
            ));
            self.indent += 1;
            for var in variables {
                let rust_var = to_snake_case(var);
                if unchanged.contains(var) {
                    self.writeln_indented(&format!("{}: state.{}.clone(),", rust_var, rust_var));
                } else if let Some(expr) = primed_assigns.get(var) {
                    let value = self.primed_expr_to_rust(expr);
                    self.writeln_indented(&format!("{}: {},", rust_var, value));
                } else {
                    self.writeln_indented(&format!("{}: state.{}.clone(),", rust_var, rust_var));
                }
            }
            self.indent -= 1;
            self.writeln_indented("}) {");
            self.indent += 1;
            self.writeln_indented("return std::ops::ControlFlow::Break(());");
            self.indent -= 1;
            self.writeln_indented("}");
        } else {
            for (var, set_expr) in &loop_choices {
                let rust_var = to_snake_case(var);
                let set_str = self.primed_expr_to_rust(set_expr);
                self.writeln_indented(&format!("for {}_next in {} {{", rust_var, set_str));
                self.indent += 1;
            }

            self.writeln_indented(&format!(
                "if let std::ops::ControlFlow::Break(()) = {}(Self::State {{",
                yield_state_fn
            ));
            self.indent += 1;
            for var in variables {
                let rust_var = to_snake_case(var);
                if loop_choice_vars.contains(var) {
                    self.writeln_indented(&format!("{}: {}_next.clone(),", rust_var, rust_var));
                } else if unchanged.contains(var) {
                    self.writeln_indented(&format!("{}: state.{}.clone(),", rust_var, rust_var));
                } else if let Some(expr) = primed_assigns.get(var) {
                    let value = self.primed_expr_to_rust(expr);
                    self.writeln_indented(&format!("{}: {},", rust_var, value));
                } else {
                    self.writeln_indented(&format!("{}: state.{}.clone(),", rust_var, rust_var));
                }
            }
            self.indent -= 1;
            self.writeln_indented("}) {");
            self.indent += 1;
            self.writeln_indented("return std::ops::ControlFlow::Break(());");
            self.indent -= 1;
            self.writeln_indented("}");

            for _ in &loop_choices {
                self.indent -= 1;
                self.writeln_indented("}");
            }
        }

        if !guard_parts.is_empty() {
            self.indent -= 1;
            self.writeln_indented("}");
        }

        Ok(())
    }

    pub(in crate::emit) fn analyze_action(
        expr: &Expr,
        primed_assigns: &mut std::collections::HashMap<String, Expr>,
        unchanged: &mut HashSet<String>,
        guards: &mut Vec<Expr>,
    ) {
        match expr {
            Expr::And(left, right) => {
                Self::analyze_action(&left.node, primed_assigns, unchanged, guards);
                Self::analyze_action(&right.node, primed_assigns, unchanged, guards);
            }
            Expr::Eq(left, right) => {
                if let Expr::Prime(inner) = &left.node {
                    if let Expr::Ident(name, _) = &inner.node {
                        primed_assigns.insert(name.clone(), right.node.clone());
                        return;
                    }
                }
                guards.push(expr.clone());
            }
            Expr::In(elem, _set) => {
                if let Expr::Prime(inner) = &elem.node {
                    if let Expr::Ident(name, _) = &inner.node {
                        primed_assigns.insert(name.clone(), expr.clone());
                        return;
                    }
                }
                guards.push(expr.clone());
            }
            Expr::Unchanged(vars) => {
                Self::collect_unchanged_vars(&vars.node, unchanged);
            }
            _ => {
                guards.push(expr.clone());
            }
        }
    }

    pub(in crate::emit) fn collect_unchanged_vars(expr: &Expr, unchanged: &mut HashSet<String>) {
        match expr {
            Expr::Ident(name, _) => {
                unchanged.insert(name.clone());
            }
            Expr::Tuple(elems) => {
                for elem in elems {
                    Self::collect_unchanged_vars(&elem.node, unchanged);
                }
            }
            _ => {}
        }
    }

    pub(in crate::emit) fn primed_expr_to_rust(&self, expr: &Expr) -> String {
        match expr {
            Expr::Prime(inner) => {
                if let Expr::Ident(name, _) = &inner.node {
                    format!("{}_next", to_snake_case(name))
                } else {
                    self.expr_to_rust(expr)
                }
            }
            Expr::Ident(name, _) if self.state_vars.contains(name) => {
                format!("state.{}.clone()", to_snake_case(name))
            }
            _ => self.expr_to_rust_with_state(expr, true),
        }
    }

    pub(in crate::emit) fn expand_operators(&self, expr: &Expr) -> Expr {
        let mut expander = super::ExpandOperatorsCodegen::new(
            &self.module_env,
            &self.state_vars,
            &self.module_name,
        );
        expander.env.push(self.op_defs.clone());
        expander.fold_expr(Spanned::dummy(expr.clone())).node
    }
}
