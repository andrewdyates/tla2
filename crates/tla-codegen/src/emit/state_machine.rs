// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::util::{to_pascal_case, to_snake_case};
use super::{CgResult, RustEmitter, WRITE_TO_STRING_ERR};
use crate::types::TlaType;
use std::collections::HashSet;
use std::fmt::Write;
use tla_core::ast::Expr;
use tla_core::ast::OperatorDef;
use tla_core::NameId;

fn emitted_rust_type(ty: Option<&TlaType>) -> String {
    match ty {
        Some(TlaType::Unknown | TlaType::Var(_)) | None => "Value".to_string(),
        Some(ty) => ty.to_rust_type(),
    }
}

impl RustEmitter<'_> {
    pub(in crate::emit) fn emit_state_machine(
        &mut self,
        name: &str,
        variables: &[String],
        init_op: Option<&OperatorDef>,
        next_op: Option<&OperatorDef>,
        invariants: &[&OperatorDef],
        recursive_ops: &[&OperatorDef],
    ) -> CgResult {
        let struct_name = to_pascal_case(name);
        let state_name = format!("{}State", struct_name);

        // Generate unit struct for the state machine
        writeln!(self.out, "/// State machine for {}", name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "pub struct {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        // Implement StateMachine trait
        writeln!(self.out, "impl StateMachine for {} {{", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    type State = {};", state_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        // Init
        writeln!(self.out, "    fn init(&self) -> Vec<Self::State> {{").expect(WRITE_TO_STRING_ERR);
        self.indent = 2;
        if let Some(init) = init_op {
            self.emit_init_body(&init.body, variables)?;
        } else {
            self.writeln_indented("// No Init operator found");
            self.writeln_indented("vec![]");
        }
        self.indent = 0;
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        // for_each_init
        {
            let yield_fn = self.choose_yield_state_fn_name(variables);
            writeln!(
                self.out,
                "    fn for_each_init<F>(&self, mut {yield_fn}: F) -> std::ops::ControlFlow<()> where F: FnMut(Self::State) -> std::ops::ControlFlow<()> {{"
            )
            .expect(WRITE_TO_STRING_ERR);
            self.indent = 2;
            if let Some(init) = init_op {
                self.emit_for_each_init_body(&init.body, variables, &yield_fn)?;
            } else {
                self.writeln_indented("// No Init operator found");
                self.writeln_indented(&format!("let _ = &mut {};", yield_fn));
                self.writeln_indented("std::ops::ControlFlow::Continue(())");
            }
            self.indent = 0;
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        }

        // Next
        writeln!(
            self.out,
            "    fn next(&self, state: &Self::State) -> Vec<Self::State> {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        self.indent = 2;
        if let Some(next) = next_op {
            self.emit_next_body(&next.body, variables)?;
        } else {
            self.writeln_indented("// No Next operator found");
            self.writeln_indented("let _ = state;");
            self.writeln_indented("vec![]");
        }
        self.indent = 0;
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        // for_each_next
        {
            let yield_fn = self.choose_yield_state_fn_name(variables);
            writeln!(
                self.out,
                "    fn for_each_next<F>(&self, state: &Self::State, mut {yield_fn}: F) -> std::ops::ControlFlow<()> where F: FnMut(Self::State) -> std::ops::ControlFlow<()> {{"
            )
            .expect(WRITE_TO_STRING_ERR);
            self.indent = 2;
            if let Some(next) = next_op {
                self.emit_for_each_next_body(&next.body, variables, &yield_fn)?;
            } else {
                self.writeln_indented("// No Next operator found");
                self.writeln_indented(&format!("let _ = (state, &mut {});", yield_fn));
                self.writeln_indented("std::ops::ControlFlow::Continue(())");
            }
            self.indent = 0;
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        }

        // is_next
        {
            let var_set: HashSet<String> = variables.iter().cloned().collect();
            let supported = next_op
                .map(|op| Self::is_next_supported_prime_uses(&op.body.node, &var_set))
                .unwrap_or(false);
            if supported {
                writeln!(
                    self.out,
                    "    fn is_next(&self, old: &Self::State, new: &Self::State) -> Option<bool> {{"
                )
                .expect(WRITE_TO_STRING_ERR);
                self.emit_is_next_method(
                    next_op.expect("supported implies next_op exists"),
                    variables,
                )?;
                writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
                writeln!(self.out).expect(WRITE_TO_STRING_ERR);
            }
        }

        // Invariants
        if !invariants.is_empty() {
            // invariant_names
            writeln!(
                self.out,
                "    fn invariant_names(&self) -> Vec<&'static str> {{"
            )
            .expect(WRITE_TO_STRING_ERR);
            let names_str: Vec<_> = invariants
                .iter()
                .map(|inv| format!("\"{}\"", inv.name.node))
                .collect();
            writeln!(self.out, "        vec![{}]", names_str.join(", "))
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);

            // check_named_invariant
            writeln!(
                self.out,
                "    fn check_named_invariant(&self, name: &str, state: &Self::State) -> Option<bool> {{"
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        match name {{").expect(WRITE_TO_STRING_ERR);
            for inv in invariants.iter() {
                writeln!(
                    self.out,
                    "            \"{}\" => Some(self.check_{}(state)),",
                    inv.name.node,
                    to_snake_case(&inv.name.node)
                )
                .expect(WRITE_TO_STRING_ERR);
            }
            writeln!(self.out, "            _ => None,").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);

            // check_invariant
            writeln!(
                self.out,
                "    fn check_invariant(&self, state: &Self::State) -> Option<bool> {{"
            )
            .expect(WRITE_TO_STRING_ERR);
            let checks: Vec<_> = invariants
                .iter()
                .map(|inv| format!("self.check_{}(state)", to_snake_case(&inv.name.node)))
                .collect();
            writeln!(self.out, "        Some({})", checks.join(" && ")).expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        }

        writeln!(self.out, "}}").expect(WRITE_TO_STRING_ERR);

        // Individual invariant check methods as inherent methods (outside trait impl)
        if !invariants.is_empty() || !recursive_ops.is_empty() {
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "impl {} {{", struct_name).expect(WRITE_TO_STRING_ERR);
            if !recursive_ops.is_empty() {
                writeln!(self.out, "    const MAX_RECURSION_DEPTH: u32 = 10000;")
                    .expect(WRITE_TO_STRING_ERR);
                writeln!(self.out).expect(WRITE_TO_STRING_ERR);
                for op in recursive_ops.iter() {
                    self.emit_recursive_helper_method(op, &state_name)?;
                    writeln!(self.out).expect(WRITE_TO_STRING_ERR);
                }
            }
            for inv in invariants.iter() {
                self.emit_invariant_method(inv, &struct_name)?;
            }
            writeln!(self.out, "}}").expect(WRITE_TO_STRING_ERR);
        }
        Ok(())
    }

    fn emit_is_next_method(&mut self, next_op: &OperatorDef, variables: &[String]) -> CgResult {
        let expanded = self.expand_operators(&next_op.body.node);
        let actions = Self::collect_actions(&expanded);

        writeln!(self.out, "        let result = false").expect(WRITE_TO_STRING_ERR);
        for action in &actions {
            let mut primed_assigns = std::collections::HashMap::<String, Expr>::new();
            let mut unchanged: HashSet<String> = HashSet::new();
            let mut guards = Vec::new();
            Self::analyze_action(action, &mut primed_assigns, &mut unchanged, &mut guards);

            let guard_parts: Vec<String> = guards
                .iter()
                .map(|g| self.expr_to_rust_with_scope(g, true, "old", Some("new")))
                .collect();

            // Build old-to-new comparison parts
            // A variable can appear in both unchanged AND primed_assigns
            // (e.g. x' = 1 /\ UNCHANGED x), so both constraints must be emitted.
            let mut comparison_parts: Vec<String> = Vec::new();
            for var in variables {
                let rust_var = to_snake_case(var);
                if unchanged.contains(var) {
                    comparison_parts.push(format!("old.{} == new.{}", rust_var, rust_var));
                }
                if let Some(expr) = primed_assigns.get(var) {
                    match expr {
                        Expr::In(_elem, set) => {
                            let new_var = Expr::Ident(var.clone(), NameId::INVALID);
                            comparison_parts.push(self.emit_membership_with_scope(
                                &new_var, &set.node, true, "new", None,
                            ));
                        }
                        _ => {
                            let value =
                                self.expr_to_rust_with_scope(expr, true, "old", Some("new"));
                            comparison_parts.push(format!("new.{} == {}", rust_var, value));
                        }
                    }
                }
            }

            let mut all_parts = guard_parts;
            all_parts.extend(comparison_parts);
            if all_parts.is_empty() {
                writeln!(self.out, "            || true").expect(WRITE_TO_STRING_ERR);
            } else {
                writeln!(self.out, "            || ({})", all_parts.join(" && "))
                    .expect(WRITE_TO_STRING_ERR);
            }
        }
        writeln!(self.out, "        ;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        Some(result)").expect(WRITE_TO_STRING_ERR);
        Ok(())
    }

    fn emit_invariant_method(&mut self, inv: &OperatorDef, struct_name: &str) -> CgResult {
        writeln!(
            self.out,
            "    fn check_{}(&self, state: &{}State) -> bool {{",
            to_snake_case(&inv.name.node),
            struct_name,
        )
        .expect(WRITE_TO_STRING_ERR);

        if inv.is_recursive {
            writeln!(
                self.out,
                "        self.{}(state, 0)",
                to_snake_case(&inv.name.node)
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
            return Ok(());
        }

        // Translate the invariant body expression
        let expanded = self.expand_operators(&inv.body.node);
        let inv_expr = self.expr_to_rust_with_state(&expanded, true);
        writeln!(self.out, "        {}", inv_expr).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        Ok(())
    }

    fn emit_recursive_helper_method(&mut self, op: &OperatorDef, state_name: &str) -> CgResult {
        let fn_name = to_snake_case(&op.name.node);
        let needs_state = self.recursive_helpers_needing_state.contains(&op.name.node);
        let return_type = emitted_rust_type(self.op_types.get(&op.name.node));
        let param_types = self.op_param_types.get(&op.name.node);

        let mut params = Vec::new();
        if needs_state {
            params.push(format!("state: &{state_name}"));
        }
        for (idx, param) in op.params.iter().enumerate() {
            let param_type = emitted_rust_type(param_types.and_then(|types| types.get(idx)));
            params.push(format!(
                "{}: &{}",
                to_snake_case(&param.name.node),
                param_type
            ));
        }
        params.push("__depth: u32".to_string());

        writeln!(
            self.out,
            "    fn {fn_name}(&self, {}) -> {return_type} {{",
            params.join(", ")
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        if __depth > Self::MAX_RECURSION_DEPTH {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            panic!(\"recursive operator {} exceeded max recursion depth {{}}\", Self::MAX_RECURSION_DEPTH);",
            op.name.node
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
        for param in &op.params {
            let name = to_snake_case(&param.name.node);
            writeln!(self.out, "        let {name} = {name}.clone();").expect(WRITE_TO_STRING_ERR);
        }

        let expanded = self.expand_operators(&op.body.node);
        let prev_recursive = self.in_recursive_helper.replace(true);
        let body = self.expr_to_rust_with_scope(&expanded, needs_state, "state", None);
        self.in_recursive_helper.set(prev_recursive);
        writeln!(self.out, "        let __r = {body};").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        __r").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        Ok(())
    }
}
