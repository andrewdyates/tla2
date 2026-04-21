// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{to_snake_case, Expr, InitValue, RustEmitter, Spanned};

type CgResult = Result<(), crate::error::CodegenError>;

impl<'a> RustEmitter<'a> {
    pub(in crate::emit) fn emit_init_body(
        &mut self,
        expr: &Spanned<Expr>,
        variables: &[String],
    ) -> CgResult {
        let mut assignments = std::collections::HashMap::<String, InitValue>::new();
        let expanded = self.expand_operators(&expr.node);
        self.collect_init_assignments(&expanded, &mut assignments);

        let missing: Vec<_> = variables
            .iter()
            .filter(|v| !assignments.contains_key(*v))
            .collect();

        if !missing.is_empty() {
            self.writeln_indented("// Could not infer initial values for all variables");
            self.writeln_indented(&format!("// Missing: {:?}", missing));
            self.writeln_indented("vec![]");
            return Ok(());
        }

        let has_choice: Vec<_> = assignments
            .iter()
            .filter(|(_, v)| matches!(v, InitValue::InSet(_)))
            .map(|(k, _)| k.clone())
            .collect();

        if has_choice.is_empty() {
            self.writeln_indented("vec![Self::State {");
            self.indent += 1;
            for var in variables {
                let rust_var = to_snake_case(var);
                if let Some(value) = assignments.get(var) {
                    let value_str = self.init_value_to_rust(value);
                    self.writeln_indented(&format!("{}: {},", rust_var, value_str));
                }
            }
            self.indent -= 1;
            self.writeln_indented("}]");
        } else {
            self.writeln_indented("let mut states = Vec::new();");
            self.emit_init_loops(variables, &assignments, &has_choice, 0)?;
            self.writeln_indented("states");
        }

        Ok(())
    }

    pub(in crate::emit) fn emit_for_each_init_body(
        &mut self,
        expr: &Spanned<Expr>,
        variables: &[String],
        yield_state_fn: &str,
    ) -> CgResult {
        let mut assignments = std::collections::HashMap::<String, InitValue>::new();
        let expanded = self.expand_operators(&expr.node);
        self.collect_init_assignments(&expanded, &mut assignments);

        let missing: Vec<_> = variables
            .iter()
            .filter(|v| !assignments.contains_key(*v))
            .collect();

        if !missing.is_empty() {
            self.writeln_indented("// Could not infer initial values for all variables");
            self.writeln_indented(&format!("// Missing: {:?}", missing));
            self.writeln_indented(&format!("let _ = &mut {};", yield_state_fn));
            self.writeln_indented("std::ops::ControlFlow::Continue(())");
            return Ok(());
        }

        let has_choice: Vec<_> = assignments
            .iter()
            .filter(|(_, v)| matches!(v, InitValue::InSet(_)))
            .map(|(k, _)| k.clone())
            .collect();

        if has_choice.is_empty() {
            self.writeln_indented(&format!(
                "if let std::ops::ControlFlow::Break(()) = {}(Self::State {{",
                yield_state_fn
            ));
            self.indent += 1;
            for var in variables {
                let rust_var = to_snake_case(var);
                if let Some(value) = assignments.get(var) {
                    let value_str = self.init_value_to_rust(value);
                    self.writeln_indented(&format!("{}: {},", rust_var, value_str));
                }
            }
            self.indent -= 1;
            self.writeln_indented("}) {");
            self.indent += 1;
            self.writeln_indented("return std::ops::ControlFlow::Break(());");
            self.indent -= 1;
            self.writeln_indented("}");
        } else {
            self.emit_for_each_init_loops(variables, &assignments, &has_choice, 0, yield_state_fn)?;
        }

        self.writeln_indented("std::ops::ControlFlow::Continue(())");
        Ok(())
    }

    fn collect_init_assignments(
        &self,
        expr: &Expr,
        assignments: &mut std::collections::HashMap<String, InitValue>,
    ) {
        match expr {
            Expr::And(left, right) => {
                self.collect_init_assignments(&left.node, assignments);
                self.collect_init_assignments(&right.node, assignments);
            }
            Expr::Eq(left, right) => {
                if let Expr::Ident(name, _) = &left.node {
                    if self.state_vars.contains(name) {
                        assignments.insert(name.clone(), InitValue::Expr(right.node.clone()));
                    }
                }
            }
            Expr::In(elem, set) => {
                if let Expr::Ident(name, _) = &elem.node {
                    if self.state_vars.contains(name) {
                        assignments.insert(name.clone(), InitValue::InSet(set.node.clone()));
                    }
                }
            }
            _ => {}
        }
    }

    fn init_value_to_rust(&self, value: &InitValue) -> String {
        match value {
            InitValue::Expr(e) => self.expr_to_rust(e),
            InitValue::InSet(e) => format!("/* choose from {} */", self.expr_to_rust(e)),
        }
    }

    fn emit_init_loops(
        &mut self,
        variables: &[String],
        assignments: &std::collections::HashMap<String, InitValue>,
        choices: &[String],
        choice_idx: usize,
    ) -> CgResult {
        if choice_idx >= choices.len() {
            self.writeln_indented("states.push(Self::State {");
            self.indent += 1;
            for var in variables {
                let rust_var = to_snake_case(var);
                if choices.contains(var) {
                    self.writeln_indented(&format!("{}: {}.clone(),", rust_var, rust_var));
                } else if let Some(value) = assignments.get(var) {
                    let value_str = self.init_value_to_rust(value);
                    self.writeln_indented(&format!("{}: {},", rust_var, value_str));
                }
            }
            self.indent -= 1;
            self.writeln_indented("});");
        } else {
            let var = &choices[choice_idx];
            let rust_var = to_snake_case(var);
            if let Some(InitValue::InSet(set_expr)) = assignments.get(var) {
                let mut emit_body = |this: &mut Self| {
                    this.emit_init_loops(variables, assignments, choices, choice_idx + 1)
                };
                self.emit_init_choice_loop(&rust_var, set_expr, &mut emit_body)?;
            }
        }
        Ok(())
    }

    fn emit_for_each_init_loops(
        &mut self,
        variables: &[String],
        assignments: &std::collections::HashMap<String, InitValue>,
        choices: &[String],
        choice_idx: usize,
        yield_state_fn: &str,
    ) -> CgResult {
        if choice_idx >= choices.len() {
            self.writeln_indented(&format!(
                "if let std::ops::ControlFlow::Break(()) = {}(Self::State {{",
                yield_state_fn
            ));
            self.indent += 1;
            for var in variables {
                let rust_var = to_snake_case(var);
                if choices.contains(var) {
                    self.writeln_indented(&format!("{}: {}.clone(),", rust_var, rust_var));
                } else if let Some(value) = assignments.get(var) {
                    let value_str = self.init_value_to_rust(value);
                    self.writeln_indented(&format!("{}: {},", rust_var, value_str));
                }
            }
            self.indent -= 1;
            self.writeln_indented("}) {");
            self.indent += 1;
            self.writeln_indented("return std::ops::ControlFlow::Break(());");
            self.indent -= 1;
            self.writeln_indented("}");
        } else {
            let var = &choices[choice_idx];
            let rust_var = to_snake_case(var);
            if let Some(InitValue::InSet(set_expr)) = assignments.get(var) {
                let mut emit_body = |this: &mut Self| {
                    this.emit_for_each_init_loops(
                        variables,
                        assignments,
                        choices,
                        choice_idx + 1,
                        yield_state_fn,
                    )
                };
                self.emit_init_choice_loop(&rust_var, set_expr, &mut emit_body)?;
            }
        }
        Ok(())
    }

    fn emit_init_choice_loop(
        &mut self,
        binding: &str,
        set_expr: &Expr,
        emit_body: &mut dyn FnMut(&mut Self) -> CgResult,
    ) -> CgResult {
        match set_expr {
            Expr::SetFilter(bound, pred) => {
                let Some(domain) = &bound.domain else {
                    return self.emit_materialized_init_choice_loop(binding, set_expr, emit_body);
                };
                let loop_var = to_snake_case(&bound.name.node);
                let mut emit_filtered_body = |this: &mut Self| {
                    let pred_str = this.expr_to_rust(&pred.node);
                    this.writeln_indented(&format!("if {} {{", pred_str));
                    this.indent += 1;
                    if loop_var != binding {
                        this.writeln_indented(&format!("let {} = {}.clone();", binding, loop_var));
                    }
                    emit_body(this)?;
                    this.indent -= 1;
                    this.writeln_indented("}");
                    Ok(())
                };
                self.emit_init_choice_loop(&loop_var, &domain.node, &mut emit_filtered_body)
            }
            Expr::RecordSet(fields) if !fields.is_empty() => {
                let loop_vars: Vec<String> = (0..fields.len())
                    .map(|i| format!("__{}_field_{}", binding, i))
                    .collect();

                for ((_, domain), loop_var) in fields.iter().zip(loop_vars.iter()) {
                    let domain_str = self.expr_to_rust(&domain.node);
                    self.writeln_indented(&format!("for {} in {} {{", loop_var, domain_str));
                    self.indent += 1;
                }

                let field_entries = fields
                    .iter()
                    .zip(loop_vars.iter())
                    .map(|((name, _), loop_var)| {
                        format!("(\"{}\".to_string(), {}.clone())", name.node, loop_var)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                self.writeln_indented(&format!(
                    "let {} = TlaRecord::from_fields([{}]);",
                    binding, field_entries
                ));
                emit_body(self)?;

                for _ in fields {
                    self.indent -= 1;
                    self.writeln_indented("}");
                }
                Ok(())
            }
            _ => self.emit_materialized_init_choice_loop(binding, set_expr, emit_body),
        }
    }

    fn emit_materialized_init_choice_loop(
        &mut self,
        binding: &str,
        set_expr: &Expr,
        emit_body: &mut dyn FnMut(&mut Self) -> CgResult,
    ) -> CgResult {
        let set_str = self.expr_to_rust(set_expr);
        self.writeln_indented(&format!("for {} in {} {{", binding, set_str));
        self.indent += 1;
        emit_body(self)?;
        self.indent -= 1;
        self.writeln_indented("}");
        Ok(())
    }
}
