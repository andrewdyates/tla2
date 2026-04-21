// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Module and unit formatting for the width-aware TLA+ formatter.

use super::formatter::FormattingPrinter;
use crate::ast::{Module, OperatorDef, Unit};

/// Standard TLA+ module delimiter width.
const MODULE_DELIM_WIDTH: usize = 76;

impl<'c> FormattingPrinter<'c> {
    pub(super) fn print_module(&mut self, module: &Module) {
        // Module header: ---- MODULE Name ----
        // Standard TLA+ convention: pad dashes to fill the line
        let name = &module.name.node;
        let header_inner = format!(" MODULE {} ", name);
        let remaining = MODULE_DELIM_WIDTH.saturating_sub(header_inner.len());
        let left_dashes = remaining / 2;
        let right_dashes = remaining - left_dashes;
        for _ in 0..left_dashes.max(4) {
            self.push_char('-');
        }
        self.write(&header_inner);
        for _ in 0..right_dashes.max(4) {
            self.push_char('-');
        }
        self.newline();

        // EXTENDS
        if !module.extends.is_empty() {
            self.write("EXTENDS ");
            for (i, ext) in module.extends.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(&ext.node);
            }
            self.newline();
        }

        for unit in &module.units {
            self.newline();
            self.print_unit(&unit.node);
        }

        self.newline();
        // Closing delimiter
        for _ in 0..MODULE_DELIM_WIDTH.max(4) {
            self.push_char('=');
        }
        self.newline();
    }

    pub(super) fn print_unit(&mut self, unit: &Unit) {
        match unit {
            Unit::Variable(vars) => {
                if vars.len() == 1 {
                    self.write("VARIABLE ");
                    self.write(&vars[0].node);
                } else {
                    self.write("VARIABLES ");
                    for (i, var) in vars.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.write(&var.node);
                    }
                }
                self.newline();
            }
            Unit::Constant(consts) => {
                if consts.len() == 1 {
                    self.write("CONSTANT ");
                } else {
                    self.write("CONSTANTS ");
                }
                for (i, c) in consts.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&c.name.node);
                    if let Some(arity) = c.arity {
                        self.write("(");
                        for j in 0..arity {
                            if j > 0 {
                                self.write(", ");
                            }
                            self.write("_");
                        }
                        self.write(")");
                    }
                }
                self.newline();
            }
            Unit::Recursive(decls) => {
                self.write("RECURSIVE ");
                for (i, r) in decls.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&r.name.node);
                    if r.arity > 0 {
                        self.write("(");
                        for j in 0..r.arity {
                            if j > 0 {
                                self.write(", ");
                            }
                            self.write("_");
                        }
                        self.write(")");
                    }
                }
                self.newline();
            }
            Unit::Operator(op_def) => {
                self.print_operator_def(op_def);
            }
            Unit::Instance(inst) => {
                if inst.local {
                    self.write("LOCAL ");
                }
                self.write("INSTANCE ");
                self.write(&inst.module.node);
                if !inst.substitutions.is_empty() {
                    self.write(" WITH ");
                    for (i, sub) in inst.substitutions.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.write(&sub.from.node);
                        self.write(" <- ");
                        self.print_expr(&sub.to.node);
                    }
                }
                self.newline();
            }
            Unit::Assume(assume) => {
                self.write("ASSUME ");
                if let Some(name) = &assume.name {
                    self.write(&name.node);
                    self.write(" == ");
                }
                self.print_expr(&assume.expr.node);
                self.newline();
            }
            Unit::Theorem(thm) => {
                self.write("THEOREM ");
                if let Some(name) = &thm.name {
                    self.write(&name.node);
                    self.write(" == ");
                }
                self.print_expr(&thm.body.node);
                if let Some(proof) = &thm.proof {
                    self.newline();
                    self.print_proof(&proof.node);
                }
                self.newline();
            }
            Unit::Separator => {
                for _ in 0..MODULE_DELIM_WIDTH {
                    self.push_char('-');
                }
                self.newline();
            }
        }
    }

    /// Print an operator definition at module level with width-aware body formatting.
    pub(super) fn print_operator_def(&mut self, op: &OperatorDef) {
        if op.local {
            self.write("LOCAL ");
        }
        self.write(&op.name.node);
        if !op.params.is_empty() {
            self.write("(");
            for (i, param) in op.params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(&param.name.node);
                if param.arity > 0 {
                    self.write("(");
                    for j in 0..param.arity {
                        if j > 0 {
                            self.write(", ");
                        }
                        self.write("_");
                    }
                    self.write(")");
                }
            }
            self.write(")");
        }
        self.write(" ==");

        // Estimate body width to decide single-line vs multi-line
        let body_width = Self::estimate_expr_width(&op.body.node);
        let def_header_col = self.current_col();
        let would_exceed = def_header_col + 1 + body_width > self.max_width();

        // For conjunction/disjunction bodies, always use multi-line if they have 3+ items
        let is_long_list = match &op.body.node {
            crate::ast::Expr::And(_, _) => {
                let conjuncts = self.collect_conjuncts(&op.body.node);
                conjuncts.len() >= 3
            }
            crate::ast::Expr::Or(_, _) => {
                let disjuncts = self.collect_disjuncts(&op.body.node);
                disjuncts.len() >= 3
            }
            _ => false,
        };

        if would_exceed || is_long_list {
            // Multi-line: body indented on next line
            self.newline();
            self.indent();
            self.write_indent();
            self.print_expr(&op.body.node);
            self.dedent();
        } else {
            self.write(" ");
            self.print_expr(&op.body.node);
        }
        self.newline();
    }
}
