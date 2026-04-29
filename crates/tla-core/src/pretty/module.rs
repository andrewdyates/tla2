// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Module and unit pretty printing.

use super::PrettyPrinter;
use crate::ast::{Module, OperatorDef, Unit};

impl PrettyPrinter {
    pub(crate) fn print_module(&mut self, module: &Module) {
        self.write("---- MODULE ");
        self.write(&module.name.node);
        self.writeln(" ----");

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
        self.writeln("====");
    }

    pub(crate) fn print_unit(&mut self, unit: &Unit) {
        match unit {
            Unit::Variable(vars) => {
                self.write("VARIABLE ");
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&var.node);
                }
                self.newline();
            }
            Unit::Constant(consts) => {
                self.write("CONSTANT ");
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
                self.print_operator_def(op_def, false);
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
                self.writeln("----");
            }
        }
    }

    pub(super) fn print_operator_def(&mut self, op: &OperatorDef, in_let: bool) {
        if op.local && !in_let {
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
        self.write(" == ");
        self.print_expr(&op.body.node);
        if !in_let {
            self.newline();
        }
    }
}
