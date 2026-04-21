// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof structure formatting for the width-aware TLA+ formatter.

use super::formatter::FormattingPrinter;
use crate::ast::{Proof, ProofHint, ProofStep, ProofStepKind};

impl<'c> FormattingPrinter<'c> {
    pub(super) fn print_proof(&mut self, proof: &Proof) {
        match proof {
            Proof::By(hints) => {
                self.write("BY ");
                self.print_proof_hints(hints);
            }
            Proof::Obvious => {
                self.write("OBVIOUS");
            }
            Proof::Omitted => {
                self.write("OMITTED");
            }
            Proof::Steps(steps) => {
                for step in steps {
                    self.print_proof_step(step);
                }
            }
        }
    }

    fn print_proof_hints(&mut self, hints: &[ProofHint]) {
        for (i, hint) in hints.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            match hint {
                ProofHint::Ref(r) => {
                    self.write(&r.node);
                }
                ProofHint::Def(names) => {
                    self.write("DEF ");
                    for (j, name) in names.iter().enumerate() {
                        if j > 0 {
                            self.write(", ");
                        }
                        self.write(&name.node);
                    }
                }
                ProofHint::Module(m) => {
                    self.write("MODULE ");
                    self.write(&m.node);
                }
            }
        }
    }

    fn print_proof_step(&mut self, step: &ProofStep) {
        self.write_indent();

        self.write("<");
        self.write(&step.level.to_string());
        self.write(">");

        if let Some(label) = &step.label {
            self.write(&label.node);
            self.write(". ");
        } else {
            self.write(" ");
        }

        match &step.kind {
            ProofStepKind::Assert(expr, proof) => {
                self.print_expr(&expr.node);
                if let Some(p) = proof {
                    self.newline();
                    self.indent();
                    self.write_indent();
                    self.print_proof(&p.node);
                    self.dedent();
                }
            }
            ProofStepKind::Suffices(expr, proof) => {
                self.write("SUFFICES ");
                self.print_expr(&expr.node);
                if let Some(p) = proof {
                    self.newline();
                    self.indent();
                    self.write_indent();
                    self.print_proof(&p.node);
                    self.dedent();
                }
            }
            ProofStepKind::Have(expr) => {
                self.write("HAVE ");
                self.print_expr(&expr.node);
            }
            ProofStepKind::Take(bounds) => {
                self.write("TAKE ");
                self.print_bounds(bounds);
            }
            ProofStepKind::Witness(exprs) => {
                self.write("WITNESS ");
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(&expr.node);
                }
            }
            ProofStepKind::Pick(bounds, pred, proof) => {
                self.write("PICK ");
                self.print_bounds(bounds);
                self.write(" : ");
                self.print_expr(&pred.node);
                if let Some(p) = proof {
                    self.newline();
                    self.indent();
                    self.write_indent();
                    self.print_proof(&p.node);
                    self.dedent();
                }
            }
            ProofStepKind::UseOrHide { use_, facts } => {
                if *use_ {
                    self.write("USE ");
                } else {
                    self.write("HIDE ");
                }
                self.print_proof_hints(facts);
            }
            ProofStepKind::Define(defs) => {
                self.write("DEFINE ");
                for (i, def) in defs.iter().enumerate() {
                    if i > 0 {
                        self.newline();
                        self.write_indent();
                        self.write("       ");
                    }
                    self.print_operator_def_inline(def);
                }
            }
            ProofStepKind::Qed(proof) => {
                self.write("QED");
                if let Some(p) = proof {
                    self.newline();
                    self.indent();
                    self.write_indent();
                    self.print_proof(&p.node);
                    self.dedent();
                }
            }
        }
        self.newline();
    }
}
