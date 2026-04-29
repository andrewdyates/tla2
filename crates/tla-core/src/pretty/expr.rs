// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expression pretty printing.

use super::PrettyPrinter;
use crate::ast::{ExceptPathElement, Expr, ModuleTarget};

impl PrettyPrinter {
    pub(crate) fn print_expr(&mut self, expr: &Expr) {
        match expr {
            // Literals
            Expr::Bool(b) => {
                self.write(if *b { "TRUE" } else { "FALSE" });
            }
            Expr::Int(n) => {
                self.write(&n.to_string());
            }
            Expr::String(s) => {
                self.write("\"");
                for c in s.chars() {
                    match c {
                        '"' => self.write("\\\""),
                        '\\' => self.write("\\\\"),
                        '\n' => self.write("\\n"),
                        '\t' => self.write("\\t"),
                        _ => self.push_char(c),
                    }
                }
                self.write("\"");
            }

            // Names
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                self.write(name);
            }

            // Operators
            Expr::Apply(op, args) => {
                self.print_expr(&op.node);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(&arg.node);
                }
                self.write(")");
            }
            Expr::OpRef(name) => {
                self.write(name);
            }
            Expr::Lambda(params, body) => {
                self.write("LAMBDA ");
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&param.node);
                }
                self.write(" : ");
                self.print_expr(&body.node);
            }
            Expr::Label(label) => {
                self.write(&label.name.node);
                self.write(":: ");
                self.print_expr(&label.body.node);
            }
            Expr::ModuleRef(module_target, op, args) => {
                match module_target {
                    ModuleTarget::Named(name) => {
                        self.write(name);
                    }
                    ModuleTarget::Parameterized(name, params) => {
                        self.write(name);
                        self.write("(");
                        for (i, param) in params.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.print_expr(&param.node);
                        }
                        self.write(")");
                    }
                    ModuleTarget::Chained(base) => {
                        self.print_expr(&base.node);
                    }
                }
                self.write("!");
                self.write(op);
                if !args.is_empty() {
                    self.write("(");
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.print_expr(&arg.node);
                    }
                    self.write(")");
                }
            }
            Expr::InstanceExpr(module, substitutions) => {
                self.write("INSTANCE ");
                self.write(module);
                if !substitutions.is_empty() {
                    self.write(" WITH ");
                    for (i, sub) in substitutions.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.write(&sub.from.node);
                        self.write(" <- ");
                        self.print_expr(&sub.to.node);
                    }
                }
            }

            // Logic
            Expr::And(left, right) => {
                self.print_binop(&left.node, " /\\ ", &right.node);
            }
            Expr::Or(left, right) => {
                self.print_binop(&left.node, " \\/ ", &right.node);
            }
            Expr::Not(e) => {
                self.write("~");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }
            Expr::Implies(left, right) => {
                self.print_binop(&left.node, " => ", &right.node);
            }
            Expr::Equiv(left, right) => {
                self.print_binop(&left.node, " <=> ", &right.node);
            }

            // Quantifiers
            Expr::Forall(bounds, body) => {
                self.write("\\A ");
                self.print_bounds(bounds);
                self.write(" : ");
                self.print_expr(&body.node);
            }
            Expr::Exists(bounds, body) => {
                self.write("\\E ");
                self.print_bounds(bounds);
                self.write(" : ");
                self.print_expr(&body.node);
            }
            Expr::Choose(bound, body) => {
                self.write("CHOOSE ");
                self.print_bound(bound);
                self.write(" : ");
                self.print_expr(&body.node);
            }

            // Sets
            Expr::SetEnum(elems) => {
                self.write("{");
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(&elem.node);
                }
                self.write("}");
            }
            Expr::SetBuilder(body, bounds) => {
                self.write("{");
                self.print_expr(&body.node);
                self.write(" : ");
                self.print_bounds(bounds);
                self.write("}");
            }
            Expr::SetFilter(bound, pred) => {
                self.write("{");
                self.print_bound(bound);
                self.write(" : ");
                self.print_expr(&pred.node);
                self.write("}");
            }
            Expr::In(left, right) => {
                self.print_binop(&left.node, " \\in ", &right.node);
            }
            Expr::NotIn(left, right) => {
                self.print_binop(&left.node, " \\notin ", &right.node);
            }
            Expr::Subseteq(left, right) => {
                self.print_binop(&left.node, " \\subseteq ", &right.node);
            }
            Expr::Union(left, right) => {
                self.print_binop(&left.node, " \\cup ", &right.node);
            }
            Expr::Intersect(left, right) => {
                self.print_binop(&left.node, " \\cap ", &right.node);
            }
            Expr::SetMinus(left, right) => {
                self.print_binop(&left.node, " \\ ", &right.node);
            }
            Expr::Powerset(e) => {
                self.write("SUBSET ");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }
            Expr::BigUnion(e) => {
                self.write("UNION ");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }

            // Functions
            Expr::FuncDef(bounds, body) => {
                self.write("[");
                self.print_bounds(bounds);
                self.write(" |-> ");
                self.print_expr(&body.node);
                self.write("]");
            }
            Expr::FuncApply(func, arg) => {
                self.print_expr(&func.node);
                self.write("[");
                self.print_expr(&arg.node);
                self.write("]");
            }
            Expr::Domain(e) => {
                self.write("DOMAIN ");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }
            Expr::Except(func, specs) => {
                self.write("[");
                self.print_expr(&func.node);
                self.write(" EXCEPT ");
                for (i, spec) in specs.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write("!");
                    for elem in &spec.path {
                        match elem {
                            ExceptPathElement::Index(idx) => {
                                self.write("[");
                                self.print_expr(&idx.node);
                                self.write("]");
                            }
                            ExceptPathElement::Field(f) => {
                                self.write(".");
                                self.write(&f.name.node);
                            }
                        }
                    }
                    self.write(" = ");
                    self.print_expr(&spec.value.node);
                }
                self.write("]");
            }
            Expr::FuncSet(domain, range) => {
                self.write("[");
                self.print_expr(&domain.node);
                self.write(" -> ");
                self.print_expr(&range.node);
                self.write("]");
            }

            // Records
            Expr::Record(fields) => {
                self.write("[");
                for (i, (name, val)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&name.node);
                    self.write(" |-> ");
                    self.print_expr(&val.node);
                }
                self.write("]");
            }
            Expr::RecordAccess(rec, field) => {
                self.print_expr(&rec.node);
                self.write(".");
                self.write(&field.name.node);
            }
            Expr::RecordSet(fields) => {
                self.write("[");
                for (i, (name, typ)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&name.node);
                    self.write(" : ");
                    self.print_expr(&typ.node);
                }
                self.write("]");
            }

            // Tuples
            Expr::Tuple(elems) => {
                self.write("<<");
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(&elem.node);
                }
                self.write(">>");
            }
            Expr::Times(sets) => {
                for (i, set) in sets.iter().enumerate() {
                    if i > 0 {
                        self.write(" \\X ");
                    }
                    self.print_expr(&set.node);
                }
            }

            // Temporal
            Expr::Prime(e) => {
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
                self.write("'");
            }
            Expr::Always(e) => {
                self.write("[]");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }
            Expr::Eventually(e) => {
                self.write("<>");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }
            Expr::LeadsTo(left, right) => {
                self.print_binop(&left.node, " ~> ", &right.node);
            }
            Expr::WeakFair(vars, action) => {
                self.write("WF_");
                self.print_expr(&vars.node);
                self.write("(");
                self.print_expr(&action.node);
                self.write(")");
            }
            Expr::StrongFair(vars, action) => {
                self.write("SF_");
                self.print_expr(&vars.node);
                self.write("(");
                self.print_expr(&action.node);
                self.write(")");
            }

            // Actions
            Expr::Enabled(e) => {
                self.write("ENABLED ");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }
            Expr::Unchanged(e) => {
                self.write("UNCHANGED ");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }

            // Control
            Expr::If(cond, then_e, else_e) => {
                self.write("IF ");
                self.print_expr(&cond.node);
                self.write(" THEN ");
                self.print_expr(&then_e.node);
                self.write(" ELSE ");
                self.print_expr(&else_e.node);
            }
            Expr::Case(arms, otherwise) => {
                self.write("CASE ");
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write(" [] ");
                    }
                    self.print_expr(&arm.guard.node);
                    self.write(" -> ");
                    self.print_expr(&arm.body.node);
                }
                if let Some(other) = otherwise {
                    self.write(" [] OTHER -> ");
                    self.print_expr(&other.node);
                }
            }
            Expr::Let(defs, body) => {
                self.write("LET ");
                for (i, def) in defs.iter().enumerate() {
                    if i > 0 {
                        self.newline();
                        self.write_indent();
                        self.write("    ");
                    }
                    self.print_operator_def(def, true);
                }
                self.newline();
                self.write_indent();
                self.write("IN ");
                self.print_expr(&body.node);
            }
            Expr::SubstIn(subs, body) => {
                self.write("SUBST_IN(");
                for (i, sub) in subs.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&sub.from.node);
                    self.write(" <- ");
                    self.print_expr(&sub.to.node);
                }
                self.write(" :: ");
                self.print_expr(&body.node);
                self.write(")");
            }

            // Comparison
            Expr::Eq(left, right) => {
                self.print_binop(&left.node, " = ", &right.node);
            }
            Expr::Neq(left, right) => {
                self.print_binop(&left.node, " /= ", &right.node);
            }
            Expr::Lt(left, right) => {
                self.print_binop(&left.node, " < ", &right.node);
            }
            Expr::Leq(left, right) => {
                self.print_binop(&left.node, " <= ", &right.node);
            }
            Expr::Gt(left, right) => {
                self.print_binop(&left.node, " > ", &right.node);
            }
            Expr::Geq(left, right) => {
                self.print_binop(&left.node, " >= ", &right.node);
            }

            // Arithmetic
            Expr::Add(left, right) => {
                self.print_binop(&left.node, " + ", &right.node);
            }
            Expr::Sub(left, right) => {
                self.print_binop(&left.node, " - ", &right.node);
            }
            Expr::Mul(left, right) => {
                self.print_binop(&left.node, " * ", &right.node);
            }
            Expr::Div(left, right) => {
                self.print_binop(&left.node, " / ", &right.node);
            }
            Expr::IntDiv(left, right) => {
                self.print_binop(&left.node, " \\div ", &right.node);
            }
            Expr::Mod(left, right) => {
                self.print_binop(&left.node, " % ", &right.node);
            }
            Expr::Pow(left, right) => {
                self.print_binop(&left.node, "^", &right.node);
            }
            Expr::Neg(e) => {
                self.write("-");
                self.print_expr_parens(&e.node, needs_parens(expr, &e.node));
            }
            Expr::Range(left, right) => {
                self.print_binop(&left.node, "..", &right.node);
            }
        }
    }
}

/// Determine if an expression needs parentheses in a given context
pub(super) fn needs_parens(parent: &Expr, child: &Expr) -> bool {
    match parent {
        Expr::Not(_)
        | Expr::Neg(_)
        | Expr::Prime(_)
        | Expr::Always(_)
        | Expr::Eventually(_)
        | Expr::Enabled(_)
        | Expr::Unchanged(_)
        | Expr::Powerset(_)
        | Expr::BigUnion(_)
        | Expr::Domain(_) => {
            matches!(
                child,
                Expr::And(_, _)
                    | Expr::Or(_, _)
                    | Expr::Implies(_, _)
                    | Expr::Equiv(_, _)
                    | Expr::Eq(_, _)
                    | Expr::Neq(_, _)
                    | Expr::Lt(_, _)
                    | Expr::Leq(_, _)
                    | Expr::Gt(_, _)
                    | Expr::Geq(_, _)
                    | Expr::Add(_, _)
                    | Expr::Sub(_, _)
                    | Expr::Mul(_, _)
                    | Expr::Div(_, _)
                    | Expr::In(_, _)
                    | Expr::NotIn(_, _)
            )
        }
        _ => false,
    }
}
