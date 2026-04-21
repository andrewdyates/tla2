// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Width-aware expression formatting for the TLA+ formatter.
//!
//! Key TLA+ formatting conventions handled here:
//! - Conjunction lists: `/\` aligned vertically when expression is wide
//! - Disjunction lists: `\/` aligned vertically when expression is wide
//! - CASE expressions: each arm on its own line with aligned `[]`
//! - LET/IN blocks: definitions indented, IN at same level as LET
//! - IF/THEN/ELSE: multi-line when wide

use super::formatter::FormattingPrinter;
use crate::ast::{BoundVar, ExceptPathElement, Expr, ModuleTarget};

impl<'c> FormattingPrinter<'c> {
    pub(super) fn print_expr(&mut self, expr: &Expr) {
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

            // Logic - width-aware formatting for conjunction/disjunction
            Expr::And(_, _) => {
                self.print_conjunction_list(expr);
            }
            Expr::Or(_, _) => {
                self.print_disjunction_list(expr);
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

            // Control - width-aware formatting
            Expr::If(cond, then_e, else_e) => {
                self.print_if_then_else(&cond.node, &then_e.node, &else_e.node);
            }
            Expr::Case(arms, otherwise) => {
                self.print_case(arms, otherwise.as_deref());
            }
            Expr::Let(defs, body) => {
                self.print_let(defs, &body.node);
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

    // --- Width-aware formatting for conjunction and disjunction lists ---

    /// Collect a chain of And nodes into a flat list.
    pub(super) fn collect_conjuncts<'a>(&self, expr: &'a Expr) -> Vec<&'a Expr> {
        let mut conjuncts = Vec::new();
        Self::collect_conjuncts_inner(expr, &mut conjuncts);
        conjuncts
    }

    fn collect_conjuncts_inner<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
        if let Expr::And(left, right) = expr {
            Self::collect_conjuncts_inner(&left.node, out);
            Self::collect_conjuncts_inner(&right.node, out);
        } else {
            out.push(expr);
        }
    }

    /// Collect a chain of Or nodes into a flat list.
    pub(super) fn collect_disjuncts<'a>(&self, expr: &'a Expr) -> Vec<&'a Expr> {
        let mut disjuncts = Vec::new();
        Self::collect_disjuncts_inner(expr, &mut disjuncts);
        disjuncts
    }

    fn collect_disjuncts_inner<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
        if let Expr::Or(left, right) = expr {
            Self::collect_disjuncts_inner(&left.node, out);
            Self::collect_disjuncts_inner(&right.node, out);
        } else {
            out.push(expr);
        }
    }

    /// Print a conjunction list. If the total width fits on one line, print inline.
    /// Otherwise, print each conjunct on its own line with aligned `/\`.
    fn print_conjunction_list(&mut self, expr: &Expr) {
        let conjuncts = self.collect_conjuncts(expr);

        // Estimate single-line width
        let single_line_width = Self::estimate_expr_width(expr);
        let would_exceed = self.current_col() + single_line_width > self.max_width();

        if conjuncts.len() <= 2 && !would_exceed {
            // Print inline: A /\ B
            for (i, c) in conjuncts.iter().enumerate() {
                if i > 0 {
                    self.write(" /\\ ");
                }
                self.print_expr(c);
            }
        } else {
            // Print vertically aligned:
            // /\ A
            // /\ B
            // /\ C
            let base_col = self.current_col();
            for (i, c) in conjuncts.iter().enumerate() {
                if i > 0 {
                    self.newline();
                    self.write_spaces(base_col);
                }
                self.write("/\\ ");
                self.print_expr(c);
            }
        }
    }

    /// Print a disjunction list. If the total width fits on one line, print inline.
    /// Otherwise, print each disjunct on its own line with aligned `\/`.
    fn print_disjunction_list(&mut self, expr: &Expr) {
        let disjuncts = self.collect_disjuncts(expr);

        // Estimate single-line width
        let single_line_width = Self::estimate_expr_width(expr);
        let would_exceed = self.current_col() + single_line_width > self.max_width();

        if disjuncts.len() <= 2 && !would_exceed {
            // Print inline: A \/ B
            for (i, d) in disjuncts.iter().enumerate() {
                if i > 0 {
                    self.write(" \\/ ");
                }
                self.print_expr(d);
            }
        } else {
            // Print vertically aligned:
            // \/ A
            // \/ B
            // \/ C
            let base_col = self.current_col();
            for (i, d) in disjuncts.iter().enumerate() {
                if i > 0 {
                    self.newline();
                    self.write_spaces(base_col);
                }
                self.write("\\/ ");
                self.print_expr(d);
            }
        }
    }

    // --- IF/THEN/ELSE ---

    fn print_if_then_else(&mut self, cond: &Expr, then_e: &Expr, else_e: &Expr) {
        // Estimate single-line width
        let total_width = 3 /* IF */ + 1 + Self::estimate_expr_width(cond)
            + 6 /* _THEN_ */ + Self::estimate_expr_width(then_e)
            + 6 /* _ELSE_ */ + Self::estimate_expr_width(else_e);
        let would_exceed = self.current_col() + total_width > self.max_width();

        if !would_exceed {
            self.write("IF ");
            self.print_expr(cond);
            self.write(" THEN ");
            self.print_expr(then_e);
            self.write(" ELSE ");
            self.print_expr(else_e);
        } else {
            let base_col = self.current_col();
            self.write("IF ");
            self.print_expr(cond);
            self.newline();
            self.write_spaces(base_col);
            self.write("THEN ");
            self.print_expr(then_e);
            self.newline();
            self.write_spaces(base_col);
            self.write("ELSE ");
            self.print_expr(else_e);
        }
    }

    // --- CASE ---

    fn print_case(
        &mut self,
        arms: &[crate::ast::CaseArm],
        otherwise: Option<&crate::span::Spanned<Expr>>,
    ) {
        // Estimate single-line width
        let mut single_width = 5; // "CASE "
        for (i, arm) in arms.iter().enumerate() {
            if i > 0 {
                single_width += 4; // " [] "
            }
            single_width += Self::estimate_expr_width(&arm.guard.node);
            single_width += 4; // " -> "
            single_width += Self::estimate_expr_width(&arm.body.node);
        }
        if let Some(other) = otherwise {
            single_width += 4 + 5 + 4; // " [] OTHER -> "
            single_width += Self::estimate_expr_width(&other.node);
        }
        let would_exceed = self.current_col() + single_width > self.max_width();

        if !would_exceed {
            // Single line
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
        } else {
            // Multi-line: each arm on its own line
            let base_col = self.current_col();
            self.write("CASE ");
            for (i, arm) in arms.iter().enumerate() {
                if i > 0 {
                    self.newline();
                    self.write_spaces(base_col + 2); // align [] under CASE
                    self.write("[] ");
                }
                self.print_expr(&arm.guard.node);
                self.write(" -> ");
                self.print_expr(&arm.body.node);
            }
            if let Some(other) = otherwise {
                self.newline();
                self.write_spaces(base_col + 2);
                self.write("[] OTHER -> ");
                self.print_expr(&other.node);
            }
        }
    }

    // --- LET/IN ---

    fn print_let(&mut self, defs: &[crate::ast::OperatorDef], body: &Expr) {
        self.write("LET ");
        let let_indent = self.current_col();
        for (i, def) in defs.iter().enumerate() {
            if i > 0 {
                self.newline();
                self.write_spaces(let_indent);
            }
            self.print_operator_def_inline(def);
        }
        self.newline();
        // IN at same indentation as LET
        self.write_spaces(let_indent.saturating_sub(4));
        self.write("IN ");
        self.print_expr(body);
    }

    /// Print an operator def on a single line (used in LET and DEFINE).
    pub(super) fn print_operator_def_inline(&mut self, op: &crate::ast::OperatorDef) {
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
    }

    // --- Helpers ---

    pub(super) fn print_binop(&mut self, left: &Expr, op: &str, right: &Expr) {
        self.print_expr(left);
        self.write(op);
        self.print_expr(right);
    }

    pub(super) fn print_expr_parens(&mut self, expr: &Expr, parens: bool) {
        if parens {
            self.write("(");
            self.print_expr(expr);
            self.write(")");
        } else {
            self.print_expr(expr);
        }
    }

    pub(super) fn print_bounds(&mut self, bounds: &[BoundVar]) {
        for (i, bound) in bounds.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.print_bound(bound);
        }
    }

    pub(super) fn print_bound(&mut self, bound: &BoundVar) {
        self.write(&bound.name.node);
        if let Some(domain) = &bound.domain {
            self.write(" \\in ");
            self.print_expr(&domain.node);
        }
    }
}

/// Determine if an expression needs parentheses in a given context.
fn needs_parens(parent: &Expr, child: &Expr) -> bool {
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
