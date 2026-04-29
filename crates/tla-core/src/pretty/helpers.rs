// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared helpers for pretty printing bounds and parenthesization.

use super::PrettyPrinter;
use crate::ast::{BoundVar, Expr};

impl PrettyPrinter {
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
