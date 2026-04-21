// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! SMT-LIB2 formatting for [`Constraint`].

use super::Constraint;
use crate::format_symbol;
use crate::sort::Sort;
use std::fmt::{self, Display, Formatter};

/// Write a space-separated list of sorts in parentheses.
fn write_sort_list(f: &mut Formatter<'_>, sorts: &[Sort]) -> fmt::Result {
    write!(f, "(")?;
    for (i, sort) in sorts.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        write!(f, "{sort}")?;
    }
    write!(f, ")")
}

/// Format core SMT commands (declarations, assertions, control flow).
fn fmt_core(constraint: &Constraint, f: &mut Formatter<'_>) -> fmt::Result {
    match constraint {
        Constraint::DeclareConst { name, sort } => {
            write!(f, "(declare-const {} {})", format_symbol(name), sort)
        }
        Constraint::DeclareFun {
            name,
            arg_sorts,
            return_sort,
        } => {
            write!(f, "(declare-fun {} ", format_symbol(name))?;
            write_sort_list(f, arg_sorts)?;
            write!(f, " {return_sort})")
        }
        Constraint::DeclareDatatype(dt) => {
            write!(f, "(declare-datatype {} (", format_symbol(&dt.name))?;
            for (i, cons) in dt.constructors.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "({}", format_symbol(&cons.name))?;
                for field in &cons.fields {
                    write!(f, " ({} {})", format_symbol(&field.name), field.sort)?;
                }
                write!(f, ")")?;
            }
            write!(f, "))")
        }
        Constraint::Assert { expr, label: None } => write!(f, "(assert {expr})"),
        Constraint::Assert {
            expr,
            label: Some(name),
        } => write!(f, "(assert (! {} :named {}))", expr, format_symbol(name)),
        Constraint::SoftAssert {
            expr,
            weight,
            group: None,
        } => write!(f, "(assert-soft {expr} :weight {weight})"),
        Constraint::SoftAssert {
            expr,
            weight,
            group: Some(g),
        } => write!(
            f,
            "(assert-soft {} :weight {} :id {})",
            expr,
            weight,
            format_symbol(g)
        ),
        Constraint::Push => write!(f, "(push)"),
        Constraint::Pop(levels) => write!(f, "(pop {levels})"),
        Constraint::CheckSat => write!(f, "(check-sat)"),
        Constraint::CheckSatAssuming(assumptions) => {
            write!(f, "(check-sat-assuming (")?;
            for (i, a) in assumptions.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{a}")?;
            }
            write!(f, "))")
        }
        Constraint::GetModel => write!(f, "(get-model)"),
        Constraint::GetValue(exprs) => {
            write!(f, "(get-value (")?;
            for (i, e) in exprs.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{e}")?;
            }
            write!(f, "))")
        }
        Constraint::GetUnsatCore => write!(f, "(get-unsat-core)"),
        Constraint::SetOption { name, value } => write!(f, "(set-option :{name} {value})"),
        Constraint::SetLogic(logic) => write!(f, "(set-logic {logic})"),
        Constraint::Exit => write!(f, "(exit)"),
        _ => unreachable!(),
    }
}

/// Format CHC and OMT commands.
fn fmt_chc_omt(constraint: &Constraint, f: &mut Formatter<'_>) -> fmt::Result {
    match constraint {
        Constraint::DeclareRel { name, arg_sorts } => {
            write!(f, "(declare-rel {} ", format_symbol(name))?;
            write_sort_list(f, arg_sorts)?;
            write!(f, ")")
        }
        Constraint::Rule {
            head: Some(head),
            body,
        } => write!(f, "(rule (=> {body} {head}))"),
        Constraint::Rule { head: None, body } => write!(f, "(rule {body})"),
        Constraint::Query(rel) => write!(f, "(query {rel})"),
        Constraint::DeclareVar { name, sort } => {
            write!(f, "(declare-var {} {})", format_symbol(name), sort)
        }
        Constraint::Maximize(expr) => write!(f, "(maximize {expr})"),
        Constraint::Minimize(expr) => write!(f, "(minimize {expr})"),
        Constraint::GetObjectives => write!(f, "(get-objectives)"),
        _ => unreachable!(),
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::DeclareRel { .. }
            | Self::Rule { .. }
            | Self::Query(_)
            | Self::DeclareVar { .. }
            | Self::Maximize(_)
            | Self::Minimize(_)
            | Self::GetObjectives => fmt_chc_omt(self, f),
            _ => fmt_core(self, f),
        }
    }
}
