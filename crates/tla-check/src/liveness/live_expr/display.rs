// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::LiveExpr;

impl std::fmt::Display for LiveExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LiveExpr::Bool(true) => write!(f, "TRUE"),
            LiveExpr::Bool(false) => write!(f, "FALSE"),
            LiveExpr::StatePred { tag, .. } => write!(f, "S{}", tag),
            LiveExpr::ActionPred { tag, .. } => write!(f, "A{}", tag),
            LiveExpr::Enabled { tag, .. } => write!(f, "ENABLED({})", tag),
            LiveExpr::StateChanged { tag, .. } => write!(f, "CHANGED({})", tag),
            LiveExpr::Not(expr) => write!(f, "~{}", expr),
            LiveExpr::And(exprs) => {
                write!(f, "(")?;
                for (index, expr) in exprs.iter().enumerate() {
                    if index > 0 {
                        write!(f, " /\\ ")?;
                    }
                    write!(f, "{}", expr)?;
                }
                write!(f, ")")
            }
            LiveExpr::Or(exprs) => {
                write!(f, "(")?;
                for (index, expr) in exprs.iter().enumerate() {
                    if index > 0 {
                        write!(f, " \\/ ")?;
                    }
                    write!(f, "{}", expr)?;
                }
                write!(f, ")")
            }
            LiveExpr::Always(expr) => write!(f, "[]{}", expr),
            LiveExpr::Eventually(expr) => write!(f, "<>{}", expr),
            LiveExpr::Next(expr) => write!(f, "(){}", expr),
        }
    }
}
