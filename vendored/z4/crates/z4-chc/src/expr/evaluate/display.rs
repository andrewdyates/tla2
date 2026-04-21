// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB display formatting for CHC expressions.
//!
//! Implements `fmt::Display` for `ChcExpr`, producing SMT-LIB2 S-expression syntax.

use std::fmt;

use super::super::{maybe_grow_expr_stack, ChcExpr, ChcOp};

impl fmt::Display for ChcExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Intentionally no depth bail-out: SMT-LIB rendering should remain exact;
        // stack growth is handled by `maybe_grow_expr_stack`.
        maybe_grow_expr_stack(|| match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{n}"),
            Self::Real(n, d) => write!(f, "{n}/{d}"),
            Self::BitVec(val, width) => write!(f, "(_ bv{val} {width})"),
            Self::Var(v) => write!(f, "{v}"),
            Self::PredicateApp(name, id, args) => {
                write!(f, "({name}#{}", id.index())?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            Self::FuncApp(name, sort, args) => {
                write!(f, "({name}:{sort}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            Self::Op(op, args) => {
                // Indexed BV ops use (_ op N) syntax
                match op {
                    ChcOp::BvExtract(hi, lo) => {
                        write!(f, "((_ extract {hi} {lo})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvZeroExtend(n) => {
                        write!(f, "((_ zero_extend {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvSignExtend(n) => {
                        write!(f, "((_ sign_extend {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvRotateLeft(n) => {
                        write!(f, "((_ rotate_left {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvRotateRight(n) => {
                        write!(f, "((_ rotate_right {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvRepeat(n) => {
                        write!(f, "((_ repeat {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::Int2Bv(w) => {
                        write!(f, "((_ int2bv {w})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    _ => {}
                }
                let op_str = match op {
                    ChcOp::Not => "not",
                    ChcOp::And => "and",
                    ChcOp::Or => "or",
                    ChcOp::Implies => "=>",
                    ChcOp::Iff => "iff",
                    ChcOp::Add => "+",
                    ChcOp::Sub => "-",
                    ChcOp::Mul => "*",
                    ChcOp::Div => "div",
                    ChcOp::Mod => "mod",
                    ChcOp::Neg => "-",
                    ChcOp::Eq => "=",
                    ChcOp::Ne => "distinct",
                    ChcOp::Lt => "<",
                    ChcOp::Le => "<=",
                    ChcOp::Gt => ">",
                    ChcOp::Ge => ">=",
                    ChcOp::Ite => "ite",
                    ChcOp::Select => "select",
                    ChcOp::Store => "store",
                    ChcOp::BvAdd => "bvadd",
                    ChcOp::BvSub => "bvsub",
                    ChcOp::BvMul => "bvmul",
                    ChcOp::BvUDiv => "bvudiv",
                    ChcOp::BvURem => "bvurem",
                    ChcOp::BvSDiv => "bvsdiv",
                    ChcOp::BvSRem => "bvsrem",
                    ChcOp::BvSMod => "bvsmod",
                    ChcOp::BvAnd => "bvand",
                    ChcOp::BvOr => "bvor",
                    ChcOp::BvXor => "bvxor",
                    ChcOp::BvNand => "bvnand",
                    ChcOp::BvNor => "bvnor",
                    ChcOp::BvXnor => "bvxnor",
                    ChcOp::BvNot => "bvnot",
                    ChcOp::BvNeg => "bvneg",
                    ChcOp::BvShl => "bvshl",
                    ChcOp::BvLShr => "bvlshr",
                    ChcOp::BvAShr => "bvashr",
                    ChcOp::BvULt => "bvult",
                    ChcOp::BvULe => "bvule",
                    ChcOp::BvUGt => "bvugt",
                    ChcOp::BvUGe => "bvuge",
                    ChcOp::BvSLt => "bvslt",
                    ChcOp::BvSLe => "bvsle",
                    ChcOp::BvSGt => "bvsgt",
                    ChcOp::BvSGe => "bvsge",
                    ChcOp::BvComp => "bvcomp",
                    ChcOp::BvConcat => "concat",
                    ChcOp::Bv2Nat => "bv2nat",
                    // Indexed ops handled above; fallback for new variants (#6091)
                    other => {
                        write!(f, "({other:?}")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                };
                write!(f, "({op_str}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            Self::ConstArrayMarker(_) => write!(f, "(as const)"),
            Self::IsTesterMarker(name) => write!(f, "(_ is {name})"),
            Self::ConstArray(key_sort, val) => {
                // Output in SMT-LIB2 format for constant arrays
                write!(f, "((as const (Array {key_sort} {})) {})", val.sort(), val)
            }
        })
    }
}
