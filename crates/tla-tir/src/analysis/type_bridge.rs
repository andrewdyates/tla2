// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bridge from shared TIR type analysis to consumer-specific representations.
//!
//! The JIT compiler needs memory layout descriptors (byte offsets, slot counts).
//! The code generator needs Rust type name strings. Both start from the same
//! [`TirType`] produced by the shared type analysis in [`super::type_inference`].
//!
//! This module provides:
//!
//! - [`TirTypeToLayout`]: Convert `TirType` to a layout descriptor for JIT.
//! - [`TirTypeToRust`]: Convert `TirType` to Rust type name strings for codegen.
//! - [`TirTypeAnalysis`]: Unified entry point that runs shared analysis and
//!   provides extension points for both consumers.
//!
//! Part of #3930.

use crate::types::TirType;
use tla_core::NameId;

// ============================================================================
// Layout descriptors (JIT consumer)
// ============================================================================

/// Memory layout classification for the JIT compiler.
///
/// This is the `tla-tir`-level equivalent of `CompoundLayout` from `tla-jit`.
/// The JIT crate can convert this to its own `CompoundLayout` without the
/// `tla-tir` crate depending on `tla-jit`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TirLayout {
    /// Scalar integer — 1 slot.
    Int,
    /// Scalar boolean — 1 slot.
    Bool,
    /// Interned string — 1 slot (NameId).
    Str,
    /// Record with known field names and per-field layouts.
    Record { fields: Vec<(NameId, TirLayout)> },
    /// Sequence with homogeneous element layout.
    Seq { element: Box<TirLayout> },
    /// Finite set with homogeneous element layout.
    Set { element: Box<TirLayout> },
    /// Function with key and value layouts.
    Func {
        key: Box<TirLayout>,
        value: Box<TirLayout>,
    },
    /// Tuple with per-position layouts.
    Tuple { elements: Vec<TirLayout> },
    /// Dynamic — type not statically known.
    Dynamic,
}

impl TirLayout {
    /// Whether this is a scalar type (Int, Bool, or Str).
    #[must_use]
    pub fn is_scalar(&self) -> bool {
        matches!(self, TirLayout::Int | TirLayout::Bool | TirLayout::Str)
    }

    /// Compute the fixed serialized size in i64 slots, if statically known.
    ///
    /// Scalar types use 2 slots (tag + value). Records and tuples with
    /// all-fixed-size fields can be computed. Dynamic or variable-length
    /// types return `None`.
    #[must_use]
    pub fn fixed_slot_count(&self) -> Option<usize> {
        match self {
            TirLayout::Int | TirLayout::Bool | TirLayout::Str => Some(2),
            TirLayout::Record { fields } => {
                let mut total = 2; // tag + field_count
                for (_, fl) in fields {
                    total += 1; // name_id slot
                    total += fl.fixed_slot_count()?;
                }
                Some(total)
            }
            TirLayout::Tuple { elements } => {
                let mut total = 2; // tag + element_count
                for el in elements {
                    total += el.fixed_slot_count()?;
                }
                Some(total)
            }
            TirLayout::Seq { .. }
            | TirLayout::Set { .. }
            | TirLayout::Func { .. }
            | TirLayout::Dynamic => None,
        }
    }
}

/// Convert a [`TirType`] to a [`TirLayout`] descriptor.
///
/// This is a pure function that maps the gradual type lattice to memory
/// layout descriptors. `Dyn` and `Var` types map to `Dynamic`.
#[must_use]
pub fn tir_type_to_layout(ty: &TirType) -> TirLayout {
    match ty {
        TirType::Int => TirLayout::Int,
        TirType::Bool => TirLayout::Bool,
        TirType::Str => TirLayout::Str,
        TirType::Record(fields) => TirLayout::Record {
            fields: fields
                .iter()
                .map(|(nid, ft)| (*nid, tir_type_to_layout(ft)))
                .collect(),
        },
        TirType::OpenRecord(fields, _) => TirLayout::Record {
            fields: fields
                .iter()
                .map(|(nid, ft)| (*nid, tir_type_to_layout(ft)))
                .collect(),
        },
        TirType::Seq(inner) => TirLayout::Seq {
            element: Box::new(tir_type_to_layout(inner)),
        },
        TirType::Set(inner) => TirLayout::Set {
            element: Box::new(tir_type_to_layout(inner)),
        },
        TirType::Func(d, r) => TirLayout::Func {
            key: Box::new(tir_type_to_layout(d)),
            value: Box::new(tir_type_to_layout(r)),
        },
        TirType::Tuple(elems) => TirLayout::Tuple {
            elements: elems.iter().map(tir_type_to_layout).collect(),
        },
        TirType::Dyn | TirType::Var(_) | TirType::Variant(_) => TirLayout::Dynamic,
    }
}

// ============================================================================
// Rust type strings (codegen consumer)
// ============================================================================

/// Convert a [`TirType`] to a Rust type name string for code generation.
///
/// This produces the same strings as `TlaType::to_rust_type()` in the codegen
/// crate, but works directly from `TirType` so the codegen crate doesn't need
/// to re-infer types from the AST.
#[must_use]
pub fn tir_type_to_rust(ty: &TirType) -> String {
    match ty {
        TirType::Bool => "bool".to_string(),
        TirType::Int => "i64".to_string(),
        TirType::Str => "String".to_string(),
        TirType::Set(inner) => format!("TlaSet<{}>", tir_type_to_rust(inner)),
        TirType::Seq(inner) => format!("Vec<{}>", tir_type_to_rust(inner)),
        TirType::Func(d, r) => {
            format!("TlaFunc<{}, {}>", tir_type_to_rust(d), tir_type_to_rust(r))
        }
        TirType::Tuple(elems) => {
            let types: Vec<_> = elems.iter().map(|e| tir_type_to_rust(e)).collect();
            format!("({})", types.join(", "))
        }
        TirType::Record(fields) if !fields.is_empty() => {
            // Heterogeneous records need struct codegen; use tuple as fallback.
            let types: Vec<_> = fields.iter().map(|(_, t)| tir_type_to_rust(t)).collect();
            format!("({})", types.join(", "))
        }
        TirType::OpenRecord(fields, _) if !fields.is_empty() => {
            let types: Vec<_> = fields.iter().map(|(_, t)| tir_type_to_rust(t)).collect();
            format!("({})", types.join(", "))
        }
        TirType::Variant(_) => "Value".to_string(),
        TirType::Var(_) | TirType::Dyn => "Value".to_string(),
        TirType::Record(_) | TirType::OpenRecord(_, _) => "()".to_string(),
    }
}

// ============================================================================
// Unified analysis entry point
// ============================================================================

use super::type_inference::{analyze_expr, TirTypeInfo};
use tla_core::Spanned;
use crate::nodes::TirExpr;

/// Unified type analysis result that provides both JIT and codegen views.
///
/// Wraps the shared [`TirTypeInfo`] with convenience methods for both
/// consumers.
#[derive(Debug, Clone)]
pub struct TirTypeAnalysis {
    /// The underlying shared type info from the single-pass analysis.
    info: TirTypeInfo,
}

impl TirTypeAnalysis {
    /// Run shared type analysis on a TIR expression.
    #[must_use]
    pub fn analyze(expr: &Spanned<TirExpr>) -> Self {
        TirTypeAnalysis {
            info: analyze_expr(expr),
        }
    }

    /// Access the underlying shared type info.
    #[must_use]
    pub fn info(&self) -> &TirTypeInfo {
        &self.info
    }

    /// Get the JIT layout descriptor for the result type.
    #[must_use]
    pub fn result_layout(&self) -> TirLayout {
        tir_type_to_layout(self.info.result_type())
    }

    /// Get the Rust type name for the result type (for codegen).
    #[must_use]
    pub fn result_rust_type(&self) -> String {
        tir_type_to_rust(self.info.result_type())
    }

    /// Get the JIT layout for a specific variable.
    #[must_use]
    pub fn var_layout(&self, name_id: NameId) -> TirLayout {
        self.info
            .var_type(name_id)
            .map(tir_type_to_layout)
            .unwrap_or(TirLayout::Dynamic)
    }

    /// Get the Rust type name for a specific variable (for codegen).
    #[must_use]
    pub fn var_rust_type(&self, name_id: NameId) -> String {
        self.info
            .var_type(name_id)
            .map(tir_type_to_rust)
            .unwrap_or_else(|| "Value".to_string())
    }

    /// Whether all variables are scalar (suitable for flat JIT state array).
    #[must_use]
    pub fn all_vars_scalar(&self) -> bool {
        self.info.all_vars_scalar()
    }

    /// Collect JIT layouts for all known variables.
    #[must_use]
    pub fn all_var_layouts(&self) -> Vec<(NameId, TirLayout)> {
        self.info
            .var_types()
            .iter()
            .map(|(&nid, ty)| (nid, tir_type_to_layout(ty)))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nodes::*;
    use crate::types::TirType;
    use tla_core::intern_name;
    use tla_core::span::{FileId, Span};
    use tla_value::Value;

    fn span() -> Span {
        Span::new(FileId(0), 0, 0)
    }

    fn spanned(expr: TirExpr) -> Spanned<TirExpr> {
        Spanned::new(expr, span())
    }

    fn int_const(n: i64) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::int(n),
            ty: TirType::Int,
        })
    }

    fn int_var(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::StateVar { index: 0 },
            ty: TirType::Int,
        }))
    }

    // --- TirLayout from TirType ---

    #[test]
    fn test_layout_scalar_int() {
        assert_eq!(tir_type_to_layout(&TirType::Int), TirLayout::Int);
    }

    #[test]
    fn test_layout_scalar_bool() {
        assert_eq!(tir_type_to_layout(&TirType::Bool), TirLayout::Bool);
    }

    #[test]
    fn test_layout_str() {
        assert_eq!(tir_type_to_layout(&TirType::Str), TirLayout::Str);
    }

    #[test]
    fn test_layout_set_of_int() {
        let ty = TirType::Set(Box::new(TirType::Int));
        let layout = tir_type_to_layout(&ty);
        assert_eq!(
            layout,
            TirLayout::Set {
                element: Box::new(TirLayout::Int)
            }
        );
    }

    #[test]
    fn test_layout_record() {
        let nid = intern_name("x");
        let ty = TirType::Record(vec![(nid, TirType::Int)]);
        let layout = tir_type_to_layout(&ty);
        match layout {
            TirLayout::Record { fields } => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0, nid);
                assert_eq!(fields[0].1, TirLayout::Int);
            }
            other => panic!("expected Record layout, got {other:?}"),
        }
    }

    #[test]
    fn test_layout_tuple() {
        let ty = TirType::Tuple(vec![TirType::Int, TirType::Bool]);
        let layout = tir_type_to_layout(&ty);
        assert_eq!(
            layout,
            TirLayout::Tuple {
                elements: vec![TirLayout::Int, TirLayout::Bool]
            }
        );
    }

    #[test]
    fn test_layout_func() {
        let ty = TirType::Func(Box::new(TirType::Int), Box::new(TirType::Bool));
        let layout = tir_type_to_layout(&ty);
        assert_eq!(
            layout,
            TirLayout::Func {
                key: Box::new(TirLayout::Int),
                value: Box::new(TirLayout::Bool)
            }
        );
    }

    #[test]
    fn test_layout_dyn_is_dynamic() {
        assert_eq!(tir_type_to_layout(&TirType::Dyn), TirLayout::Dynamic);
    }

    #[test]
    fn test_layout_var_is_dynamic() {
        assert_eq!(tir_type_to_layout(&TirType::Var(0)), TirLayout::Dynamic);
    }

    // --- Fixed slot counts ---

    #[test]
    fn test_fixed_slots_scalar() {
        assert_eq!(TirLayout::Int.fixed_slot_count(), Some(2));
        assert_eq!(TirLayout::Bool.fixed_slot_count(), Some(2));
        assert_eq!(TirLayout::Str.fixed_slot_count(), Some(2));
    }

    #[test]
    fn test_fixed_slots_record() {
        let nid = intern_name("f");
        let layout = TirLayout::Record {
            fields: vec![(nid, TirLayout::Int)],
        };
        // tag + field_count + name_id + (tag + value) = 2 + 1 + 2 = 5
        assert_eq!(layout.fixed_slot_count(), Some(5));
    }

    #[test]
    fn test_fixed_slots_dynamic_is_none() {
        assert_eq!(TirLayout::Dynamic.fixed_slot_count(), None);
    }

    #[test]
    fn test_fixed_slots_seq_is_none() {
        let layout = TirLayout::Seq {
            element: Box::new(TirLayout::Int),
        };
        assert_eq!(layout.fixed_slot_count(), None);
    }

    // --- Rust type strings ---

    #[test]
    fn test_rust_type_scalar() {
        assert_eq!(tir_type_to_rust(&TirType::Int), "i64");
        assert_eq!(tir_type_to_rust(&TirType::Bool), "bool");
        assert_eq!(tir_type_to_rust(&TirType::Str), "String");
    }

    #[test]
    fn test_rust_type_set() {
        let ty = TirType::Set(Box::new(TirType::Int));
        assert_eq!(tir_type_to_rust(&ty), "TlaSet<i64>");
    }

    #[test]
    fn test_rust_type_func() {
        let ty = TirType::Func(Box::new(TirType::Int), Box::new(TirType::Bool));
        assert_eq!(tir_type_to_rust(&ty), "TlaFunc<i64, bool>");
    }

    #[test]
    fn test_rust_type_tuple() {
        let ty = TirType::Tuple(vec![TirType::Int, TirType::Bool]);
        assert_eq!(tir_type_to_rust(&ty), "(i64, bool)");
    }

    #[test]
    fn test_rust_type_dyn_is_value() {
        assert_eq!(tir_type_to_rust(&TirType::Dyn), "Value");
    }

    // --- TirTypeAnalysis integration ---

    #[test]
    fn test_analysis_pure_integer_expr() {
        // x + 1
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_var("x_bridge")),
            op: TirArithOp::Add,
            right: Box::new(int_const(1)),
        });
        let analysis = TirTypeAnalysis::analyze(&expr);

        assert!(analysis.info().is_pure_integer());
        assert_eq!(analysis.result_layout(), TirLayout::Int);
        assert_eq!(analysis.result_rust_type(), "i64");
        assert!(analysis.all_vars_scalar());

        let nid = intern_name("x_bridge");
        assert_eq!(analysis.var_layout(nid), TirLayout::Int);
        assert_eq!(analysis.var_rust_type(nid), "i64");
    }

    #[test]
    fn test_analysis_unknown_var_returns_dynamic() {
        let expr = int_const(42);
        let analysis = TirTypeAnalysis::analyze(&expr);

        let unknown_nid = intern_name("nonexistent_var_bridge");
        assert_eq!(analysis.var_layout(unknown_nid), TirLayout::Dynamic);
        assert_eq!(analysis.var_rust_type(unknown_nid), "Value");
    }

    #[test]
    fn test_is_scalar() {
        assert!(TirLayout::Int.is_scalar());
        assert!(TirLayout::Bool.is_scalar());
        assert!(TirLayout::Str.is_scalar());
        assert!(!TirLayout::Dynamic.is_scalar());
        assert!(!TirLayout::Set {
            element: Box::new(TirLayout::Int)
        }
        .is_scalar());
    }
}
