// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Datatype operations for Z4 expressions.
//!
//! Provides constructors, field selectors, and constructor testers for
//! algebraic datatypes (structs and enums).

use crate::sort::Sort;
use std::sync::Arc;

use super::{Expr, ExprValue};

impl Expr {
    // ===== Datatype Operations =====

    /// Create a datatype constructor application.
    ///
    /// Used to construct instances of algebraic datatypes (structs, enums).
    ///
    /// # Arguments
    /// * `constructor_name` - The constructor name (e.g., "Point_mk" for struct, "Some" for Option)
    /// * `args` - Arguments to the constructor (field values)
    /// * `result_sort` - The datatype sort of the resulting expression
    ///
    /// # Example
    /// ```rust
    /// use z4_bindings::{Expr, Sort};
    ///
    /// // Construct a Point struct: (Point_mk 1 2)
    /// // Note: Sort::struct_type uses "{name}_mk" as the constructor name
    /// let point = Expr::datatype_constructor(
    ///     "Point",
    ///     "Point_mk",
    ///     vec![Expr::bitvec_const(1i32, 32), Expr::bitvec_const(2i32, 32)],
    ///     Sort::struct_type("Point", [("x", Sort::bv32()), ("y", Sort::bv32())]),
    /// );
    /// ```
    #[must_use]
    #[cfg_attr(kani, kani::requires(result_sort.is_datatype()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_datatype()))]
    pub fn datatype_constructor(
        datatype_name: impl Into<String>,
        constructor_name: impl Into<String>,
        args: Vec<Self>,
        result_sort: Sort,
    ) -> Self {
        Self::try_datatype_constructor(datatype_name, constructor_name, args, result_sort)
            .expect("datatype_constructor requires Datatype sort")
    }

    /// Select a field from a datatype expression.
    ///
    /// Used to access fields of algebraic datatypes (struct fields, enum variant data).
    ///
    /// # Arguments
    /// * `selector_name` - The selector name (must match field name in datatype declaration)
    /// * `result_sort` - The sort of the selected field
    ///
    /// # Example
    /// ```rust
    /// use z4_bindings::{Expr, Sort};
    ///
    /// // Select x field from Point: (x p)
    /// // Note: Selector names match field names ("x", not "get-x" or "get-Point-x")
    /// let point_sort =
    ///     Sort::struct_type("Point", [("x", Sort::bv32()), ("y", Sort::bv32())]);
    /// let point_expr = Expr::var("p", point_sort);
    /// let x = point_expr.field_select("Point", "x", Sort::bv32());
    /// ```
    #[must_use]
    #[cfg_attr(kani, kani::requires(self.sort.is_datatype()))]
    pub fn field_select(
        self,
        datatype_name: impl Into<String>,
        selector_name: impl Into<String>,
        result_sort: Sort,
    ) -> Self {
        self.try_field_select(datatype_name, selector_name, result_sort)
            .expect("field_select requires Datatype sort")
    }

    /// Test if an expression matches a specific constructor.
    ///
    /// Returns true if the expression was created with the named constructor.
    /// Used for enum variant matching.
    ///
    /// # Example
    /// ```rust
    /// use z4_bindings::{Expr, Sort};
    ///
    /// // Test if option is Some: ((_ is Some) opt)
    /// let option_sort = Sort::enum_type(
    ///     "Option",
    ///     vec![
    ///         ("Some", vec![("value", Sort::int())]),
    ///         ("None", vec![]),
    ///     ],
    /// );
    /// let option_expr = Expr::var("opt", option_sort);
    /// let is_some = option_expr.is_constructor("Option", "Some");
    /// ```
    #[cfg_attr(kani, kani::requires(self.sort.is_datatype()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn is_constructor(
        self,
        datatype_name: impl Into<String>,
        constructor_name: impl Into<String>,
    ) -> Self {
        self.try_is_constructor(datatype_name, constructor_name)
            .expect("is_constructor requires Datatype sort")
    }

    // ===== Datatype try_* variants (#5818) =====

    /// Fallible datatype constructor — returns `Err` if `result_sort` is not a Datatype.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_datatype_constructor(
        datatype_name: impl Into<String>,
        constructor_name: impl Into<String>,
        args: Vec<Self>,
        result_sort: Sort,
    ) -> Result<Self, crate::SortError> {
        if !result_sort.is_datatype() {
            return Err(crate::SortError::Mismatch {
                operation: "datatype_constructor",
                expected: "Datatype sort",
                actual: result_sort.to_string(),
            });
        }
        Ok(Self {
            sort: result_sort,
            value: Arc::new(ExprValue::DatatypeConstructor {
                datatype_name: datatype_name.into(),
                constructor_name: constructor_name.into(),
                args,
            }),
        })
    }

    /// Fallible field select — returns `Err` if `self` is not a Datatype sort.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_field_select(
        self,
        datatype_name: impl Into<String>,
        selector_name: impl Into<String>,
        result_sort: Sort,
    ) -> Result<Self, crate::SortError> {
        if !self.sort.is_datatype() {
            return Err(crate::SortError::unary(
                "field_select",
                "Datatype sort",
                &self.sort,
            ));
        }
        Ok(Self {
            sort: result_sort,
            value: Arc::new(ExprValue::DatatypeSelector {
                datatype_name: datatype_name.into(),
                selector_name: selector_name.into(),
                expr: self,
            }),
        })
    }

    /// Fallible constructor tester — returns `Err` if `self` is not a Datatype sort.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_is_constructor(
        self,
        datatype_name: impl Into<String>,
        constructor_name: impl Into<String>,
    ) -> Result<Self, crate::SortError> {
        if !self.sort.is_datatype() {
            return Err(crate::SortError::unary(
                "is_constructor",
                "Datatype sort",
                &self.sort,
            ));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::DatatypeTester {
                datatype_name: datatype_name.into(),
                constructor_name: constructor_name.into(),
                expr: self,
            }),
        })
    }
}
