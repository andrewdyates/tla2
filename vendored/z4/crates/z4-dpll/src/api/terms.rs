// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term construction for Z4 Solver API.
//!
//! Variable declaration, datatypes, arrays, constants, booleans,
//! quantifiers, comparisons, arithmetic, and sort conversions.

mod arithmetic;
mod arrays;
mod boolean;
mod comparisons;
mod compat;
mod constants;
mod conversions;
mod datatypes;
mod quantifiers;

#[allow(deprecated)]
pub use compat::AstKind;

use std::collections::HashSet;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use z4_core::term::{Symbol, TermData};
use z4_core::{DatatypeSort, Sort, TermId, TermStore};
use z4_frontend::Command;

use super::types::{FuncDecl, SolverError, SortExt, Term};
use super::Solver;

// All public methods in this module are convenience wrappers that intentionally
// panic on error. Each has a fallible `try_*` counterpart.
#[allow(clippy::panic, deprecated)]
impl Solver {
    // =========================================================================
    // Variable declaration
    // =========================================================================

    /// Declare a constant (0-arity function) with the given name and sort.
    ///
    /// The `name` is used for model extraction (see [`Solver::get_model`]).
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Logic, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", Sort::Int);
    /// let y = solver.declare_const("y", Sort::Int);
    /// # let _ = (x, y);
    /// ```
    pub fn declare_const(&mut self, name: &str, sort: Sort) -> Term {
        let term_sort = sort.as_term_sort();
        let term_id = self.terms_mut().mk_var(name, term_sort.clone());
        self.var_names.insert(term_id, name.to_string());
        self.var_sorts.insert(term_id, sort);
        // Register the symbol in the context so it appears in models
        self.executor
            .context_mut()
            .register_symbol(name.to_string(), term_id, term_sort);
        Term(term_id)
    }

    /// Declare an integer constant (0-arity) variable.
    pub fn int_var(&mut self, name: &str) -> Term {
        self.declare_const(name, Sort::Int)
    }

    /// Declare a real constant (0-arity) variable.
    pub fn real_var(&mut self, name: &str) -> Term {
        self.declare_const(name, Sort::Real)
    }

    /// Declare a boolean constant (0-arity) variable.
    pub fn bool_var(&mut self, name: &str) -> Term {
        self.declare_const(name, Sort::Bool)
    }

    /// Declare a bitvector constant (0-arity) variable with the specified width.
    pub fn bv_var(&mut self, name: &str, width: u32) -> Term {
        self.declare_const(name, Sort::bitvec(width))
    }

    /// Create a fresh variable (guaranteed unique) that is *not* registered for model extraction.
    ///
    /// This is primarily useful for constructing quantified formulas, where bound variables
    /// should not appear as top-level symbols in models.
    pub fn fresh_var(&mut self, prefix: &str, sort: Sort) -> Term {
        let term_sort = sort.as_term_sort();
        Term(self.terms_mut().mk_fresh_var(prefix, term_sort))
    }

    /// Declare a function (n-arity) with the given name, domain, and range sorts.
    ///
    /// The function is registered with the SMT context so it appears in models.
    /// Use `Solver::apply` to create application terms.
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Logic, SolveResult, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfUflia);
    /// let x = solver.declare_const("x", Sort::Int);
    ///
    /// let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    /// let fx = solver.apply(&f, &[x]);
    ///
    /// let one = solver.int_const(1);
    /// let x_plus_1 = solver.add(x, one);
    /// let eq_term = solver.eq(fx, x_plus_1);
    /// solver.assert_term(eq_term);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the executor fails to declare the function. Use [`try_declare_fun`]
    /// for a fallible version that returns an error instead.
    ///
    /// [`try_declare_fun`]: Solver::try_declare_fun
    #[deprecated(note = "use try_declare_fun() which returns Result instead of panicking")]
    pub fn declare_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        self.try_declare_fun(name, domain, range)
            .unwrap_or_else(|e| panic!("Failed to declare function '{name}': {e}"))
    }

    /// Try to declare a function (n-arity) with the given name, domain, and range sorts.
    ///
    /// Fallible version of [`declare_fun`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to declare the function.
    ///
    /// [`declare_fun`]: Solver::declare_fun
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_declare_fun(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FuncDecl, SolverError> {
        // Build the DeclareFun command to register the function with the SMT context
        let domain_sorts: Vec<_> = domain.iter().map(SortExt::to_command_sort).collect();
        let range_sort = range.to_command_sort();
        let cmd = Command::DeclareFun(name.to_string(), domain_sorts, range_sort);

        // Execute the command to register the function
        // This makes it appear in ctx.symbol_iter() for model printing
        self.executor.execute(&cmd)?;

        Ok(FuncDecl {
            name: name.to_string(),
            domain: domain.to_vec(),
            range,
        })
    }

    /// Apply a declared function to arguments, creating an application term.
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Logic, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfUflia);
    /// let x = solver.declare_const("x", Sort::Int);
    ///
    /// let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    /// let fx = solver.apply(&f, &[x]);
    /// # let _ = fx;
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The number of arguments doesn't match the function's arity
    /// - Argument sorts don't match the function's domain sorts
    ///
    /// Use [`Self::try_apply`] for a fallible version.
    #[deprecated(note = "use try_apply() which returns Result instead of panicking")]
    pub fn apply(&mut self, func: &FuncDecl, args: &[Term]) -> Term {
        self.try_apply(func, args).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`apply`](Solver::apply). Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if the number of arguments doesn't
    /// match the function's arity.
    ///
    /// Returns [`SolverError::SortMismatch`] if any argument's sort doesn't match
    /// the corresponding domain sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_apply(&mut self, func: &FuncDecl, args: &[Term]) -> Result<Term, SolverError> {
        if args.len() != func.domain.len() {
            return Err(SolverError::InvalidArgument {
                operation: "apply",
                message: format!(
                    "function {} expects {} args, got {}",
                    func.name,
                    func.domain.len(),
                    args.len()
                ),
            });
        }

        for (arg, expected_sort) in args.iter().zip(func.domain.iter()) {
            let actual_sort = self.terms().sort(arg.0).clone();
            let expected_core = expected_sort.as_term_sort();
            if actual_sort != expected_core {
                return Err(SolverError::SortMismatch {
                    operation: "apply",
                    expected: "matching domain sort",
                    got: vec![actual_sort],
                });
            }
        }

        let arg_ids: Vec<_> = args.iter().map(|t| t.0).collect();
        let result_sort = func.range.as_term_sort();
        Ok(Term(self.terms_mut().mk_app(
            Symbol::Named(func.name.clone()),
            arg_ids,
            result_sort,
        )))
    }
}
