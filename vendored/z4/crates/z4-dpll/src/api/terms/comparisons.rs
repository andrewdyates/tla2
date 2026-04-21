// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create an equality (a = b).
    ///
    /// # Panics
    /// Panics if arguments have different sorts. Use [`Self::try_eq`] for a fallible version.
    #[deprecated(note = "use try_eq() which returns Result instead of panicking")]
    pub fn eq(&mut self, a: Term, b: Term) -> Term {
        self.try_eq(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`eq`](Solver::eq). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if arguments have different sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_eq(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_sort("eq", a, b)?;
        Ok(Term(self.terms_mut().mk_eq(a.0, b.0)))
    }

    /// Create a disequality (a != b).
    ///
    /// # Panics
    /// Panics if arguments have different sorts. Use [`Self::try_neq`] for a fallible version.
    #[deprecated(note = "use try_neq() which returns Result instead of panicking")]
    pub fn neq(&mut self, a: Term, b: Term) -> Term {
        self.try_neq(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`neq`](Solver::neq). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if arguments have different sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_neq(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let eq = self.try_eq(a, b)?;
        self.try_not(eq)
    }

    /// Assert that all terms are pairwise distinct (SMT-LIB `distinct`).
    ///
    /// For 0-1 terms, this returns `true`.
    /// For 2 terms, this is equivalent to `neq(a, b)`.
    /// For 3+ terms, this expands to a conjunction of pairwise disequalities.
    ///
    /// # Panics
    /// Panics if terms have different sorts. Use [`Self::try_distinct`] for a fallible version.
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Logic, SolveResult, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", Sort::Int);
    /// let y = solver.declare_const("y", Sort::Int);
    /// let distinct_xy = solver.distinct(&[x, y]);
    /// solver.assert_term(distinct_xy);
    ///
    /// // x = 1 and y = 1 violates distinctness.
    /// let one = solver.int_const(1);
    /// let x_is_1 = solver.eq(x, one);
    /// solver.assert_term(x_is_1);
    ///
    /// let one2 = solver.int_const(1);
    /// let y_is_1 = solver.eq(y, one2);
    /// solver.assert_term(y_is_1);
    ///
    /// assert_eq!(solver.check_sat(), SolveResult::Unsat);
    /// ```
    #[deprecated(note = "use try_distinct() which returns Result instead of panicking")]
    pub fn distinct(&mut self, terms: &[Term]) -> Term {
        self.try_distinct(terms).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`distinct`](Solver::distinct). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if any two terms have different sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_distinct(&mut self, terms: &[Term]) -> Result<Term, SolverError> {
        if terms.len() >= 2 {
            let first = terms[0];
            for t in &terms[1..] {
                self.expect_same_sort("distinct", first, *t)?;
            }
        }
        let ids: Vec<_> = terms.iter().map(|t| t.0).collect();
        Ok(Term(self.terms_mut().mk_distinct(ids)))
    }

    /// Create a less-than comparison (a < b). Panics if sorts don't match.
    #[deprecated(note = "use try_lt() which returns Result instead of panicking")]
    pub fn lt(&mut self, a: Term, b: Term) -> Term {
        self.try_lt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a less-than comparison (a < b). Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_lt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_arith_sort("lt", a, b)?;
        Ok(Term(self.terms_mut().mk_lt(a.0, b.0)))
    }

    /// Create a less-than-or-equal comparison (a <= b). Panics if sorts don't match.
    #[deprecated(note = "use try_le() which returns Result instead of panicking")]
    pub fn le(&mut self, a: Term, b: Term) -> Term {
        self.try_le(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a less-than-or-equal comparison (a <= b). Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_le(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_arith_sort("le", a, b)?;
        Ok(Term(self.terms_mut().mk_le(a.0, b.0)))
    }

    /// Create a greater-than comparison (a > b). Panics if sorts don't match.
    #[deprecated(note = "use try_gt() which returns Result instead of panicking")]
    pub fn gt(&mut self, a: Term, b: Term) -> Term {
        self.try_gt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a greater-than comparison (a > b). Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_gt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_arith_sort("gt", a, b)?;
        Ok(Term(self.terms_mut().mk_gt(a.0, b.0)))
    }

    /// Create a greater-than-or-equal comparison (a >= b). Panics if sorts don't match.
    #[deprecated(note = "use try_ge() which returns Result instead of panicking")]
    pub fn ge(&mut self, a: Term, b: Term) -> Term {
        self.try_ge(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a greater-than-or-equal comparison (a >= b). Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_ge(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_arith_sort("ge", a, b)?;
        Ok(Term(self.terms_mut().mk_ge(a.0, b.0)))
    }
}
