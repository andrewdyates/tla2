// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a universally quantified formula: `(forall ((x S) ...) body)`.
    ///
    /// `vars` must be variable terms (see [`Self::fresh_var`] and [`Self::declare_const`]).
    ///
    /// # Panics
    /// Panics if any element of `vars` is not a variable term, or if `vars` contains duplicates.
    /// Use [`Self::try_forall`] for a fallible version.
    #[deprecated(note = "use try_forall() which returns Result instead of panicking")]
    pub fn forall(&mut self, vars: &[Term], body: Term) -> Term {
        self.try_forall(vars, body)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a universally quantified formula: `(forall ((x S) ...) body)`.
    ///
    /// Fallible version of [`forall`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `body` is not a Bool.
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - Any element of `vars` is not a variable term
    /// - `vars` contains duplicate variables
    ///
    /// [`forall`]: Solver::forall
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_forall(&mut self, vars: &[Term], body: Term) -> Result<Term, SolverError> {
        let body_sort = self.terms().sort(body.0).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "forall",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::new();
        let mut core_vars = Vec::with_capacity(vars.len());
        for var in vars {
            let name = match self.terms().get(var.0) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation: "forall",
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };

            if !seen.insert(var.0) {
                return Err(SolverError::InvalidArgument {
                    operation: "forall",
                    message: format!("duplicate bound variable: {name}"),
                });
            }

            let sort = self.terms().sort(var.0).clone();
            core_vars.push((name, sort));
        }
        Ok(Term(self.terms_mut().mk_forall(core_vars, body.0)))
    }

    /// Create a universally quantified formula with trigger patterns.
    ///
    /// Triggers guide E-matching instantiation. Each inner slice is a multi-trigger
    /// (all patterns must match for instantiation). Multiple outer elements are
    /// alternative trigger sets.
    ///
    /// # Panics
    /// Panics on invalid bound variables or triggers. Use [`Self::try_forall_with_triggers`]
    /// for a fallible version.
    #[deprecated(note = "use try_forall_with_triggers() which returns Result instead of panicking")]
    pub fn forall_with_triggers(
        &mut self,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Term {
        self.try_forall_with_triggers(vars, body, triggers)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a universally quantified formula with trigger patterns.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if `body` is not a Bool.
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - Any element of `vars` is not a variable term
    /// - `vars` contains duplicate variables
    ///
    /// Returns [`SolverError::InvalidTrigger`] if any trigger application does not
    /// contain at least one bound variable.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_forall_with_triggers(
        &mut self,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Result<Term, SolverError> {
        let body_sort = self.terms().sort(body.0).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "forall_with_triggers",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::new();
        let mut bound_names: HashSet<String> = HashSet::new();
        let mut core_vars = Vec::with_capacity(vars.len());
        for var in vars {
            let name = match self.terms().get(var.0) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation: "forall_with_triggers",
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };

            if !seen.insert(var.0) {
                return Err(SolverError::InvalidArgument {
                    operation: "forall_with_triggers",
                    message: format!("duplicate bound variable: {name}"),
                });
            }

            let sort = self.terms().sort(var.0).clone();
            bound_names.insert(name.clone());
            core_vars.push((name, sort));
        }

        let mut core_triggers: Vec<Vec<TermId>> = Vec::new();
        for multi in triggers {
            let mut multi_terms: Vec<TermId> = Vec::new();
            for t in *multi {
                let TermData::App(_, _) = self.terms().get(t.0) else {
                    continue;
                };
                if !contains_bound_var(self.terms(), t.0, &bound_names) {
                    return Err(SolverError::InvalidTrigger {
                        operation: "forall_with_triggers",
                        message: "trigger must contain at least one bound variable".to_string(),
                    });
                }
                multi_terms.push(t.0);
            }
            if !multi_terms.is_empty() {
                core_triggers.push(multi_terms);
            }
        }

        Ok(Term(self.terms_mut().mk_forall_with_triggers(
            core_vars,
            body.0,
            core_triggers,
        )))
    }

    /// Create an existentially quantified formula: `(exists ((x S) ...) body)`.
    ///
    /// `vars` must be variable terms (see [`Self::fresh_var`] and [`Self::declare_const`]).
    ///
    /// # Panics
    /// Panics if any element of `vars` is not a variable term, or if `vars` contains duplicates.
    /// Use [`Self::try_exists`] for a fallible version.
    #[deprecated(note = "use try_exists() which returns Result instead of panicking")]
    pub fn exists(&mut self, vars: &[Term], body: Term) -> Term {
        self.try_exists(vars, body)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an existentially quantified formula: `(exists ((x S) ...) body)`.
    ///
    /// Fallible version of [`exists`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `body` is not a Bool.
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - Any element of `vars` is not a variable term
    /// - `vars` contains duplicate variables
    ///
    /// [`exists`]: Solver::exists
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_exists(&mut self, vars: &[Term], body: Term) -> Result<Term, SolverError> {
        let body_sort = self.terms().sort(body.0).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "exists",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::new();
        let mut core_vars = Vec::with_capacity(vars.len());
        for var in vars {
            let name = match self.terms().get(var.0) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation: "exists",
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };

            if !seen.insert(var.0) {
                return Err(SolverError::InvalidArgument {
                    operation: "exists",
                    message: format!("duplicate bound variable: {name}"),
                });
            }

            let sort = self.terms().sort(var.0).clone();
            core_vars.push((name, sort));
        }
        Ok(Term(self.terms_mut().mk_exists(core_vars, body.0)))
    }

    /// Create an existentially quantified formula with trigger patterns.
    ///
    /// Triggers guide E-matching instantiation. Each inner slice is a multi-trigger
    /// (all patterns must match for instantiation). Multiple outer elements are
    /// alternative trigger sets.
    ///
    /// # Panics
    /// Panics on invalid bound variables or triggers. Use [`Self::try_exists_with_triggers`]
    /// for a fallible version.
    #[deprecated(note = "use try_exists_with_triggers() which returns Result instead of panicking")]
    pub fn exists_with_triggers(
        &mut self,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Term {
        self.try_exists_with_triggers(vars, body, triggers)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an existentially quantified formula with trigger patterns.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if `body` is not a Bool.
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - Any element of `vars` is not a variable term
    /// - `vars` contains duplicate variables
    ///
    /// Returns [`SolverError::InvalidTrigger`] if any trigger application does not
    /// contain at least one bound variable.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_exists_with_triggers(
        &mut self,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Result<Term, SolverError> {
        let body_sort = self.terms().sort(body.0).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "exists_with_triggers",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::new();
        let mut bound_names: HashSet<String> = HashSet::new();
        let mut core_vars = Vec::with_capacity(vars.len());
        for var in vars {
            let name = match self.terms().get(var.0) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation: "exists_with_triggers",
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };

            if !seen.insert(var.0) {
                return Err(SolverError::InvalidArgument {
                    operation: "exists_with_triggers",
                    message: format!("duplicate bound variable: {name}"),
                });
            }

            bound_names.insert(name.clone());
            let sort = self.terms().sort(var.0).clone();
            core_vars.push((name, sort));
        }

        let mut core_triggers: Vec<Vec<TermId>> = Vec::new();
        for multi in triggers {
            let mut multi_terms: Vec<TermId> = Vec::new();
            for t in *multi {
                let TermData::App(_, _) = self.terms().get(t.0) else {
                    continue;
                };
                if !contains_bound_var(self.terms(), t.0, &bound_names) {
                    return Err(SolverError::InvalidTrigger {
                        operation: "exists_with_triggers",
                        message: "trigger must contain at least one bound variable".to_string(),
                    });
                }
                multi_terms.push(t.0);
            }
            if !multi_terms.is_empty() {
                core_triggers.push(multi_terms);
            }
        }

        Ok(Term(self.terms_mut().mk_exists_with_triggers(
            core_vars,
            body.0,
            core_triggers,
        )))
    }
}

fn contains_bound_var(terms: &TermStore, term: TermId, bound_names: &HashSet<String>) -> bool {
    match terms.get(term) {
        TermData::Var(name, _) => bound_names.contains(name),
        TermData::App(_, args) => args
            .iter()
            .any(|&arg| contains_bound_var(terms, arg, bound_names)),
        TermData::Not(inner) => contains_bound_var(terms, *inner, bound_names),
        TermData::Ite(c, t, e) => {
            contains_bound_var(terms, *c, bound_names)
                || contains_bound_var(terms, *t, bound_names)
                || contains_bound_var(terms, *e, bound_names)
        }
        TermData::Let(_, _) | TermData::Forall(..) | TermData::Exists(..) => false,
        TermData::Const(_) => false,
        other => unreachable!("unhandled TermData variant in contains_bound_var(): {other:?}"),
    }
}
