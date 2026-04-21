// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alethe proof format printer.
//!
//! Formats proof steps, clauses, terms, and constants as SMT-LIB/Alethe text.

use hashbrown::HashMap;
use num_bigint::Sign;
use z4_core::{
    quote_symbol, Constant, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
};

/// Alethe proof printer
pub(crate) struct AlethePrinter<'a> {
    terms: &'a TermStore,
    term_overrides: Option<&'a HashMap<TermId, String>>,
}

impl<'a> AlethePrinter<'a> {
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        Self::new_with_overrides(terms, None)
    }

    pub(crate) fn new_with_overrides(
        terms: &'a TermStore,
        term_overrides: Option<&'a HashMap<TermId, String>>,
    ) -> Self {
        Self {
            terms,
            term_overrides,
        }
    }

    /// Format a proof step as an Alethe command
    pub(crate) fn format_step(&self, step: &ProofStep, id: ProofId) -> String {
        match step {
            ProofStep::Assume(term_id) => {
                let term_str = self.format_term(*term_id);
                format!("(assume {id} {term_str})")
            }
            ProofStep::Resolution {
                clause,
                pivot: _,
                clause1,
                clause2,
            } => {
                let clause_str = self.format_clause(clause);
                // Omit :args — Carcara infers pivot from premises.
                format!("(step {id} {clause_str} :rule resolution :premises ({clause1} {clause2}))")
            }
            ProofStep::TheoryLemma {
                theory: _,
                clause,
                farkas,
                kind,
                ..
            } => self.format_theory_lemma(id, clause, farkas.as_ref(), kind),
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => self.format_generic_step(id, rule, clause, premises, args),
            ProofStep::Anchor {
                end_step,
                variables,
            } => Self::format_anchor(*end_step, variables),
            _ => unreachable!("unexpected ProofStep variant"),
        }
    }

    fn format_theory_lemma(
        &self,
        id: ProofId,
        clause: &[TermId],
        farkas: Option<&z4_core::FarkasAnnotation>,
        kind: &z4_core::TheoryLemmaKind,
    ) -> String {
        let clause_str = self.format_clause(clause);
        if let Some(farkas) = farkas {
            let rule = kind.alethe_rule();
            let coeffs: Vec<String> = farkas.coefficients.iter().map(format_rational64).collect();
            format!(
                "(step {} {} :rule {} :args ({}))",
                id,
                clause_str,
                rule,
                coeffs.join(" ")
            )
        } else {
            // #6686 defensive fallback: la_generic and lia_generic REQUIRE :args
            // (Farkas coefficients). Without them, carcara rejects the step.
            // Fall back to "trust" when the annotation is missing.
            let rule = match kind {
                z4_core::TheoryLemmaKind::LraFarkas | z4_core::TheoryLemmaKind::LiaGeneric => {
                    "trust"
                }
                _ => kind.alethe_rule(),
            };
            format!("(step {id} {clause_str} :rule {rule})")
        }
    }

    fn format_generic_step(
        &self,
        id: ProofId,
        rule: &z4_core::AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> String {
        let clause_str = self.format_clause(clause);
        let mut result = format!("(step {id} {clause_str} :rule {rule}");
        if !premises.is_empty() {
            let premises_str: Vec<String> = premises.iter().map(ToString::to_string).collect();
            let _ = std::fmt::Write::write_fmt(
                &mut result,
                format_args!(" :premises ({})", premises_str.join(" ")),
            );
        }
        if let Some(args_str) = self.format_external_args(rule, clause, premises, args) {
            let _ = std::fmt::Write::write_fmt(
                &mut result,
                format_args!(" :args ({})", args_str.join(" ")),
            );
        }
        result.push(')');
        result
    }

    fn format_anchor(end_step: ProofId, variables: &[(String, Sort)]) -> String {
        let mut result = format!("(anchor :step {end_step}");
        if !variables.is_empty() {
            let vars_str: Vec<String> = variables
                .iter()
                .map(|(name, sort)| format!("({} {sort})", quote_symbol(name)))
                .collect();
            let _ = std::fmt::Write::write_fmt(
                &mut result,
                format_args!(" :args ({})", vars_str.join(" ")),
            );
        }
        result.push(')');
        result
    }

    /// Format a clause (list of literals) as "(cl lit1 lit2 ...)"
    fn format_clause(&self, clause: &[TermId]) -> String {
        if clause.is_empty() {
            "(cl)".to_string()
        } else {
            let lits: Vec<String> = clause.iter().map(|t| self.format_term(*t)).collect();
            format!("(cl {})", lits.join(" "))
        }
    }

    /// Format a term as an SMT-LIB expression
    pub(crate) fn format_term(&self, term_id: TermId) -> String {
        if let Some(term_str) = self
            .term_overrides
            .and_then(|overrides| overrides.get(&term_id))
        {
            return term_str.clone();
        }
        let term = self.terms.get(term_id);
        self.format_term_data(term)
    }

    /// Format term data recursively
    fn format_term_data(&self, term: &TermData) -> String {
        match term {
            TermData::Var(name, _) => quote_symbol(name),

            TermData::Const(c) => Self::format_constant(c),

            TermData::Not(inner) => {
                format!("(not {})", self.format_term(*inner))
            }

            TermData::Ite(cond, then_br, else_br) => {
                format!(
                    "(ite {} {} {})",
                    self.format_term(*cond),
                    self.format_term(*then_br),
                    self.format_term(*else_br)
                )
            }

            TermData::App(sym, args) => {
                let name = Self::format_symbol(sym);
                if args.is_empty() {
                    // Alethe's clause constructor is written as `(cl ...)`, including the
                    // empty clause `(cl)`. Printing the 0-arity `cl` application as `cl`
                    // causes Carcara to reject `drup` steps that use `(cl)` terms in `:args`.
                    if matches!(sym, Symbol::Named(s) if s == "cl") {
                        format!("({name})")
                    } else {
                        name
                    }
                } else {
                    let args_str: Vec<String> = args.iter().map(|&a| self.format_term(a)).collect();
                    format!("({} {})", name, args_str.join(" "))
                }
            }

            TermData::Let(bindings, body) => {
                let bindings_str: Vec<String> = bindings
                    .iter()
                    .map(|(name, term)| {
                        format!("({} {})", quote_symbol(name), self.format_term(*term))
                    })
                    .collect();
                format!(
                    "(let ({}) {})",
                    bindings_str.join(" "),
                    self.format_term(*body)
                )
            }

            TermData::Forall(vars, body, _) => self.format_quantifier("forall", vars, *body),

            TermData::Exists(vars, body, _) => self.format_quantifier("exists", vars, *body),
            _ => unreachable!("unexpected TermData variant"),
        }
    }

    /// Format a quantifier (forall/exists) with sorted variable list.
    fn format_quantifier(&self, keyword: &str, vars: &[(String, Sort)], body: TermId) -> String {
        let vars_str: Vec<String> = vars
            .iter()
            .map(|(name, sort)| format!("({} {})", quote_symbol(name), sort))
            .collect();
        format!(
            "({} ({}) {})",
            keyword,
            vars_str.join(" "),
            self.format_term(body)
        )
    }

    /// Format a constant value
    fn format_constant(c: &Constant) -> String {
        match c {
            Constant::Bool(true) => "true".to_string(),
            Constant::Bool(false) => "false".to_string(),
            Constant::Int(i) => {
                if i.sign() == Sign::Minus {
                    format!("(- {})", i.magnitude())
                } else {
                    i.to_string()
                }
            }
            Constant::Rational(r) => {
                let rat = &r.0;
                if rat.is_integer() {
                    if rat.numer().sign() == Sign::Minus {
                        format!("(- {}.0)", rat.numer().magnitude())
                    } else {
                        format!("{}.0", rat.numer())
                    }
                } else if rat.numer().sign() == Sign::Minus {
                    format!("(- (/ {}.0 {}.0))", rat.numer().magnitude(), rat.denom())
                } else {
                    format!("(/ {}.0 {}.0)", rat.numer(), rat.denom())
                }
            }
            Constant::BitVec { value, width } => {
                // Use binary format for bitvectors
                format!("#b{:0>width$b}", value, width = *width as usize)
            }
            Constant::String(s) => {
                // Escape quotes in strings
                format!("\"{}\"", s.replace('\"', "\"\""))
            }
            _ => unreachable!("unexpected Constant variant"),
        }
    }

    /// Format a function symbol
    fn format_symbol(sym: &Symbol) -> String {
        match sym {
            Symbol::Named(name) => quote_symbol(name),
            Symbol::Indexed(name, indices) => {
                let indices_str: Vec<String> = indices.iter().map(ToString::to_string).collect();
                format!("(_ {} {})", quote_symbol(name), indices_str.join(" "))
            }
            _ => unreachable!("unexpected Symbol variant"),
        }
    }

    fn format_external_args(
        &self,
        rule: &z4_core::AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Option<Vec<String>> {
        // Clausification proof annotations carry the source Boolean term as an
        // internal bookkeeping arg, but Alethe expects rule-specific numeric
        // positions (for `and_pos` / `or_neg`) or no args at all.
        if premises.is_empty() {
            match rule {
                z4_core::AletheRule::AndPos(position) => {
                    return Some(vec![position.to_string()]);
                }
                z4_core::AletheRule::OrNeg => {
                    if let Some(position) = self.infer_or_neg_position(clause, args) {
                        return Some(vec![position.to_string()]);
                    }
                }
                _ => {}
            }

            if self.uses_internal_source_term_arg(rule, clause, args) {
                return None;
            }
        }

        if args.is_empty() {
            None
        } else {
            Some(args.iter().map(|a| self.format_term(*a)).collect())
        }
    }

    fn uses_internal_source_term_arg(
        &self,
        rule: &z4_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> bool {
        if args.len() != 1
            || !matches!(
                rule,
                z4_core::AletheRule::AndPos(_)
                    | z4_core::AletheRule::AndNeg
                    | z4_core::AletheRule::OrPos(_)
                    | z4_core::AletheRule::OrNeg
                    | z4_core::AletheRule::ImpliesPos
                    | z4_core::AletheRule::ImpliesNeg1
                    | z4_core::AletheRule::ImpliesNeg2
                    | z4_core::AletheRule::EquivPos1
                    | z4_core::AletheRule::EquivPos2
                    | z4_core::AletheRule::EquivNeg1
                    | z4_core::AletheRule::EquivNeg2
                    | z4_core::AletheRule::ItePos1
                    | z4_core::AletheRule::ItePos2
                    | z4_core::AletheRule::IteNeg1
                    | z4_core::AletheRule::IteNeg2
                    | z4_core::AletheRule::XorPos1
                    | z4_core::AletheRule::XorPos2
                    | z4_core::AletheRule::XorNeg1
                    | z4_core::AletheRule::XorNeg2
            )
        {
            return false;
        }

        let source_term = args[0];
        clause
            .iter()
            .copied()
            .any(|lit| lit == source_term || self.is_negation_of(lit, source_term))
    }

    fn infer_or_neg_position(&self, clause: &[TermId], args: &[TermId]) -> Option<usize> {
        if clause.len() != 2 {
            return None;
        }

        let source_term = args.first().copied().or_else(|| {
            clause.iter().copied().find(|lit| {
                matches!(
                    self.terms.get(*lit),
                    TermData::App(Symbol::Named(name), _) if name == "or"
                )
            })
        })?;

        let disjuncts = match self.terms.get(source_term) {
            TermData::App(Symbol::Named(name), disjuncts) if name == "or" => disjuncts,
            _ => return None,
        };

        let negated_disjunct =
            clause
                .iter()
                .copied()
                .find_map(|lit| match self.terms.get(lit) {
                    TermData::Not(inner) => Some(*inner),
                    _ => None,
                })?;

        disjuncts
            .iter()
            .position(|disjunct| *disjunct == negated_disjunct)
    }

    fn is_negation_of(&self, lit: TermId, term: TermId) -> bool {
        matches!(self.terms.get(lit), TermData::Not(inner) if *inner == term)
    }
}

fn format_rational64(r: &num_rational::Rational64) -> String {
    let mut numer = *r.numer();
    let mut denom = *r.denom();
    if denom < 0 {
        numer = -numer;
        denom = -denom;
    }
    if denom == 1 {
        numer.to_string()
    } else {
        // Carcara requires Real literals (/ 1.0 2.0) not (/ 1 2)
        format!("(/ {numer}.0 {denom}.0)")
    }
}
