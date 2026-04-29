// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Certificate verification implementation.

use std::collections::{HashMap, HashSet};

use crate::axiom_check;
use crate::formula_ops::{
    alpha_equiv, is_existential_intro_instance, is_valid_tableau_decomposition,
    substitute_term_in_formula, substitute_var_in_formula,
};
use crate::types::{
    Certificate, CertificateStep, Formula, Justification, StepId, VerificationError,
    VerificationResult,
};

/// The certificate checker
pub struct CertificateChecker {
    /// Proven facts (step_id -> formula)
    facts: HashMap<StepId, Formula>,
    /// Definitions available
    definitions: HashMap<String, Formula>,
}

impl CertificateChecker {
    /// Create a new certificate checker
    pub fn new() -> Self {
        Self {
            facts: HashMap::new(),
            definitions: HashMap::new(),
        }
    }

    /// Add a definition
    pub fn add_definition(&mut self, name: String, formula: Formula) {
        self.definitions.insert(name, formula);
    }

    /// Verify a certificate
    pub fn verify(&mut self, cert: &Certificate) -> VerificationResult {
        self.facts.clear();

        // Add hypotheses as facts
        for (i, hyp) in cert.hypotheses.iter().enumerate() {
            self.facts.insert(i as StepId, hyp.clone());
        }

        // Verify each step
        for step in &cert.steps {
            match self.verify_step(step, &cert.hypotheses) {
                Ok(()) => {
                    self.facts.insert(step.id, step.formula.clone());
                }
                Err(e) => return VerificationResult::Invalid(e),
            }
        }

        // Check that the goal was proven (using alpha-equivalence for quantified formulas)
        let last_step = cert.steps.last();
        match last_step {
            Some(step) if alpha_equiv(&step.formula, &cert.goal) => VerificationResult::Valid,
            _ => VerificationResult::Invalid(VerificationError::GoalMismatch),
        }
    }

    fn has_contradiction(&self) -> bool {
        if self
            .facts
            .values()
            .any(|formula| matches!(formula, Formula::Bool(false)))
        {
            return true;
        }

        let formulas: HashSet<Formula> = self.facts.values().cloned().collect();
        for formula in &formulas {
            if let Formula::Not(inner) = formula {
                if formulas.contains(inner.as_ref()) {
                    return true;
                }
            }
        }

        false
    }

    fn get_fact(&self, id: &StepId) -> Result<&Formula, VerificationError> {
        self.facts
            .get(id)
            .ok_or(VerificationError::UnknownStep(*id))
    }

    fn verify_step(
        &self,
        step: &CertificateStep,
        hypotheses: &[Formula],
    ) -> Result<(), VerificationError> {
        match &step.justification {
            Justification::Hypothesis(idx) => self.verify_hypothesis(step, hypotheses, *idx),
            Justification::Axiom(axiom) => axiom_check::verify_axiom(axiom, &step.formula),
            Justification::ModusPonens {
                premise,
                implication,
            } => self.verify_modus_ponens(step, premise, implication),
            Justification::AndIntro { left, right } => self.verify_and_intro(step, left, right),
            Justification::AndElimLeft { conjunction } => {
                self.verify_and_elim_left(step, conjunction)
            }
            Justification::AndElimRight { conjunction } => {
                self.verify_and_elim_right(step, conjunction)
            }
            Justification::OrIntroLeft { premise, right } => {
                self.verify_or_intro_left(step, premise, right)
            }
            Justification::OrIntroRight { left, premise } => {
                self.verify_or_intro_right(step, left, premise)
            }
            Justification::DoubleNegElim { premise } => self.verify_double_neg_elim(step, premise),
            Justification::Rewrite { equality, target } => {
                self.verify_rewrite(step, equality, target)
            }
            Justification::Definition { name } => self.verify_definition(step, name),
            Justification::UniversalInstantiation { forall, term } => {
                self.verify_universal_inst(step, forall, term)
            }
            Justification::TableauDecomposition { premise } => {
                self.verify_tableau_decomp(step, premise)
            }
            Justification::ExistentialIntro { witness, variable } => {
                self.verify_existential_intro(step, witness, variable)
            }
        }
    }

    fn verify_hypothesis(
        &self,
        step: &CertificateStep,
        hypotheses: &[Formula],
        idx: usize,
    ) -> Result<(), VerificationError> {
        if idx < hypotheses.len() && hypotheses[idx] == step.formula {
            Ok(())
        } else {
            Err(VerificationError::InvalidJustification {
                step: step.id,
                reason: "Invalid hypothesis reference".to_string(),
            })
        }
    }

    fn verify_modus_ponens(
        &self,
        step: &CertificateStep,
        premise: &StepId,
        implication: &StepId,
    ) -> Result<(), VerificationError> {
        let p = self.get_fact(premise)?;
        let imp = self.get_fact(implication)?;

        if let Formula::Implies(ante, cons) = imp {
            if ante.as_ref() == p && cons.as_ref() == &step.formula {
                return Ok(());
            }
        }

        Err(VerificationError::InvalidJustification {
            step: step.id,
            reason: "Modus ponens doesn't apply".to_string(),
        })
    }

    fn verify_and_intro(
        &self,
        step: &CertificateStep,
        left: &StepId,
        right: &StepId,
    ) -> Result<(), VerificationError> {
        let l = self.get_fact(left)?;
        let r = self.get_fact(right)?;

        if step.formula == Formula::And(Box::new(l.clone()), Box::new(r.clone())) {
            Ok(())
        } else {
            Err(VerificationError::InvalidJustification {
                step: step.id,
                reason: "And-intro doesn't match".to_string(),
            })
        }
    }

    fn verify_and_elim_left(
        &self,
        step: &CertificateStep,
        conjunction: &StepId,
    ) -> Result<(), VerificationError> {
        let conj = self.get_fact(conjunction)?;
        if let Formula::And(left, _) = conj {
            if left.as_ref() == &step.formula {
                return Ok(());
            }
        }
        Err(VerificationError::InvalidJustification {
            step: step.id,
            reason: "And-elim-left doesn't apply".to_string(),
        })
    }

    fn verify_and_elim_right(
        &self,
        step: &CertificateStep,
        conjunction: &StepId,
    ) -> Result<(), VerificationError> {
        let conj = self.get_fact(conjunction)?;
        if let Formula::And(_, right) = conj {
            if right.as_ref() == &step.formula {
                return Ok(());
            }
        }
        Err(VerificationError::InvalidJustification {
            step: step.id,
            reason: "And-elim-right doesn't apply".to_string(),
        })
    }

    fn verify_or_intro_left(
        &self,
        step: &CertificateStep,
        premise: &StepId,
        right: &Formula,
    ) -> Result<(), VerificationError> {
        let p = self.get_fact(premise)?;
        let expected = Formula::Or(Box::new(p.clone()), Box::new(right.clone()));
        if step.formula == expected {
            Ok(())
        } else {
            Err(VerificationError::InvalidJustification {
                step: step.id,
                reason: "Or-intro-left doesn't match".to_string(),
            })
        }
    }

    fn verify_or_intro_right(
        &self,
        step: &CertificateStep,
        left: &Formula,
        premise: &StepId,
    ) -> Result<(), VerificationError> {
        let q = self.get_fact(premise)?;
        let expected = Formula::Or(Box::new(left.clone()), Box::new(q.clone()));
        if step.formula == expected {
            Ok(())
        } else {
            Err(VerificationError::InvalidJustification {
                step: step.id,
                reason: "Or-intro-right doesn't match".to_string(),
            })
        }
    }

    fn verify_double_neg_elim(
        &self,
        step: &CertificateStep,
        premise: &StepId,
    ) -> Result<(), VerificationError> {
        let nnp = self.get_fact(premise)?;
        if let Formula::Not(inner) = nnp {
            if let Formula::Not(p) = inner.as_ref() {
                if p.as_ref() == &step.formula {
                    return Ok(());
                }
            }
        }
        Err(VerificationError::InvalidJustification {
            step: step.id,
            reason: "Double negation elimination doesn't apply".to_string(),
        })
    }

    fn verify_rewrite(
        &self,
        step: &CertificateStep,
        equality: &StepId,
        target: &StepId,
    ) -> Result<(), VerificationError> {
        let eq_formula = self.get_fact(equality)?;
        let target_formula = self.get_fact(target)?;

        if let Formula::Eq(a, b) = eq_formula {
            let rewritten_ab = substitute_term_in_formula(target_formula, a, b);
            let rewritten_ba = substitute_term_in_formula(target_formula, b, a);
            if step.formula == rewritten_ab || step.formula == rewritten_ba {
                return Ok(());
            }
        }

        Err(VerificationError::InvalidJustification {
            step: step.id,
            reason: "Rewrite doesn't apply".to_string(),
        })
    }

    fn verify_definition(
        &self,
        step: &CertificateStep,
        name: &str,
    ) -> Result<(), VerificationError> {
        if let Some(def_formula) = self.definitions.get(name) {
            if &step.formula == def_formula {
                return Ok(());
            }
        }
        Err(VerificationError::InvalidJustification {
            step: step.id,
            reason: format!("Definition '{}' not found or doesn't match", name),
        })
    }

    fn verify_universal_inst(
        &self,
        step: &CertificateStep,
        forall: &StepId,
        term: &crate::types::Term,
    ) -> Result<(), VerificationError> {
        let forall_formula = self.get_fact(forall)?;
        if let Formula::Forall(var, body) = forall_formula {
            let instantiated = substitute_var_in_formula(body, var, term);
            if step.formula == instantiated {
                return Ok(());
            }
        }
        Err(VerificationError::InvalidJustification {
            step: step.id,
            reason: "Universal instantiation doesn't apply".to_string(),
        })
    }

    fn verify_tableau_decomp(
        &self,
        step: &CertificateStep,
        premise: &StepId,
    ) -> Result<(), VerificationError> {
        let premise_formula = self.get_fact(premise)?;
        if is_valid_tableau_decomposition(premise_formula, &step.formula)
            || self.has_contradiction()
        {
            Ok(())
        } else {
            Err(VerificationError::InvalidJustification {
                step: step.id,
                reason: "Tableau decomposition doesn't apply".to_string(),
            })
        }
    }

    fn verify_existential_intro(
        &self,
        step: &CertificateStep,
        witness: &StepId,
        variable: &str,
    ) -> Result<(), VerificationError> {
        let witness_formula = self.get_fact(witness)?;
        if let Formula::Exists(var, body) = &step.formula {
            if var == variable && is_existential_intro_instance(body, var, witness_formula) {
                return Ok(());
            }
        }
        Err(VerificationError::InvalidJustification {
            step: step.id,
            reason: "Existential introduction doesn't apply".to_string(),
        })
    }
}

impl Default for CertificateChecker {
    fn default() -> Self {
        Self::new()
    }
}
