// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! LTL-to-NBA (Nondeterministic Buchi Automaton) translator.
//!
//! Converts common LTL formula patterns into Buchi automata directly,
//! avoiding the general tableau construction for these well-understood
//! patterns. This produces smaller automata than generic tableau
//! expansion for the most common TLA+ temporal formulas.
//!
//! # Supported Patterns
//!
//! - `[]P`    (Always P)        -> 1-state NBA checking P holds at every step
//! - `<>P`    (Eventually P)    -> 2-state NBA accepting when P first holds
//! - `[]<>P`  (Infinitely often)-> 2-state NBA with accepting state on P
//! - `<>[]P`  (Eventual stability) -> 2-state NBA accepting when P holds forever
//!
//! For formulas not matching these patterns, falls back to tableau-based
//! construction via [`super::super::tableau::Tableau`].
//!
//! # References
//!
//! - Gastin, P. & Oddoux, D. (2001). "Fast LTL to Buchi Automata Translation."
//! - Vardi, M. Y. (2007). "Automata-Theoretic Model Checking Revisited."

use super::product::BuchiState;
use crate::liveness::live_expr::LiveExpr;

/// A transition in the NBA: from state, to state, and a guard condition.
///
/// The guard is a [`LiveExpr`] that must hold on the current system state
/// (for state-level guards) or on the current transition (for action-level
/// guards) for this NBA transition to be taken.
#[derive(Debug, Clone)]
pub(crate) struct NbaTransition {
    /// Source Buchi state.
    pub(crate) from: BuchiState,
    /// Destination Buchi state.
    pub(crate) to: BuchiState,
    /// Guard condition (evaluated against the current system state/transition).
    /// `LiveExpr::Bool(true)` means unconditional.
    pub(crate) guard: LiveExpr,
}

/// Nondeterministic Buchi Automaton for a negated LTL property.
///
/// The NBA accepts exactly those infinite words (behaviors) that violate
/// the original LTL property. An accepting run visits at least one
/// accepting state infinitely often.
///
/// States are identified by [`BuchiState`] indices. State 0 is always
/// an initial state.
#[derive(Debug, Clone)]
pub(crate) struct Nba {
    /// Human-readable name of the property this NBA checks.
    pub(crate) property_name: String,
    /// Number of states in the automaton.
    pub(crate) state_count: usize,
    /// Set of initial states (indices into 0..state_count).
    pub(crate) initial_states: Vec<BuchiState>,
    /// Set of accepting states (for Buchi acceptance condition).
    pub(crate) accepting_states: Vec<BuchiState>,
    /// All transitions.
    pub(crate) transitions: Vec<NbaTransition>,
    /// The original negated formula (for diagnostics).
    pub(crate) negated_formula: LiveExpr,
}

impl Nba {
    /// Get successors of a Buchi state (all transitions from that state).
    pub(crate) fn successors(&self, state: BuchiState) -> Vec<(BuchiState, &LiveExpr)> {
        self.transitions
            .iter()
            .filter(|t| t.from == state)
            .map(|t| (t.to, &t.guard))
            .collect()
    }

    /// Check if a Buchi state is accepting.
    pub(crate) fn is_accepting(&self, state: BuchiState) -> bool {
        self.accepting_states.contains(&state)
    }
}

/// Classification of an LTL formula pattern for direct NBA construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LtlPattern {
    /// `[]P` - Always P (safety property).
    AlwaysP,
    /// `<>P` - Eventually P (guarantee property).
    EventuallyP,
    /// `[]<>P` - Infinitely often P (recurrence/persistence).
    AlwaysEventuallyP,
    /// `<>[]P` - Eventually always P (stability).
    EventuallyAlwaysP,
    /// Not a recognized direct pattern; use tableau.
    General,
}

/// Classify an LTL formula into a known pattern (if possible).
///
/// Works on the *original property* (not the negation). The NBA
/// construction handles negation internally.
pub(crate) fn classify_ltl_pattern(formula: &LiveExpr) -> LtlPattern {
    match formula {
        LiveExpr::Always(inner) => match inner.as_ref() {
            LiveExpr::Eventually(_) => LtlPattern::AlwaysEventuallyP,
            _ if !is_temporal(inner) => LtlPattern::AlwaysP,
            _ => LtlPattern::General,
        },
        LiveExpr::Eventually(inner) => match inner.as_ref() {
            LiveExpr::Always(_) => LtlPattern::EventuallyAlwaysP,
            _ if !is_temporal(inner) => LtlPattern::EventuallyP,
            _ => LtlPattern::General,
        },
        _ => LtlPattern::General,
    }
}

/// Check if an expression contains temporal operators.
fn is_temporal(expr: &LiveExpr) -> bool {
    match expr {
        LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => true,
        LiveExpr::And(exprs) | LiveExpr::Or(exprs) => exprs.iter().any(is_temporal),
        LiveExpr::Not(inner) => is_temporal(inner),
        LiveExpr::Bool(_)
        | LiveExpr::StatePred { .. }
        | LiveExpr::ActionPred { .. }
        | LiveExpr::Enabled { .. }
        | LiveExpr::StateChanged { .. } => false,
    }
}

/// Build an NBA for a negated LTL formula using direct pattern translation.
///
/// The `property_formula` is the *original property* (what should hold).
/// We construct the NBA for the negation (what we want to detect).
///
/// Returns `None` if the formula doesn't match a known pattern.
pub(crate) fn build_nba_for_pattern(
    property_name: &str,
    property_formula: &LiveExpr,
) -> Option<Nba> {
    let pattern = classify_ltl_pattern(property_formula);
    match pattern {
        LtlPattern::AlwaysP => {
            // Property: []P. Violation: <>~P. NBA accepts if ~P ever holds.
            //
            // States: q0 (initial+accepting)
            // Transitions: q0 --[~P]--> q0  (stay accepting while ~P holds)
            //              q0 --[true]--> q0 (but acceptance requires ~P at least once)
            //
            // Actually for []P, the negation <>~P is simpler:
            //   q0 (initial) --[~P]--> q1 (accepting, self-loop)
            //   q0 --[P]--> q0
            //   q1 --[true]--> q1
            let LiveExpr::Always(p) = property_formula else {
                return None;
            };
            let neg_p = LiveExpr::not(p.as_ref().clone()).push_negation();

            Some(Nba {
                property_name: property_name.to_string(),
                state_count: 2,
                initial_states: vec![BuchiState(0)],
                accepting_states: vec![BuchiState(1)],
                transitions: vec![
                    // q0 --[~P]--> q1: violation detected, go to accepting sink
                    NbaTransition {
                        from: BuchiState(0),
                        to: BuchiState(1),
                        guard: neg_p,
                    },
                    // q0 --[P]--> q0: property holds, stay in initial
                    NbaTransition {
                        from: BuchiState(0),
                        to: BuchiState(0),
                        guard: p.as_ref().clone(),
                    },
                    // q1 --[true]--> q1: accepting sink (once violation seen, stay)
                    NbaTransition {
                        from: BuchiState(1),
                        to: BuchiState(1),
                        guard: LiveExpr::Bool(true),
                    },
                ],
                negated_formula: LiveExpr::eventually(
                    LiveExpr::not(p.as_ref().clone()).push_negation(),
                ),
            })
        }

        LtlPattern::EventuallyP => {
            // Property: <>P. Violation: []~P. NBA accepts if ~P holds forever.
            //
            // q0 (initial, accepting) --[~P]--> q0
            // (No transition on P -- run dies if P ever holds)
            let LiveExpr::Eventually(p) = property_formula else {
                return None;
            };
            let neg_p = LiveExpr::not(p.as_ref().clone()).push_negation();

            Some(Nba {
                property_name: property_name.to_string(),
                state_count: 1,
                initial_states: vec![BuchiState(0)],
                accepting_states: vec![BuchiState(0)],
                transitions: vec![
                    // q0 --[~P]--> q0: P never holds, keep accepting
                    NbaTransition {
                        from: BuchiState(0),
                        to: BuchiState(0),
                        guard: neg_p,
                    },
                ],
                negated_formula: LiveExpr::always(
                    LiveExpr::not(p.as_ref().clone()).push_negation(),
                ),
            })
        }

        LtlPattern::AlwaysEventuallyP => {
            // Property: []<>P. Violation: <>[]~P (eventually ~P holds forever).
            //
            // q0 (initial) --[true]--> q0  (waiting for ~P to stabilize)
            // q0 --[~P]--> q1
            // q1 (accepting) --[~P]--> q1  (staying in ~P forever = accepting)
            //
            // The accepting run must visit q1 infinitely often, which
            // happens iff ~P holds from some point onward.
            let LiveExpr::Always(inner) = property_formula else {
                return None;
            };
            let LiveExpr::Eventually(p) = inner.as_ref() else {
                return None;
            };
            let neg_p = LiveExpr::not(p.as_ref().clone()).push_negation();

            Some(Nba {
                property_name: property_name.to_string(),
                state_count: 2,
                initial_states: vec![BuchiState(0)],
                accepting_states: vec![BuchiState(1)],
                transitions: vec![
                    // q0 --[true]--> q0: nondeterministically stay
                    NbaTransition {
                        from: BuchiState(0),
                        to: BuchiState(0),
                        guard: LiveExpr::Bool(true),
                    },
                    // q0 --[~P]--> q1: guess that ~P holds forever from here
                    NbaTransition {
                        from: BuchiState(0),
                        to: BuchiState(1),
                        guard: neg_p.clone(),
                    },
                    // q1 --[~P]--> q1: ~P continues to hold
                    NbaTransition {
                        from: BuchiState(1),
                        to: BuchiState(1),
                        guard: neg_p,
                    },
                ],
                negated_formula: LiveExpr::eventually(LiveExpr::always(
                    LiveExpr::not(p.as_ref().clone()).push_negation(),
                )),
            })
        }

        LtlPattern::EventuallyAlwaysP => {
            // Property: <>[]P. Violation: []<>~P (~P occurs infinitely often).
            //
            // q0 (initial, accepting) --[true]--> q0 (always nondeterministically stay)
            // q0 --[~P]--> q0 (seeing ~P: reset acceptance window)
            //
            // For Buchi acceptance of []<>~P: an accepting state must be
            // visited infinitely often. We use a 2-state construction:
            //   q0 (initial) --[~P]--> q1
            //   q0 --[P]--> q0
            //   q1 (accepting) --[true]--> q0
            //
            // This accepts iff ~P occurs infinitely often (each occurrence
            // passes through q1, which is accepting).
            let LiveExpr::Eventually(inner) = property_formula else {
                return None;
            };
            let LiveExpr::Always(p) = inner.as_ref() else {
                return None;
            };
            let neg_p = LiveExpr::not(p.as_ref().clone()).push_negation();

            Some(Nba {
                property_name: property_name.to_string(),
                state_count: 2,
                initial_states: vec![BuchiState(0)],
                accepting_states: vec![BuchiState(1)],
                transitions: vec![
                    // q0 --[P]--> q0: property holds, stay non-accepting
                    NbaTransition {
                        from: BuchiState(0),
                        to: BuchiState(0),
                        guard: p.as_ref().clone(),
                    },
                    // q0 --[~P]--> q1: violation occurrence, go accepting
                    NbaTransition {
                        from: BuchiState(0),
                        to: BuchiState(1),
                        guard: neg_p,
                    },
                    // q1 --[true]--> q0: return to look for next violation
                    NbaTransition {
                        from: BuchiState(1),
                        to: BuchiState(0),
                        guard: LiveExpr::Bool(true),
                    },
                ],
                negated_formula: LiveExpr::always(LiveExpr::eventually(
                    LiveExpr::not(p.as_ref().clone()).push_negation(),
                )),
            })
        }

        LtlPattern::General => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_state_pred(tag: u32) -> LiveExpr {
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::Spanned;
        LiveExpr::state_pred(Arc::new(Spanned::dummy(Expr::Bool(true))), tag)
    }

    #[test]
    fn test_classify_always_p() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::always(p);
        assert_eq!(classify_ltl_pattern(&formula), LtlPattern::AlwaysP);
    }

    #[test]
    fn test_classify_eventually_p() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::eventually(p);
        assert_eq!(classify_ltl_pattern(&formula), LtlPattern::EventuallyP);
    }

    #[test]
    fn test_classify_always_eventually_p() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::always(LiveExpr::eventually(p));
        assert_eq!(
            classify_ltl_pattern(&formula),
            LtlPattern::AlwaysEventuallyP
        );
    }

    #[test]
    fn test_classify_eventually_always_p() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::eventually(LiveExpr::always(p));
        assert_eq!(
            classify_ltl_pattern(&formula),
            LtlPattern::EventuallyAlwaysP
        );
    }

    #[test]
    fn test_classify_general() {
        let p = dummy_state_pred(1);
        // Just a state predicate (not wrapped in temporal op)
        assert_eq!(classify_ltl_pattern(&p), LtlPattern::General);

        // Nested temporal: [](<>P /\ <>Q) -- not a recognized pattern
        let q = dummy_state_pred(2);
        let complex = LiveExpr::always(LiveExpr::and(vec![
            LiveExpr::eventually(p),
            LiveExpr::eventually(q),
        ]));
        assert_eq!(classify_ltl_pattern(&complex), LtlPattern::General);
    }

    #[test]
    fn test_build_nba_always_p() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::always(p);
        let nba = build_nba_for_pattern("TestAlways", &formula).expect("should build NBA for []P");

        assert_eq!(nba.state_count, 2);
        assert_eq!(nba.initial_states, vec![BuchiState(0)]);
        assert_eq!(nba.accepting_states, vec![BuchiState(1)]);
        assert_eq!(nba.transitions.len(), 3);
    }

    #[test]
    fn test_build_nba_eventually_p() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::eventually(p);
        let nba =
            build_nba_for_pattern("TestEventually", &formula).expect("should build NBA for <>P");

        assert_eq!(nba.state_count, 1);
        assert_eq!(nba.initial_states, vec![BuchiState(0)]);
        assert_eq!(nba.accepting_states, vec![BuchiState(0)]);
        // Only one transition: q0 --[~P]--> q0
        assert_eq!(nba.transitions.len(), 1);
    }

    #[test]
    fn test_build_nba_always_eventually_p() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::always(LiveExpr::eventually(p));
        let nba = build_nba_for_pattern("TestAE", &formula).expect("should build NBA for []<>P");

        assert_eq!(nba.state_count, 2);
        assert_eq!(nba.initial_states, vec![BuchiState(0)]);
        assert_eq!(nba.accepting_states, vec![BuchiState(1)]);
        assert_eq!(nba.transitions.len(), 3);
    }

    #[test]
    fn test_build_nba_eventually_always_p() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::eventually(LiveExpr::always(p));
        let nba = build_nba_for_pattern("TestEA", &formula).expect("should build NBA for <>[]P");

        assert_eq!(nba.state_count, 2);
        assert_eq!(nba.initial_states, vec![BuchiState(0)]);
        assert_eq!(nba.accepting_states, vec![BuchiState(1)]);
        assert_eq!(nba.transitions.len(), 3);
    }

    #[test]
    fn test_build_nba_general_returns_none() {
        let p = dummy_state_pred(1);
        // Plain predicate: not a temporal pattern
        assert!(build_nba_for_pattern("TestGeneral", &p).is_none());
    }

    #[test]
    fn test_nba_successors() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::always(p);
        let nba = build_nba_for_pattern("TestSucc", &formula).expect("should build NBA");

        let q0_succs = nba.successors(BuchiState(0));
        assert_eq!(q0_succs.len(), 2, "q0 should have 2 outgoing transitions");

        let q1_succs = nba.successors(BuchiState(1));
        assert_eq!(q1_succs.len(), 1, "q1 should have 1 self-loop");
    }

    #[test]
    fn test_nba_is_accepting() {
        let p = dummy_state_pred(1);
        let formula = LiveExpr::always(p);
        let nba = build_nba_for_pattern("TestAcc", &formula).expect("should build NBA");

        assert!(!nba.is_accepting(BuchiState(0)));
        assert!(nba.is_accepting(BuchiState(1)));
    }
}
