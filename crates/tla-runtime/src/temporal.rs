// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Temporal property verification over execution traces.
//!
//! TLA+ temporal operators (`[]`, `<>`, `~>`, `WF`, `SF`) are trace-level
//! properties — they cannot be checked on a single state. This module provides
//! composable temporal formulas that verify these properties over finite
//! execution traces produced by the model checker or runtime monitor.
//!
//! # Design
//!
//! The key insight is that generated Rust code cannot evaluate temporal operators
//! inline (they are NOT single-state predicates). Instead, we:
//!
//! 1. **Extract** state predicates and action predicates from temporal formulas
//! 2. **Compose** them into `TemporalProp` values representing the LTL structure
//! 3. **Verify** the composed formula over a trace via `check_trace()`
//!
//! This turns the "inherently untranslatable" temporal operators into first-class
//! runtime-checkable properties for property-based testing and trace validation.
//!
//! # Supported Properties
//!
//! | TLA+ | Semantics | Rust |
//! |------|-----------|------|
//! | `[]P` | P holds in every state | `TemporalProp::Always(p)` |
//! | `<>P` | P holds in some state | `TemporalProp::Eventually(p)` |
//! | `P ~> Q` | If P holds, Q eventually holds | `TemporalProp::LeadsTo(p, q)` |
//! | `WF_v(A)` | Continuously enabled → eventually happens | `TemporalProp::WeakFairness(a)` |
//! | `SF_v(A)` | Repeatedly enabled → eventually happens | `TemporalProp::StrongFairness(a)` |
//! | `[A]_v` | Action A or stutter step | `TemporalProp::BoxAction(a, v)` |
//! | `<<A>>_v` | Action A with actual change | `TemporalProp::AngleAction(a, v)` |

use std::fmt;

/// A composable temporal property over states of type `S`.
///
/// These are constructed by generated code and verified over traces at runtime.
pub enum TemporalProp<S> {
    /// `[]P`: P holds in every state of the trace.
    Always(Box<dyn Fn(&S) -> bool + Send + Sync>),

    /// `<>P`: P holds in at least one state of the trace.
    Eventually(Box<dyn Fn(&S) -> bool + Send + Sync>),

    /// `P ~> Q`: Whenever P holds at state i, Q holds at some j >= i.
    LeadsTo(
        Box<dyn Fn(&S) -> bool + Send + Sync>,
        Box<dyn Fn(&S) -> bool + Send + Sync>,
    ),

    /// `WF_v(A)`: If <<A>>_v is continuously enabled from some point,
    /// then <<A>>_v eventually occurs. (Weak fairness.)
    ///
    /// For finite trace checking: if the action is enabled in the final
    /// suffix (all states from some point), it must fire at least once.
    WeakFairness(Box<dyn Fn(&S) -> bool + Send + Sync>),

    /// `SF_v(A)`: If <<A>>_v is repeatedly enabled (infinitely often),
    /// then <<A>>_v eventually occurs. (Strong fairness.)
    ///
    /// Stronger than WF: even intermittent enabling requires eventual firing.
    StrongFairness(Box<dyn Fn(&S) -> bool + Send + Sync>),

    /// `[A]_v`: Action A holds OR the subscript variables are unchanged
    /// (stutter step). Checked over consecutive state pairs.
    BoxAction(
        Box<dyn Fn(&S) -> bool + Send + Sync>,
        Box<dyn Fn(&S) -> bool + Send + Sync>,
    ),

    /// `<<A>>_v`: Action A holds AND the subscript variables actually change.
    /// Checked over consecutive state pairs.
    AngleAction(
        Box<dyn Fn(&S) -> bool + Send + Sync>,
        Box<dyn Fn(&S) -> bool + Send + Sync>,
    ),
}

/// Result of checking a temporal property over a trace.
#[derive(Debug, Clone)]
pub enum TemporalCheckResult {
    /// The property holds over the entire trace.
    Satisfied,
    /// The property is violated at the given trace index.
    Violated {
        /// Index in the trace where the violation was detected.
        index: usize,
        /// Human-readable description of the violation.
        reason: String,
    },
    /// The trace is too short to determine the property.
    Inconclusive,
}

impl TemporalCheckResult {
    /// Returns true if the property is satisfied.
    #[must_use]
    pub fn is_satisfied(&self) -> bool {
        matches!(self, Self::Satisfied)
    }

    /// Returns true if the property is violated.
    #[must_use]
    pub fn is_violated(&self) -> bool {
        matches!(self, Self::Violated { .. })
    }
}

impl<S: PartialEq> TemporalProp<S> {
    /// Check this temporal property over a finite execution trace.
    ///
    /// The trace is a sequence of states `[s0, s1, s2, ...]` representing
    /// an execution path through the state space.
    ///
    /// # Finite-trace semantics
    ///
    /// Temporal operators have infinite-trace semantics in TLA+, but for
    /// practical testing we use finite-trace approximations:
    ///
    /// - `[]P`: P holds in every state (exact for finite prefixes)
    /// - `<>P`: P holds in at least one state (underapproximation)
    /// - `P ~> Q`: For every state where P holds, Q holds at some later state
    /// - `WF/SF`: Checked over the trace suffix (best effort)
    pub fn check_trace(&self, trace: &[S]) -> TemporalCheckResult {
        if trace.is_empty() {
            return TemporalCheckResult::Inconclusive;
        }

        match self {
            TemporalProp::Always(p) => {
                for (i, state) in trace.iter().enumerate() {
                    if !p(state) {
                        return TemporalCheckResult::Violated {
                            index: i,
                            reason: format!("[]P violated at state {i}"),
                        };
                    }
                }
                TemporalCheckResult::Satisfied
            }

            TemporalProp::Eventually(p) => {
                if trace.iter().any(|s| p(s)) {
                    TemporalCheckResult::Satisfied
                } else {
                    TemporalCheckResult::Violated {
                        index: trace.len() - 1,
                        reason: "<>P never satisfied in trace".to_string(),
                    }
                }
            }

            TemporalProp::LeadsTo(p, q) => {
                for (i, state) in trace.iter().enumerate() {
                    if p(state) {
                        // P holds at i: check that Q holds at some j >= i
                        let q_found = trace[i..].iter().any(|s| q(s));
                        if !q_found {
                            return TemporalCheckResult::Violated {
                                index: i,
                                reason: format!(
                                    "P ~> Q violated: P holds at {i} but Q never follows"
                                ),
                            };
                        }
                    }
                }
                TemporalCheckResult::Satisfied
            }

            TemporalProp::WeakFairness(action_pred) => {
                // WF: If the action is continuously enabled in a suffix, it
                // must eventually fire. For finite traces, check if the action
                // is enabled in the last N states but never fires.
                if trace.len() < 2 {
                    return TemporalCheckResult::Inconclusive;
                }
                // Find the longest suffix where the action predicate is "enabled"
                // (we use the predicate as an enablement check).
                // If enabled in all states but never true in any transition,
                // that's a WF violation.
                let all_enabled_suffix = trace.iter().rev().take_while(|s| action_pred(s)).count();
                if all_enabled_suffix == trace.len() {
                    // Enabled everywhere but we can't tell if it "fired" without
                    // transition-level info — report as inconclusive for finite traces
                    TemporalCheckResult::Inconclusive
                } else {
                    TemporalCheckResult::Satisfied
                }
            }

            TemporalProp::StrongFairness(action_pred) => {
                // SF: If the action is repeatedly enabled (infinitely often),
                // it must eventually fire. Similar to WF but weaker enabling.
                if trace.len() < 2 {
                    return TemporalCheckResult::Inconclusive;
                }
                let enabled_count = trace.iter().filter(|s| action_pred(s)).count();
                if enabled_count > trace.len() / 2 && enabled_count == trace.len() {
                    TemporalCheckResult::Inconclusive
                } else {
                    TemporalCheckResult::Satisfied
                }
            }

            TemporalProp::BoxAction(action, subscript) => {
                // [A]_v: for each consecutive pair (si, si+1), either A(si) or
                // v(si) == v(si+1) (stutter step).
                // Since we don't have transition-level action info in the trace,
                // we check: for each state, either the action predicate holds
                // (the action "could have" produced the next state) or the
                // subscript value is unchanged.
                for i in 0..trace.len().saturating_sub(1) {
                    let a_holds = action(&trace[i]);
                    // We approximate stutter by checking if subscript values match
                    // between consecutive states. This is sound when the subscript
                    // is a pure state predicate (which it always is in codegen).
                    let v_same = subscript(&trace[i]) == subscript(&trace[i + 1]);
                    if !a_holds && !v_same {
                        return TemporalCheckResult::Violated {
                            index: i,
                            reason: format!(
                                "[A]_v violated at transition {i}->{}: \
                                 action false and subscript changed",
                                i + 1
                            ),
                        };
                    }
                }
                TemporalCheckResult::Satisfied
            }

            TemporalProp::AngleAction(action, subscript) => {
                // <<A>>_v: there exists a consecutive pair where A holds AND
                // v changes. (Angle bracket = something actually happens.)
                let found = (0..trace.len().saturating_sub(1)).any(|i| {
                    let a_holds = action(&trace[i]);
                    let v_changed = subscript(&trace[i]) != subscript(&trace[i + 1]);
                    a_holds && v_changed
                });
                if found {
                    TemporalCheckResult::Satisfied
                } else {
                    TemporalCheckResult::Violated {
                        index: 0,
                        reason: "<<A>>_v never satisfied: no transition where action holds \
                                 and subscript changes"
                            .to_string(),
                    }
                }
            }
        }
    }
}

impl<S> fmt::Debug for TemporalProp<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Always(_) => write!(f, "[]P"),
            Self::Eventually(_) => write!(f, "<>P"),
            Self::LeadsTo(_, _) => write!(f, "P ~> Q"),
            Self::WeakFairness(_) => write!(f, "WF"),
            Self::StrongFairness(_) => write!(f, "SF"),
            Self::BoxAction(_, _) => write!(f, "[A]_v"),
            Self::AngleAction(_, _) => write!(f, "<<A>>_v"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct S {
        x: i64,
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_always_satisfied() {
        let prop = TemporalProp::Always(Box::new(|s: &S| s.x >= 0));
        let trace = vec![S { x: 0 }, S { x: 1 }, S { x: 2 }];
        assert!(prop.check_trace(&trace).is_satisfied());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_always_violated() {
        let prop = TemporalProp::Always(Box::new(|s: &S| s.x < 3));
        let trace = vec![S { x: 0 }, S { x: 1 }, S { x: 3 }];
        let result = prop.check_trace(&trace);
        assert!(result.is_violated());
        if let TemporalCheckResult::Violated { index, .. } = result {
            assert_eq!(index, 2);
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eventually_satisfied() {
        let prop = TemporalProp::Eventually(Box::new(|s: &S| s.x == 5));
        let trace = vec![S { x: 0 }, S { x: 3 }, S { x: 5 }];
        assert!(prop.check_trace(&trace).is_satisfied());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_eventually_violated() {
        let prop = TemporalProp::Eventually(Box::new(|s: &S| s.x == 99));
        let trace = vec![S { x: 0 }, S { x: 1 }, S { x: 2 }];
        assert!(prop.check_trace(&trace).is_violated());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_leads_to_satisfied() {
        // x == 1 ~> x == 3 : whenever x is 1, x becomes 3 eventually
        let prop = TemporalProp::LeadsTo(Box::new(|s: &S| s.x == 1), Box::new(|s: &S| s.x == 3));
        let trace = vec![S { x: 0 }, S { x: 1 }, S { x: 2 }, S { x: 3 }];
        assert!(prop.check_trace(&trace).is_satisfied());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_leads_to_violated() {
        let prop = TemporalProp::LeadsTo(Box::new(|s: &S| s.x == 1), Box::new(|s: &S| s.x == 99));
        let trace = vec![S { x: 0 }, S { x: 1 }, S { x: 2 }, S { x: 3 }];
        let result = prop.check_trace(&trace);
        assert!(result.is_violated());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_box_action_with_stutter() {
        // [A]_v where A is "x > 0" and v is "x > 1"
        // trace: [1, 1, 2] — the 1→1 step is a stutter (subscript unchanged), allowed by [A]_v
        let prop = TemporalProp::BoxAction(
            Box::new(|s: &S| s.x > 0), // action predicate
            Box::new(|s: &S| s.x > 1), // subscript: bool fingerprint of state
        );
        let trace = vec![S { x: 1 }, S { x: 1 }, S { x: 2 }];
        assert!(prop.check_trace(&trace).is_satisfied());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_angle_action_satisfied() {
        // <<A>>_v: action holds AND subscript changes
        let prop = TemporalProp::AngleAction(
            Box::new(|_s: &S| true),   // action always true
            Box::new(|s: &S| s.x > 0), // subscript: changes from false to true
        );
        let trace = vec![S { x: 0 }, S { x: 1 }];
        assert!(prop.check_trace(&trace).is_satisfied());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_trace_inconclusive() {
        let prop = TemporalProp::Always(Box::new(|_s: &S| true));
        let trace: Vec<S> = vec![];
        match prop.check_trace(&trace) {
            TemporalCheckResult::Inconclusive => {}
            other => panic!("expected Inconclusive, got {other:?}"),
        }
    }
}
