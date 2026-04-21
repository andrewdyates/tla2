// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::VecDeque;
use std::marker::PhantomData;

use crate::traits::{AtomEvaluator, TransitionSystem};

/// CTL formula over caller-defined atom payloads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtlFormula<Atom> {
    /// Atomic state predicate.
    Atom(Atom),
    /// Boolean negation.
    Not(Box<CtlFormula<Atom>>),
    /// Boolean conjunction.
    And(Vec<CtlFormula<Atom>>),
    /// Boolean disjunction.
    Or(Vec<CtlFormula<Atom>>),
    /// EX(phi): some successor satisfies `phi`.
    EX(Box<CtlFormula<Atom>>),
    /// AX(phi): all successors satisfy `phi`.
    AX(Box<CtlFormula<Atom>>),
    /// EF(phi): some path eventually reaches `phi`.
    EF(Box<CtlFormula<Atom>>),
    /// AF(phi): all paths eventually reach `phi`.
    AF(Box<CtlFormula<Atom>>),
    /// EG(phi): some maximal path stays in `phi`.
    EG(Box<CtlFormula<Atom>>),
    /// AG(phi): all maximal paths stay in `phi`.
    AG(Box<CtlFormula<Atom>>),
    /// E[phi U psi]: some path has `phi` until `psi`.
    EU(Box<CtlFormula<Atom>>, Box<CtlFormula<Atom>>),
    /// A[phi U psi]: all paths have `phi` until `psi`.
    AU(Box<CtlFormula<Atom>>, Box<CtlFormula<Atom>>),
}

/// Accessor for successor state IDs stored in graph edges.
pub trait CtlEdge {
    /// Return the successor state ID referenced by this edge.
    fn successor(&self) -> u32;
}

impl CtlEdge for u32 {
    fn successor(&self) -> u32 {
        *self
    }
}

impl<Label> CtlEdge for (u32, Label) {
    fn successor(&self) -> u32 {
        self.0
    }
}

/// Evaluates CTL atoms against explicit states.
pub trait CtlAtomEvaluator<State, Atom>: Send + Sync {
    /// Evaluate `atom` on `state`.
    fn evaluate(&self, state: &State, atom: &Atom) -> bool;
}

impl<State, Atom, F> CtlAtomEvaluator<State, Atom> for F
where
    F: Fn(&State, &Atom) -> bool + Send + Sync,
{
    fn evaluate(&self, state: &State, atom: &Atom) -> bool {
        self(state, atom)
    }
}

/// Indexed explicit graph view consumed by the CTL engine.
pub struct IndexedCtlGraph<'a, State, Edge> {
    states: &'a [State],
    successors: &'a [Vec<Edge>],
    predecessors: &'a [Vec<u32>],
}

impl<'a, State, Edge> IndexedCtlGraph<'a, State, Edge> {
    /// Build a graph view over indexed states and adjacency lists.
    ///
    /// The state, successor, and predecessor arrays must all use the same
    /// stable index space.
    #[must_use]
    pub fn new(
        states: &'a [State],
        successors: &'a [Vec<Edge>],
        predecessors: &'a [Vec<u32>],
    ) -> Self {
        assert!(
            states.len() <= u32::MAX as usize,
            "CTL engine supports at most {} states, got {}",
            u32::MAX,
            states.len()
        );
        assert_eq!(
            successors.len(),
            states.len(),
            "CTL successor adjacency length {} did not match state count {}",
            successors.len(),
            states.len()
        );
        assert_eq!(
            predecessors.len(),
            states.len(),
            "CTL predecessor adjacency length {} did not match state count {}",
            predecessors.len(),
            states.len()
        );
        Self {
            states,
            successors,
            predecessors,
        }
    }

    #[must_use]
    pub fn state_count(&self) -> usize {
        self.states.len()
    }
}

/// Build reverse predecessor adjacency from forward successor adjacency.
#[must_use]
pub fn build_predecessor_adjacency<Edge: CtlEdge>(successors: &[Vec<Edge>]) -> Vec<Vec<u32>> {
    assert!(
        successors.len() <= u32::MAX as usize,
        "CTL engine supports at most {} states, got {}",
        u32::MAX,
        successors.len()
    );

    let mut predecessors = vec![Vec::new(); successors.len()];
    for (state, edges) in successors.iter().enumerate() {
        for edge in edges {
            let successor = edge.successor() as usize;
            assert!(
                successor < successors.len(),
                "CTL successor index {} out of bounds for {} states",
                successor,
                successors.len()
            );
            predecessors[successor].push(state as u32);
        }
    }
    predecessors
}

/// Reusable CTL fixpoint engine over an indexed explicit graph.
pub struct CtlEngine<'a, State, Edge, Atom, Eval> {
    graph: IndexedCtlGraph<'a, State, Edge>,
    atom_evaluator: Eval,
    atom: PhantomData<fn(&Atom)>,
}

impl<'a, State, Edge, Atom, Eval> CtlEngine<'a, State, Edge, Atom, Eval>
where
    Edge: CtlEdge,
    Eval: CtlAtomEvaluator<State, Atom>,
{
    /// Construct a CTL engine over an indexed graph and atom evaluator.
    #[must_use]
    pub fn new(graph: IndexedCtlGraph<'a, State, Edge>, atom_evaluator: Eval) -> Self {
        Self {
            graph,
            atom_evaluator,
            atom: PhantomData,
        }
    }

    /// Evaluate a CTL formula to a satisfying-state bitset.
    #[must_use]
    pub fn eval(&self, formula: &CtlFormula<Atom>) -> Vec<bool> {
        match formula {
            CtlFormula::Atom(atom) => self.eval_atom(atom),
            CtlFormula::Not(inner) => self.eval(inner).into_iter().map(|value| !value).collect(),
            CtlFormula::And(children) => self.eval_nary_and(children),
            CtlFormula::Or(children) => self.eval_nary_or(children),
            CtlFormula::EX(inner) => {
                let sat = self.eval(inner);
                self.pre_e(&sat)
            }
            CtlFormula::AX(inner) => {
                let sat = self.eval(inner);
                self.pre_a(&sat)
            }
            CtlFormula::EF(inner) => {
                let sat = self.eval(inner);
                self.lfp_ef(&sat)
            }
            CtlFormula::AF(inner) => {
                let sat = self.eval(inner);
                let not_sat: Vec<bool> = sat.iter().map(|&value| !value).collect();
                let eg_not = self.gfp_eg(&not_sat);
                eg_not.into_iter().map(|value| !value).collect()
            }
            CtlFormula::EG(inner) => {
                let sat = self.eval(inner);
                self.gfp_eg(&sat)
            }
            CtlFormula::AG(inner) => {
                let sat = self.eval(inner);
                let not_sat: Vec<bool> = sat.iter().map(|&value| !value).collect();
                let ef_not = self.lfp_ef(&not_sat);
                ef_not.into_iter().map(|value| !value).collect()
            }
            CtlFormula::EU(phi, psi) => {
                let sat_phi = self.eval(phi);
                let sat_psi = self.eval(psi);
                self.lfp_eu(&sat_phi, &sat_psi)
            }
            CtlFormula::AU(phi, psi) => {
                let sat_phi = self.eval(phi);
                let sat_psi = self.eval(psi);
                let not_phi: Vec<bool> = sat_phi.iter().map(|&value| !value).collect();
                let not_psi: Vec<bool> = sat_psi.iter().map(|&value| !value).collect();
                let not_phi_and_not_psi: Vec<bool> = (0..self.state_count())
                    .map(|index| not_phi[index] && not_psi[index])
                    .collect();
                let eu = self.lfp_eu(&not_psi, &not_phi_and_not_psi);
                let eg = self.gfp_eg(&not_psi);
                (0..self.state_count())
                    .map(|index| !(eu[index] || eg[index]))
                    .collect()
            }
        }
    }

    /// EX: states with some successor satisfying `sat`.
    ///
    /// Deadlock states have no successors, so `EX` is false there.
    #[must_use]
    pub fn pre_e(&self, sat: &[bool]) -> Vec<bool> {
        self.assert_sat_len(sat);

        let mut result = vec![false; self.state_count()];
        for (res, adj) in result.iter_mut().zip(self.graph.successors.iter()) {
            if !adj.is_empty() {
                for edge in adj {
                    if sat[edge.successor() as usize] {
                        *res = true;
                        break;
                    }
                }
            }
        }
        result
    }

    /// AX: states where all successors satisfy `sat`.
    ///
    /// Deadlock states have no successors, so `AX` is vacuously true there.
    #[must_use]
    pub fn pre_a(&self, sat: &[bool]) -> Vec<bool> {
        self.assert_sat_len(sat);

        let mut result = vec![false; self.state_count()];
        for (res, adj) in result.iter_mut().zip(self.graph.successors.iter()) {
            if adj.is_empty() {
                *res = true;
            } else {
                *res = adj.iter().all(|edge| sat[edge.successor() as usize]);
            }
        }
        result
    }

    /// EF: backward BFS from `sat` states (least fixpoint μZ. sat ∨ EX(Z)).
    #[must_use]
    pub fn lfp_ef(&self, sat: &[bool]) -> Vec<bool> {
        self.assert_sat_len(sat);

        let mut result = sat.to_vec();
        let mut queue: VecDeque<u32> = VecDeque::new();
        for (state, &is_sat) in result.iter().enumerate() {
            if is_sat {
                queue.push_back(state as u32);
            }
        }
        while let Some(state) = queue.pop_front() {
            for &predecessor in &self.graph.predecessors[state as usize] {
                if !result[predecessor as usize] {
                    result[predecessor as usize] = true;
                    queue.push_back(predecessor);
                }
            }
        }
        result
    }

    /// EG: greatest fixpoint νZ. sat ∧ EX(Z).
    ///
    /// Deadlock states use maximal-path semantics: they remain in the result
    /// iff `sat` already holds there.
    #[must_use]
    pub fn gfp_eg(&self, sat: &[bool]) -> Vec<bool> {
        self.assert_sat_len(sat);

        let mut current = sat.to_vec();
        let mut succ_in_set: Vec<u32> = vec![0; self.state_count()];
        let mut queue: VecDeque<u32> = VecDeque::new();

        for state in 0..self.state_count() {
            if !current[state] {
                continue;
            }
            if self.graph.successors[state].is_empty() {
                succ_in_set[state] = u32::MAX;
                continue;
            }
            let count = self.graph.successors[state]
                .iter()
                .filter(|edge| current[edge.successor() as usize])
                .count() as u32;
            succ_in_set[state] = count;
            if count == 0 {
                queue.push_back(state as u32);
            }
        }

        while let Some(state) = queue.pop_front() {
            let state_idx = state as usize;
            if !current[state_idx] {
                continue;
            }
            current[state_idx] = false;
            for &predecessor in &self.graph.predecessors[state_idx] {
                let pred_idx = predecessor as usize;
                if !current[pred_idx] || succ_in_set[pred_idx] == u32::MAX {
                    continue;
                }
                succ_in_set[pred_idx] = succ_in_set[pred_idx].saturating_sub(1);
                if succ_in_set[pred_idx] == 0 {
                    queue.push_back(predecessor);
                }
            }
        }

        current
    }

    /// E[phi U psi]: backward BFS from `psi` states through `phi` states.
    #[must_use]
    pub fn lfp_eu(&self, sat_phi: &[bool], sat_psi: &[bool]) -> Vec<bool> {
        self.assert_sat_len(sat_phi);
        self.assert_sat_len(sat_psi);

        let mut result = sat_psi.to_vec();
        let mut queue: VecDeque<u32> = VecDeque::new();
        for (state, &is_sat) in result.iter().enumerate() {
            if is_sat {
                queue.push_back(state as u32);
            }
        }
        while let Some(state) = queue.pop_front() {
            for &predecessor in &self.graph.predecessors[state as usize] {
                let predecessor_index = predecessor as usize;
                if !result[predecessor_index] && sat_phi[predecessor_index] {
                    result[predecessor_index] = true;
                    queue.push_back(predecessor);
                }
            }
        }
        result
    }

    fn state_count(&self) -> usize {
        self.graph.state_count()
    }

    fn assert_sat_len(&self, sat: &[bool]) {
        assert_eq!(
            sat.len(),
            self.state_count(),
            "CTL bitset length {} did not match graph state count {}",
            sat.len(),
            self.state_count()
        );
    }

    fn eval_atom(&self, atom: &Atom) -> Vec<bool> {
        self.graph
            .states
            .iter()
            .map(|state| self.atom_evaluator.evaluate(state, atom))
            .collect()
    }

    fn eval_nary_and(&self, children: &[CtlFormula<Atom>]) -> Vec<bool> {
        let Some((first, rest)) = children.split_first() else {
            return vec![true; self.state_count()];
        };

        let mut result = self.eval(first);
        for child in rest {
            let sat = self.eval(child);
            for (value, child_sat) in result.iter_mut().zip(sat) {
                *value &= child_sat;
            }
            if result.iter().all(|&value| !value) {
                break;
            }
        }
        result
    }

    fn eval_nary_or(&self, children: &[CtlFormula<Atom>]) -> Vec<bool> {
        let Some((first, rest)) = children.split_first() else {
            return vec![false; self.state_count()];
        };

        let mut result = self.eval(first);
        for child in rest {
            let sat = self.eval(child);
            for (value, child_sat) in result.iter_mut().zip(sat) {
                *value |= child_sat;
            }
            if result.iter().all(|&value| value) {
                break;
            }
        }
        result
    }
}

// ---------------------------------------------------------------------------
// TransitionSystem bridge
// ---------------------------------------------------------------------------

/// Adapter that bridges [`AtomEvaluator<TS>`] to [`CtlAtomEvaluator`].
///
/// This allows callers that already have a `TransitionSystem` + `AtomEvaluator`
/// pair to use the CTL engine without creating a custom `CtlAtomEvaluator`.
/// Atoms are represented as `usize` indices passed to
/// [`AtomEvaluator::evaluate`].
struct AtomEvalBridge<'a, TS: TransitionSystem> {
    inner: &'a dyn AtomEvaluator<TS>,
}

impl<TS: TransitionSystem> CtlAtomEvaluator<TS::State, usize> for AtomEvalBridge<'_, TS> {
    fn evaluate(&self, state: &TS::State, atom: &usize) -> bool {
        self.inner.evaluate(state, *atom)
    }
}

/// Evaluate a CTL formula over an explicit state graph using the
/// [`TransitionSystem`] / [`AtomEvaluator`] trait pair.
///
/// This is a convenience entry point that builds a [`CtlEngine`] internally.
/// Atoms in the formula are `usize` identifiers resolved by `atom_eval`.
///
/// # Arguments
///
/// - `states` -- all reachable states, indexed `0..N`.
/// - `successors` -- `successors[i]` lists successor state indices for state
///   `i`.
/// - `predecessors` -- `predecessors[i]` lists predecessor state indices for
///   state `i`.
/// - `formula` -- the CTL formula to evaluate.
/// - `atom_eval` -- evaluator for atomic propositions.
///
/// # Returns
///
/// A `Vec<bool>` of length `N` where entry `i` is `true` iff `states[i]`
/// satisfies the formula.
#[must_use]
pub fn check_ctl<TS: TransitionSystem>(
    states: &[TS::State],
    successors: &[Vec<u32>],
    predecessors: &[Vec<u32>],
    formula: &CtlFormula<usize>,
    atom_eval: &dyn AtomEvaluator<TS>,
) -> Vec<bool> {
    let graph = IndexedCtlGraph::new(states, successors, predecessors);
    let bridge = AtomEvalBridge::<TS> { inner: atom_eval };
    let engine = CtlEngine::new(graph, bridge);
    engine.eval(formula)
}

#[cfg(test)]
mod tests {
    use super::{
        build_predecessor_adjacency, CtlAtomEvaluator, CtlEdge, CtlEngine, CtlFormula,
        IndexedCtlGraph,
    };

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct TestState(Vec<u8>);

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct AtLeast {
        index: usize,
        value: u8,
    }

    #[derive(Clone, Copy)]
    struct StateAtomEval;

    impl CtlAtomEvaluator<TestState, AtLeast> for StateAtomEval {
        fn evaluate(&self, state: &TestState, atom: &AtLeast) -> bool {
            state.0[atom.index] >= atom.value
        }
    }

    fn atom(index: usize, value: u8) -> CtlFormula<AtLeast> {
        CtlFormula::Atom(AtLeast { index, value })
    }

    fn engine(
        successors: Vec<Vec<(u32, &'static str)>>,
        states: Vec<TestState>,
    ) -> CtlEngine<'static, TestState, (u32, &'static str), AtLeast, StateAtomEval> {
        let successors = Box::leak(Box::new(successors));
        let predecessors = Box::leak(Box::new(build_predecessor_adjacency(successors)));
        let states = Box::leak(Box::new(states));
        let graph = IndexedCtlGraph::new(states, successors, predecessors);
        CtlEngine::new(graph, StateAtomEval)
    }

    #[test]
    fn predecessor_adjacency_accepts_labeled_edges() {
        let predecessors =
            build_predecessor_adjacency(&[vec![(1, "a"), (2, "b")], vec![(2, "c")], vec![]]);
        assert_eq!(predecessors, vec![vec![], vec![0], vec![0, 1]]);
    }

    #[test]
    fn deadlock_semantics_match_mcc_rules() {
        let engine = engine(vec![vec![]], vec![TestState(vec![1])]);

        assert_eq!(
            engine.eval(&CtlFormula::EX(Box::new(atom(0, 1)))),
            vec![false]
        );
        assert_eq!(
            engine.eval(&CtlFormula::AX(Box::new(atom(0, 1)))),
            vec![true]
        );
        assert_eq!(
            engine.eval(&CtlFormula::EG(Box::new(atom(0, 1)))),
            vec![true]
        );
        assert_eq!(
            engine.eval(&CtlFormula::AG(Box::new(atom(0, 1)))),
            vec![true]
        );

        assert_eq!(
            engine.eval(&CtlFormula::EX(Box::new(atom(0, 2)))),
            vec![false]
        );
        assert_eq!(
            engine.eval(&CtlFormula::AX(Box::new(atom(0, 2)))),
            vec![true]
        );
        assert_eq!(
            engine.eval(&CtlFormula::EG(Box::new(atom(0, 2)))),
            vec![false]
        );
        assert_eq!(
            engine.eval(&CtlFormula::AG(Box::new(atom(0, 2)))),
            vec![false]
        );
    }

    #[test]
    fn until_and_fixpoints_follow_existing_semantics() {
        let engine = engine(
            vec![
                vec![(1, "a"), (2, "b")],
                vec![(3, "c")],
                vec![(2, "d")],
                vec![(3, "e")],
            ],
            vec![
                TestState(vec![1, 0]),
                TestState(vec![1, 1]),
                TestState(vec![0, 0]),
                TestState(vec![0, 1]),
            ],
        );

        let phi = atom(0, 1);
        let psi = atom(1, 1);
        let direct = CtlFormula::AU(Box::new(phi.clone()), Box::new(psi.clone()));
        let rewritten = CtlFormula::Not(Box::new(CtlFormula::Or(vec![
            CtlFormula::EU(
                Box::new(CtlFormula::Not(Box::new(psi.clone()))),
                Box::new(CtlFormula::And(vec![
                    CtlFormula::Not(Box::new(phi.clone())),
                    CtlFormula::Not(Box::new(psi.clone())),
                ])),
            ),
            CtlFormula::EG(Box::new(CtlFormula::Not(Box::new(psi.clone())))),
        ])));

        assert_eq!(engine.eval(&direct), engine.eval(&rewritten));
        assert_eq!(engine.eval(&direct), vec![false, true, false, true]);
    }

    #[test]
    fn edge_trait_supports_plain_successor_ids() {
        assert_eq!(7u32.successor(), 7);
    }

    // -----------------------------------------------------------------------
    // Comprehensive per-operator tests on small graphs
    // -----------------------------------------------------------------------

    // Helper: build engine from plain u32 adjacency (no labels).
    fn engine_plain(
        adj: Vec<Vec<u32>>,
        states: Vec<TestState>,
    ) -> CtlEngine<'static, TestState, u32, AtLeast, StateAtomEval> {
        let adj = Box::leak(Box::new(adj));
        let predecessors = Box::leak(Box::new(build_predecessor_adjacency::<u32>(adj)));
        let states = Box::leak(Box::new(states));
        let graph = IndexedCtlGraph::new(states, adj, predecessors);
        CtlEngine::new(graph, StateAtomEval)
    }

    // ---- Atom / Not / And / Or ----

    #[test]
    fn atom_evaluation_basic() {
        // 3-state linear: 0->1->2(deadlock), values [0], [1], [2]
        let e = engine_plain(
            vec![vec![1], vec![2], vec![]],
            vec![TestState(vec![0]), TestState(vec![1]), TestState(vec![2])],
        );
        // atom(0,1): state.0[0] >= 1 => {1,2}
        assert_eq!(e.eval(&atom(0, 1)), vec![false, true, true]);
        // atom(0,2): state.0[0] >= 2 => {2}
        assert_eq!(e.eval(&atom(0, 2)), vec![false, false, true]);
    }

    #[test]
    fn not_inverts_satisfaction() {
        let e = engine_plain(
            vec![vec![1], vec![]],
            vec![TestState(vec![0]), TestState(vec![1])],
        );
        assert_eq!(
            e.eval(&CtlFormula::Not(Box::new(atom(0, 1)))),
            vec![true, false]
        );
    }

    #[test]
    fn and_intersection() {
        // 3 states with two-element vectors
        let e = engine_plain(
            vec![vec![1], vec![2], vec![]],
            vec![
                TestState(vec![1, 0]),
                TestState(vec![0, 1]),
                TestState(vec![1, 1]),
            ],
        );
        // atom(0,1) AND atom(1,1): only state 2 has both >= 1
        let f = CtlFormula::And(vec![atom(0, 1), atom(1, 1)]);
        assert_eq!(e.eval(&f), vec![false, false, true]);
    }

    #[test]
    fn or_union() {
        let e = engine_plain(
            vec![vec![1], vec![2], vec![]],
            vec![
                TestState(vec![1, 0]),
                TestState(vec![0, 1]),
                TestState(vec![0, 0]),
            ],
        );
        // atom(0,1) OR atom(1,1): states 0 and 1
        let f = CtlFormula::Or(vec![atom(0, 1), atom(1, 1)]);
        assert_eq!(e.eval(&f), vec![true, true, false]);
    }

    #[test]
    fn and_empty_is_true_everywhere() {
        let e = engine_plain(vec![vec![0]], vec![TestState(vec![0])]);
        assert_eq!(e.eval(&CtlFormula::And(vec![])), vec![true]);
    }

    #[test]
    fn or_empty_is_false_everywhere() {
        let e = engine_plain(vec![vec![0]], vec![TestState(vec![0])]);
        assert_eq!(e.eval(&CtlFormula::Or(vec![])), vec![false]);
    }

    // ---- EX ----

    #[test]
    fn ex_some_successor_satisfies() {
        // 0->{1,2}, 1->1, 2(deadlock). Values: [0], [1], [0].
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![]],
            vec![TestState(vec![0]), TestState(vec![1]), TestState(vec![0])],
        );
        // EX(atom(0,1)): successor with val >= 1
        // State 0: succs {1,2}. State 1 has [1] => true
        // State 1: succs {1}. Self-loop [1] => true
        // State 2: deadlock => false
        assert_eq!(
            e.eval(&CtlFormula::EX(Box::new(atom(0, 1)))),
            vec![true, true, false]
        );
    }

    #[test]
    fn ex_at_deadlock_is_false() {
        let e = engine_plain(vec![vec![]], vec![TestState(vec![1])]);
        assert_eq!(e.eval(&CtlFormula::EX(Box::new(atom(0, 1)))), vec![false]);
    }

    // ---- AX ----

    #[test]
    fn ax_all_successors_satisfy() {
        // 0->{1,2}, 1->1, 2(deadlock). Values: [0], [1], [0].
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![]],
            vec![TestState(vec![0]), TestState(vec![1]), TestState(vec![0])],
        );
        // AX(atom(0,1)):
        // State 0: succs {1,2}; state 2 is [0] => not all => false
        // State 1: succs {1}; [1] => true
        // State 2: deadlock => vacuously true
        assert_eq!(
            e.eval(&CtlFormula::AX(Box::new(atom(0, 1)))),
            vec![false, true, true]
        );
    }

    #[test]
    fn ax_ex_duality() {
        // AX(phi) == NOT EX(NOT phi) on non-deadlock states; at deadlock both
        // AX=true and NOT EX(NOT phi)=NOT false=true, so duality holds.
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![2]],
            vec![TestState(vec![0]), TestState(vec![1]), TestState(vec![0])],
        );
        let phi = atom(0, 1);
        let ax_sat = e.eval(&CtlFormula::AX(Box::new(phi.clone())));
        let dual = e.eval(&CtlFormula::Not(Box::new(CtlFormula::EX(Box::new(
            CtlFormula::Not(Box::new(phi)),
        )))));
        assert_eq!(ax_sat, dual);
    }

    // ---- EF ----

    #[test]
    fn ef_backward_reachability() {
        // 0->1->2(deadlock). Atom true only at state 2.
        let e = engine_plain(
            vec![vec![1], vec![2], vec![]],
            vec![TestState(vec![0]), TestState(vec![0]), TestState(vec![1])],
        );
        // EF(atom(0,1)): can reach state 2?
        // 0->1->2 => all can reach => [true, true, true]
        assert_eq!(
            e.eval(&CtlFormula::EF(Box::new(atom(0, 1)))),
            vec![true, true, true]
        );
    }

    #[test]
    fn ef_unreachable() {
        // 0->1->1(self-loop), 2(deadlock isolated). Atom true only at 2.
        // But 0 and 1 cannot reach 2.
        let e = engine_plain(
            vec![vec![1], vec![1], vec![]],
            vec![TestState(vec![0]), TestState(vec![0]), TestState(vec![1])],
        );
        // EF(atom(0,1)):
        // State 2: atom true => EF true
        // States 0,1: can only reach each other => EF false
        assert_eq!(
            e.eval(&CtlFormula::EF(Box::new(atom(0, 1)))),
            vec![false, false, true]
        );
    }

    // ---- AF ----

    #[test]
    fn af_all_paths_reach() {
        // 0->{1,2}, 1->3, 2->3, 3(deadlock). Atom true at 3.
        // All paths from any state reach 3.
        let e = engine_plain(
            vec![vec![1, 2], vec![3], vec![3], vec![]],
            vec![
                TestState(vec![0]),
                TestState(vec![0]),
                TestState(vec![0]),
                TestState(vec![1]),
            ],
        );
        assert_eq!(
            e.eval(&CtlFormula::AF(Box::new(atom(0, 1)))),
            vec![true, true, true, true]
        );
    }

    #[test]
    fn af_some_path_avoids() {
        // 0->{1,2}, 1->1(self-loop), 2(deadlock). Atom true at 2.
        // Path 0->1->1->... never reaches 2. AF = false at 0 and 1.
        // But wait, AF means "on ALL paths, eventually". State 0 has path
        // 0->1->1->... which never reaches atom. But atom holds at 0? No, atom
        // is true only at 2. So AF(atom) at 0: path 0->2 reaches it, but path
        // 0->1->1->... doesn't. => false.
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![]],
            vec![TestState(vec![0]), TestState(vec![0]), TestState(vec![1])],
        );
        // AF at 0: false (path 0->1->... avoids)
        // AF at 1: false (self-loop, never reaches)
        // AF at 2: true (holds here)
        assert_eq!(
            e.eval(&CtlFormula::AF(Box::new(atom(0, 1)))),
            vec![false, false, true]
        );
    }

    #[test]
    fn af_eg_duality() {
        // AF(phi) == NOT EG(NOT phi)
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![2]],
            vec![TestState(vec![0]), TestState(vec![1]), TestState(vec![0])],
        );
        let phi = atom(0, 1);
        let af_sat = e.eval(&CtlFormula::AF(Box::new(phi.clone())));
        let dual = e.eval(&CtlFormula::Not(Box::new(CtlFormula::EG(Box::new(
            CtlFormula::Not(Box::new(phi)),
        )))));
        assert_eq!(af_sat, dual);
    }

    // ---- EG ----

    #[test]
    fn eg_cycle_keeps_all() {
        // Cycle: 0->1->2->0. All states satisfy atom.
        let e = engine_plain(
            vec![vec![1], vec![2], vec![0]],
            vec![TestState(vec![1]), TestState(vec![1]), TestState(vec![1])],
        );
        // EG(atom): infinite path cycling => all true
        assert_eq!(
            e.eval(&CtlFormula::EG(Box::new(atom(0, 1)))),
            vec![true, true, true]
        );
    }

    #[test]
    fn eg_breaks_at_non_satisfying_successor() {
        // 0->1->2(deadlock). All satisfy atom but 2 is deadlock with atom=false.
        // Wait, need to be careful with maximal-path semantics.
        // Let's have: 0->1->2(deadlock), atom true at {0,1}, false at {2}.
        // EG: 2 is deadlock, atom=false => not in set.
        // 1: only succ=2, not in set => removed.
        // 0: only succ=1, not in set => removed.
        let e = engine_plain(
            vec![vec![1], vec![2], vec![]],
            vec![TestState(vec![1]), TestState(vec![1]), TestState(vec![0])],
        );
        assert_eq!(
            e.eval(&CtlFormula::EG(Box::new(atom(0, 1)))),
            vec![false, false, false]
        );
    }

    #[test]
    fn eg_deadlock_maximal_path_semantics() {
        // Single deadlock state, atom=true => stays (path=[s]).
        let e = engine_plain(vec![vec![]], vec![TestState(vec![1])]);
        assert_eq!(e.eval(&CtlFormula::EG(Box::new(atom(0, 1)))), vec![true]);
        // atom=false => gone
        let e2 = engine_plain(vec![vec![]], vec![TestState(vec![0])]);
        assert_eq!(e2.eval(&CtlFormula::EG(Box::new(atom(0, 1)))), vec![false]);
    }

    #[test]
    fn eg_branch_to_cycle_and_deadlock() {
        // 0->{1,2}, 1->1 (self-loop), 2(deadlock).
        // atom true at {0,1,2}.
        // EG(atom):
        //   State 2: deadlock, atom=true => stays (maximal path).
        //   State 1: self-loop, atom=true => stays.
        //   State 0: succ {1,2}, both in set => stays.
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![]],
            vec![TestState(vec![1]), TestState(vec![1]), TestState(vec![1])],
        );
        assert_eq!(
            e.eval(&CtlFormula::EG(Box::new(atom(0, 1)))),
            vec![true, true, true]
        );
    }

    // ---- AG ----

    #[test]
    fn ag_globally_true() {
        // Cycle: all satisfy atom => AG true everywhere
        let e = engine_plain(
            vec![vec![1], vec![0]],
            vec![TestState(vec![1]), TestState(vec![1])],
        );
        assert_eq!(
            e.eval(&CtlFormula::AG(Box::new(atom(0, 1)))),
            vec![true, true]
        );
    }

    #[test]
    fn ag_reachable_violation() {
        // 0->1->2(deadlock). Atom false at 2.
        // AG(atom): from 0 you reach 2 which violates => false at {0,1}.
        let e = engine_plain(
            vec![vec![1], vec![2], vec![]],
            vec![TestState(vec![1]), TestState(vec![1]), TestState(vec![0])],
        );
        assert_eq!(
            e.eval(&CtlFormula::AG(Box::new(atom(0, 1)))),
            vec![false, false, false]
        );
    }

    #[test]
    fn ag_ef_not_duality() {
        // AG(phi) == NOT EF(NOT phi)
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![]],
            vec![TestState(vec![1]), TestState(vec![1]), TestState(vec![0])],
        );
        let phi = atom(0, 1);
        let ag = e.eval(&CtlFormula::AG(Box::new(phi.clone())));
        let dual = e.eval(&CtlFormula::Not(Box::new(CtlFormula::EF(Box::new(
            CtlFormula::Not(Box::new(phi)),
        )))));
        assert_eq!(ag, dual);
    }

    // ---- EU ----

    #[test]
    fn eu_phi_until_psi_basic() {
        // 0->1->2(deadlock). States: [1,0], [1,0], [0,1].
        // EU(atom(0,1), atom(1,1)): phi holds at {0,1}, psi at {2}.
        // Backward from 2: pred=1, phi[1]=true => add; pred of 1=0, phi[0]=true => add.
        let e = engine_plain(
            vec![vec![1], vec![2], vec![]],
            vec![
                TestState(vec![1, 0]),
                TestState(vec![1, 0]),
                TestState(vec![0, 1]),
            ],
        );
        assert_eq!(
            e.eval(&CtlFormula::EU(Box::new(atom(0, 1)), Box::new(atom(1, 1)))),
            vec![true, true, true]
        );
    }

    #[test]
    fn eu_phi_breaks_midway() {
        // 0->1->2(deadlock). States: [1,0], [0,0], [0,1].
        // phi at {0}, psi at {2}. But state 1 has phi=false => can't propagate.
        let e = engine_plain(
            vec![vec![1], vec![2], vec![]],
            vec![
                TestState(vec![1, 0]),
                TestState(vec![0, 0]),
                TestState(vec![0, 1]),
            ],
        );
        assert_eq!(
            e.eval(&CtlFormula::EU(Box::new(atom(0, 1)), Box::new(atom(1, 1)))),
            vec![false, false, true]
        );
    }

    #[test]
    fn eu_psi_holds_immediately() {
        // E[phi U psi]: if psi holds at a state, EU is true regardless of phi.
        let e = engine_plain(
            vec![vec![1], vec![]],
            vec![TestState(vec![0, 1]), TestState(vec![0, 1])],
        );
        assert_eq!(
            e.eval(&CtlFormula::EU(
                Box::new(atom(0, 1)), // phi=false
                Box::new(atom(1, 1))  // psi=true
            )),
            vec![true, true]
        );
    }

    // ---- AU ----

    #[test]
    fn au_all_paths_phi_until_psi() {
        // 0->{1,2}, 1->3, 2->3, 3(deadlock). phi at {0,1,2}, psi at {3}.
        // All paths from 0 go through phi-states until reaching psi=3.
        let e = engine_plain(
            vec![vec![1, 2], vec![3], vec![3], vec![]],
            vec![
                TestState(vec![1, 0]),
                TestState(vec![1, 0]),
                TestState(vec![1, 0]),
                TestState(vec![0, 1]),
            ],
        );
        assert_eq!(
            e.eval(&CtlFormula::AU(Box::new(atom(0, 1)), Box::new(atom(1, 1)))),
            vec![true, true, true, true]
        );
    }

    #[test]
    fn au_one_path_escapes() {
        // 0->{1,2}, 1->1(self-loop), 2(deadlock). phi at {0,1}, psi at {2}.
        // Path 0->1->1->... never reaches psi => AU false at 0.
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![]],
            vec![
                TestState(vec![1, 0]),
                TestState(vec![1, 0]),
                TestState(vec![0, 1]),
            ],
        );
        // State 0: path 0->1->1->... avoids psi => false
        // State 1: self-loop, never reaches psi => false
        // State 2: psi holds => true
        assert_eq!(
            e.eval(&CtlFormula::AU(Box::new(atom(0, 1)), Box::new(atom(1, 1)))),
            vec![false, false, true]
        );
    }

    // ---- AU exhaustive cross-validation (small deadlock-free graphs) ----

    fn bitvec(mask: u32, n: usize) -> Vec<bool> {
        (0..n).map(|i| mask & (1 << i) != 0).collect()
    }

    #[test]
    fn au_algebraic_vs_fixpoint_exhaustive_deadlock_free() {
        // On graphs without deadlocks, the algebraic identity used by AU
        // matches the direct fixpoint mu Z. psi | (phi & AX(Z)).
        let graphs: &[(&str, &[&[u32]])] = &[
            ("cycle_3", &[&[1], &[2], &[0]]),
            ("single_cycle", &[&[0]]),
            ("two_cycles", &[&[1, 2], &[0], &[2]]),
        ];

        let mut total = 0;
        for &(name, adj) in graphs {
            let n = adj.len();
            let adj_vec: Vec<Vec<u32>> = adj.iter().map(|s| s.to_vec()).collect();
            let states: Vec<TestState> = (0..n).map(|_| TestState(vec![0])).collect();
            let e = engine_plain(adj_vec, states);

            for phi_mask in 0..(1u32 << n) {
                let phi = bitvec(phi_mask, n);
                for psi_mask in 0..(1u32 << n) {
                    let psi = bitvec(psi_mask, n);

                    // Algebraic AU (as implemented)
                    let not_phi: Vec<bool> = phi.iter().map(|&v| !v).collect();
                    let not_psi: Vec<bool> = psi.iter().map(|&v| !v).collect();
                    let both_not: Vec<bool> = (0..n).map(|i| not_phi[i] && not_psi[i]).collect();
                    let eu_r = e.lfp_eu(&not_psi, &both_not);
                    let eg_r = e.gfp_eg(&not_psi);
                    let alg: Vec<bool> = (0..n).map(|i| !(eu_r[i] || eg_r[i])).collect();

                    // Reference fixpoint: mu Z. psi | (phi & AX(Z))
                    let mut z = vec![false; n];
                    loop {
                        let ax_z = e.pre_a(&z);
                        let new_z: Vec<bool> =
                            (0..n).map(|i| psi[i] || (phi[i] && ax_z[i])).collect();
                        if new_z == z {
                            break;
                        }
                        z = new_z;
                    }

                    assert_eq!(alg, z, "AU mismatch on '{name}': phi={phi:?} psi={psi:?}");
                    total += 1;
                }
            }
        }
        eprintln!("AU exhaustive: {total} checks passed");
    }

    // ---- Nested formulas ----

    #[test]
    fn nested_ag_ef() {
        // 0->{1,2}, 1->1, 2(deadlock). Atom true at {0,1}.
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![]],
            vec![TestState(vec![1]), TestState(vec![1]), TestState(vec![0])],
        );
        // EF(atom) = [true, true, false]
        // AG(EF(atom)): state 0 can reach 2 (EF=false) => AG false at 0
        assert_eq!(
            e.eval(&CtlFormula::AG(Box::new(CtlFormula::EF(Box::new(atom(
                0, 1
            )))))),
            vec![false, true, false]
        );
    }

    #[test]
    fn nested_af_eg() {
        // Same graph.
        let e = engine_plain(
            vec![vec![1, 2], vec![1], vec![]],
            vec![TestState(vec![1]), TestState(vec![1]), TestState(vec![0])],
        );
        // EG(atom) = [true, true, false]
        // AF(EG(atom)): state 0 has EG true => AF true
        assert_eq!(
            e.eval(&CtlFormula::AF(Box::new(CtlFormula::EG(Box::new(atom(
                0, 1
            )))))),
            vec![true, true, false]
        );
    }

    // ---- check_ctl bridge ----

    #[test]
    fn check_ctl_bridge_basic() {
        use crate::{AtomEvaluator, TransitionSystem};

        #[derive(Clone)]
        struct TinyTS;

        impl TransitionSystem for TinyTS {
            type State = u8;
            type Action = ();
            type Fingerprint = u8;

            fn initial_states(&self) -> Vec<u8> {
                vec![0]
            }
            fn successors(&self, _: &u8) -> Vec<((), u8)> {
                Vec::new()
            }
            fn fingerprint(&self, s: &u8) -> u8 {
                *s
            }
        }

        struct TinyEval;
        impl AtomEvaluator<TinyTS> for TinyEval {
            fn evaluate(&self, state: &u8, atom_id: usize) -> bool {
                match atom_id {
                    0 => *state >= 1,
                    _ => false,
                }
            }
        }

        let states: Vec<u8> = vec![0, 1, 2];
        let successors = vec![vec![1u32], vec![2], vec![]];
        let predecessors = build_predecessor_adjacency(&successors);

        // EF(atom 0): state[i] >= 1 at {1,2}. backward: 2<-1<-0.
        let result = super::check_ctl::<TinyTS>(
            &states,
            &successors,
            &predecessors,
            &CtlFormula::EF(Box::new(CtlFormula::Atom(0))),
            &TinyEval,
        );
        assert_eq!(result, vec![true, true, true]);

        // AG(atom 0): state 0 has val=0, atom false => AG false at all
        // reaching 0. State 0 is initial so AG false at 0.
        let result = super::check_ctl::<TinyTS>(
            &states,
            &successors,
            &predecessors,
            &CtlFormula::AG(Box::new(CtlFormula::Atom(0))),
            &TinyEval,
        );
        // Not all reachable states satisfy: state 0 fails.
        // From state 0: atom=false => AG false.
        // From state 1: reaches 2(deadlock) atom=true, and state 1 atom=true => AG true.
        // From state 2: deadlock, atom=true => AG true.
        assert_eq!(result, vec![false, true, true]);
    }

    // ---- Empty graph ----

    #[test]
    fn empty_graph_returns_empty() {
        let e = engine_plain(vec![], vec![]);
        assert_eq!(e.eval(&CtlFormula::And(vec![])), Vec::<bool>::new());
        assert_eq!(
            e.eval(&CtlFormula::EG(Box::new(atom(0, 1)))),
            Vec::<bool>::new()
        );
    }
}
