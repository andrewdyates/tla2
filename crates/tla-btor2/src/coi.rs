// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Cone-of-influence (COI) reduction for BTOR2 programs.
//
// Given a set of target nodes (typically `bad` properties), compute the
// transitive backward cone of influence: only the nodes that can affect
// the target values. States and inputs outside the COI are eliminated,
// reducing the problem size before CHC translation.
//
// This is a standard hardware model checking optimization (see: McMillan,
// "Symbolic Model Checking", 1993). For BTOR2 programs with many state
// variables but few relevant to the property, COI reduction can
// dramatically reduce solver complexity.

use rustc_hash::FxHashSet;

use crate::types::{Btor2Line, Btor2Node, Btor2Program};

/// Result of COI analysis: the set of relevant node IDs.
#[derive(Debug)]
pub(crate) struct CoiResult {
    /// Node IDs in the cone of influence (absolute values).
    pub(crate) relevant_nodes: FxHashSet<i64>,
    /// State node IDs in the cone of influence.
    pub(crate) relevant_states: FxHashSet<i64>,
    /// Input node IDs in the cone of influence.
    pub(crate) relevant_inputs: FxHashSet<i64>,
    /// Number of states eliminated.
    pub(crate) eliminated_states: usize,
    /// Number of inputs eliminated.
    pub(crate) eliminated_inputs: usize,
}

/// Compute the cone of influence for a BTOR2 program's bad properties.
///
/// Starting from each `bad` property's condition node, we transitively
/// follow argument references to discover all nodes that can affect the
/// property. For state variables, we also follow their `next` and `init`
/// expressions (since a state's value depends on nodes in its next-state
/// and initialization functions).
///
/// Constraints are always included in the COI since they restrict the
/// reachable state space globally.
pub(crate) fn compute_coi(program: &Btor2Program) -> CoiResult {
    let mut relevant = FxHashSet::default();
    let mut worklist: Vec<i64> = Vec::new();

    // Build lookup structures.
    let mut line_map: rustc_hash::FxHashMap<i64, &Btor2Line> = rustc_hash::FxHashMap::default();
    let mut state_ids: FxHashSet<i64> = FxHashSet::default();
    let mut input_ids: FxHashSet<i64> = FxHashSet::default();
    // Map: state_node_id -> next_value_node_id
    let mut next_map: rustc_hash::FxHashMap<i64, i64> = rustc_hash::FxHashMap::default();
    // Map: state_node_id -> init_value_node_id
    let mut init_map: rustc_hash::FxHashMap<i64, i64> = rustc_hash::FxHashMap::default();

    for line in &program.lines {
        line_map.insert(line.id, line);
        match &line.node {
            Btor2Node::State(_, _) => {
                state_ids.insert(line.id);
            }
            Btor2Node::Input(_, _) => {
                input_ids.insert(line.id);
            }
            Btor2Node::Next(_sort_id, state_id, next_value_id) => {
                let abs_state = state_id.unsigned_abs() as i64;
                next_map.insert(abs_state, *next_value_id);
            }
            Btor2Node::Init(_sort_id, state_id, init_value_id) => {
                let abs_state = state_id.unsigned_abs() as i64;
                init_map.insert(abs_state, *init_value_id);
            }
            _ => {}
        }
    }

    // Seed: all bad property condition nodes.
    for &bad_line_id in &program.bad_properties {
        if let Some(line) = line_map.get(&bad_line_id) {
            if let Btor2Node::Bad(cond_id) = &line.node {
                let abs = cond_id.unsigned_abs() as i64;
                if relevant.insert(abs) {
                    worklist.push(abs);
                }
            }
        }
    }

    // Seed: all constraint condition nodes (constraints affect reachability).
    for &constraint_line_id in &program.constraints {
        if let Some(line) = line_map.get(&constraint_line_id) {
            if let Btor2Node::Constraint(cond_id) = &line.node {
                let abs = cond_id.unsigned_abs() as i64;
                if relevant.insert(abs) {
                    worklist.push(abs);
                }
            }
        }
    }

    // Fixed-point traversal: follow argument references backward.
    while let Some(node_id) = worklist.pop() {
        if let Some(line) = line_map.get(&node_id) {
            // Follow argument references.
            for &arg in &line.args {
                let abs_arg = arg.unsigned_abs() as i64;
                if relevant.insert(abs_arg) {
                    worklist.push(abs_arg);
                }
            }

            // For state nodes in the COI, also trace their next-state and
            // init-value functions. Both are needed for CHC translation:
            // init determines the starting value, next determines the
            // transition relation.
            if state_ids.contains(&node_id) {
                if let Some(&next_value_id) = next_map.get(&node_id) {
                    let abs_next = next_value_id.unsigned_abs() as i64;
                    if relevant.insert(abs_next) {
                        worklist.push(abs_next);
                    }
                }
                if let Some(&init_value_id) = init_map.get(&node_id) {
                    let abs_init = init_value_id.unsigned_abs() as i64;
                    if relevant.insert(abs_init) {
                        worklist.push(abs_init);
                    }
                }
            }

            // For init/next nodes, trace the value operand.
            match &line.node {
                Btor2Node::Init(_, state_id, value_id) => {
                    let abs_s = state_id.unsigned_abs() as i64;
                    let abs_v = value_id.unsigned_abs() as i64;
                    if relevant.insert(abs_s) {
                        worklist.push(abs_s);
                    }
                    if relevant.insert(abs_v) {
                        worklist.push(abs_v);
                    }
                }
                Btor2Node::Next(_, state_id, value_id) => {
                    let abs_s = state_id.unsigned_abs() as i64;
                    let abs_v = value_id.unsigned_abs() as i64;
                    if relevant.insert(abs_s) {
                        worklist.push(abs_s);
                    }
                    if relevant.insert(abs_v) {
                        worklist.push(abs_v);
                    }
                }
                _ => {}
            }
        }
    }

    // Classify relevant states and inputs.
    let relevant_states: FxHashSet<i64> = state_ids.intersection(&relevant).copied().collect();
    let relevant_inputs: FxHashSet<i64> = input_ids.intersection(&relevant).copied().collect();

    let eliminated_states = state_ids.len() - relevant_states.len();
    let eliminated_inputs = input_ids.len() - relevant_inputs.len();

    CoiResult {
        relevant_nodes: relevant,
        relevant_states,
        relevant_inputs,
        eliminated_states,
        eliminated_inputs,
    }
}

/// Build a reduced BTOR2 program containing only COI-relevant nodes.
///
/// The reduced program preserves all sort definitions (required for
/// type resolution), but only includes state, input, init, next, bad,
/// and constraint nodes that are in the cone of influence.
pub(crate) fn reduce_program(program: &Btor2Program, coi: &CoiResult) -> Btor2Program {
    // If nothing was eliminated, return a clone.
    if coi.eliminated_states == 0 && coi.eliminated_inputs == 0 {
        return program.clone();
    }

    let mut lines = Vec::new();
    let mut num_inputs = 0usize;
    let mut num_states = 0usize;

    for line in &program.lines {
        let dominated_by_irrelevant = match &line.node {
            // State: only include if in COI.
            Btor2Node::State(_, _) => {
                if coi.relevant_states.contains(&line.id) {
                    num_states += 1;
                    false
                } else {
                    true
                }
            }
            // Input: only include if in COI.
            Btor2Node::Input(_, _) => {
                if coi.relevant_inputs.contains(&line.id) {
                    num_inputs += 1;
                    false
                } else {
                    true
                }
            }
            // Init: only include if the state it initializes is in COI.
            Btor2Node::Init(_, state_id, _) => {
                let abs = state_id.unsigned_abs() as i64;
                !coi.relevant_states.contains(&abs)
            }
            // Next: only include if the state it updates is in COI.
            Btor2Node::Next(_, state_id, _) => {
                let abs = state_id.unsigned_abs() as i64;
                !coi.relevant_states.contains(&abs)
            }
            // Sort definitions: always keep (needed for type resolution).
            Btor2Node::SortBitVec(_) | Btor2Node::SortArray(_, _) => false,
            // Bad/Constraint/Fair/Justice/Output: always keep.
            Btor2Node::Bad(_)
            | Btor2Node::Constraint(_)
            | Btor2Node::Fair(_)
            | Btor2Node::Justice(_)
            | Btor2Node::Output(_) => false,
            // Computation nodes: include if referenced by any COI node.
            _ => !coi.relevant_nodes.contains(&line.id),
        };

        if !dominated_by_irrelevant {
            lines.push(line.clone());
        }
    }

    Btor2Program {
        lines,
        sorts: program.sorts.clone(),
        num_inputs,
        num_states,
        bad_properties: program.bad_properties.clone(),
        constraints: program.constraints.clone(),
        fairness: program.fairness.clone(),
        justice: program.justice.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Btor2Sort;
    use std::collections::HashMap;

    fn make_program_with_irrelevant_state() -> Btor2Program {
        // Two states: x (relevant to bad) and y (irrelevant).
        // bad = (x == 1), y is never referenced by bad or x's next function.
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(8));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(8),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 1,
                node: Btor2Node::Zero,
                args: vec![],
            },
            // Relevant state
            Btor2Line {
                id: 3,
                sort_id: 1,
                node: Btor2Node::State(1, Some("x".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 4,
                sort_id: 1,
                node: Btor2Node::Init(1, 3, 2),
                args: vec![3, 2],
            },
            Btor2Line {
                id: 5,
                sort_id: 1,
                node: Btor2Node::Next(1, 3, 2),
                args: vec![3, 2],
            },
            // Irrelevant state
            Btor2Line {
                id: 6,
                sort_id: 1,
                node: Btor2Node::State(1, Some("y".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 7,
                sort_id: 1,
                node: Btor2Node::Init(1, 6, 2),
                args: vec![6, 2],
            },
            Btor2Line {
                id: 8,
                sort_id: 1,
                node: Btor2Node::Next(1, 6, 2),
                args: vec![6, 2],
            },
            // bad = x (i.e., x != 0 would be bad; simplified to just x)
            Btor2Line {
                id: 9,
                sort_id: 0,
                node: Btor2Node::Bad(3),
                args: vec![3],
            },
        ];

        Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 2,
            bad_properties: vec![9],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        }
    }

    #[test]
    fn test_coi_eliminates_irrelevant_state() {
        let program = make_program_with_irrelevant_state();
        let coi = compute_coi(&program);

        assert!(coi.relevant_states.contains(&3), "x should be relevant");
        assert!(!coi.relevant_states.contains(&6), "y should be irrelevant");
        assert_eq!(coi.eliminated_states, 1);
    }

    #[test]
    fn test_reduce_program_removes_irrelevant() {
        let program = make_program_with_irrelevant_state();
        let coi = compute_coi(&program);
        let reduced = reduce_program(&program, &coi);

        assert_eq!(reduced.num_states, 1, "reduced should have 1 state");
        // State y (id=6), its init (id=7), and its next (id=8) should be gone.
        let ids: FxHashSet<i64> = reduced.lines.iter().map(|l| l.id).collect();
        assert!(!ids.contains(&6), "state y should be removed");
        assert!(!ids.contains(&7), "init of y should be removed");
        assert!(!ids.contains(&8), "next of y should be removed");
        // State x and its supporting lines should be present.
        assert!(ids.contains(&3), "state x should remain");
        assert!(ids.contains(&9), "bad should remain");
    }

    #[test]
    fn test_coi_no_elimination_when_all_relevant() {
        // Single state, single bad — nothing to eliminate.
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(1));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(1),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 1,
                node: Btor2Node::State(1, Some("s".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 0,
                node: Btor2Node::Bad(2),
                args: vec![2],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 1,
            bad_properties: vec![3],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        let coi = compute_coi(&program);
        assert_eq!(coi.eliminated_states, 0);
        assert_eq!(coi.eliminated_inputs, 0);
    }

    #[test]
    fn test_coi_includes_transitive_deps() {
        // bad -> cmp -> add -> state_a, state_b
        // Both states should be in COI.
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(8));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(8),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 1,
                node: Btor2Node::State(1, Some("a".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 1,
                node: Btor2Node::State(1, Some("b".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 4,
                sort_id: 1,
                node: Btor2Node::Add,
                args: vec![2, 3],
            },
            Btor2Line {
                id: 5,
                sort_id: 1,
                node: Btor2Node::Eq,
                args: vec![4, 2],
            },
            Btor2Line {
                id: 6,
                sort_id: 0,
                node: Btor2Node::Bad(5),
                args: vec![5],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 2,
            bad_properties: vec![6],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        let coi = compute_coi(&program);
        assert!(coi.relevant_states.contains(&2));
        assert!(coi.relevant_states.contains(&3));
        assert_eq!(coi.eliminated_states, 0);
    }
}
