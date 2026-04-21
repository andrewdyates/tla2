// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Nested powerset encoding for `SUBSET(SUBSET S)` patterns.
//!
//! SpanTreeTest5Nodes has the Init constraint:
//! ```text
//! Edges \in {E \in SUBSET(SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}
//! ```
//!
//! With 5 nodes, `SUBSET Nodes` has 2^5 = 32 elements, and `SUBSET(SUBSET Nodes)`
//! has 2^32 ~ 4 billion elements. But the `Cardinality(e) = 2` filter reduces the
//! base to C(5,2) = 10 edges, making `SUBSET({2-element subsets})` only 2^10 = 1024.
//!
//! # Encoding Strategy
//!
//! Instead of materializing 2^32 sets, we:
//!
//! 1. Compute the filtered base set: all k-element subsets of S (typically k=2)
//! 2. Create one Boolean variable per base element: `edge_i` for i in 0..base_size
//! 3. Optionally assert additional constraints from the spec
//! 4. Use AllSAT to enumerate all satisfying truth assignments
//! 5. Convert each assignment to a set-of-sets value
//!
//! The AllSAT loop uses blocking clauses: after finding a model, we assert
//! NOT(conjunction of all variable assignments) and re-solve.
//!
//! # Complexity
//!
//! For |S| = n and filter to k-element subsets:
//! - Base size: C(n, k)
//! - Enumeration: 2^C(n,k) (1024 for n=5, k=2)
//! - Per-solve cost: O(C(n,k)) variables in the SAT formula
//!
//! This is tractable for n <= ~10 with k=2 (C(10,2) = 45, 2^45 is too large,
//! but additional Init constraints typically prune heavily).
//!
//! Part of #3826.

use z4_dpll::api::{Logic, Model, SolveResult, Solver, Sort, Term};

use crate::error::{Z4Error, Z4Result};

/// Maximum number of base elements for nested powerset enumeration.
///
/// With base_size = 20, we get 2^20 = 1M potential solutions — still tractable
/// for SAT but may be slow. Beyond this, symbolic methods are needed.
pub const MAX_NESTED_POWERSET_BASE: usize = 20;

/// A single base element in the nested powerset encoding.
///
/// For `SUBSET(SUBSET Nodes)` with Cardinality=2 filter, each base element
/// is a 2-element subset of Nodes represented as a sorted pair.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BaseElement {
    /// The members of this subset, sorted for canonical representation.
    pub members: Vec<i64>,
}

/// Configuration for nested powerset enumeration.
#[derive(Debug, Clone)]
pub struct NestedPowersetConfig {
    /// Maximum number of solutions to enumerate (default: 1_000_000).
    pub max_solutions: usize,
    /// Timeout per SAT check (default: None = no timeout).
    pub solve_timeout: Option<std::time::Duration>,
}

impl Default for NestedPowersetConfig {
    fn default() -> Self {
        Self {
            max_solutions: 1_000_000,
            solve_timeout: None,
        }
    }
}

/// Result of nested powerset enumeration: a list of sets-of-sets.
///
/// Each outer element is one satisfying assignment (one value of `Edges`).
/// Each inner element is the set of base elements that are "in" for that assignment.
#[derive(Debug, Clone)]
pub struct NestedPowersetSolution {
    /// Each solution is a set of base elements (e.g., a set of edges).
    pub solutions: Vec<Vec<BaseElement>>,
}

/// Encoder for nested powerset patterns.
///
/// Given a base set of elements (e.g., all 2-element subsets of Nodes),
/// this encoder creates Boolean variables for each base element and
/// enumerates all subsets (with optional constraints) using AllSAT.
pub struct NestedPowersetEncoder {
    /// The SAT solver instance.
    solver: Solver,
    /// Boolean variable for each base element: `base_i` is true iff element i is in the set.
    base_vars: Vec<Term>,
    /// The base elements in order corresponding to `base_vars`.
    base_elements: Vec<BaseElement>,
    /// Counter for fresh variable names.
    fresh_counter: usize,
}

impl NestedPowersetEncoder {
    /// Create a new encoder for the given base elements.
    ///
    /// Each base element gets a fresh Boolean variable.
    ///
    /// # Errors
    /// Returns an error if the number of base elements exceeds `MAX_NESTED_POWERSET_BASE`.
    pub fn new(base_elements: Vec<BaseElement>) -> Z4Result<Self> {
        let n = base_elements.len();
        if n > MAX_NESTED_POWERSET_BASE {
            return Err(Z4Error::UnsupportedOp(format!(
                "nested powerset base has {n} elements, exceeds maximum ({MAX_NESTED_POWERSET_BASE}); \
                 would generate up to 2^{n} solutions"
            )));
        }

        let mut solver = Solver::try_new(Logic::QfLia)?;
        let mut base_vars = Vec::with_capacity(n);

        for i in 0..n {
            let name = format!("__npow_base_{i}");
            let var = solver.declare_const(&name, Sort::Bool);
            base_vars.push(var);
        }

        Ok(Self {
            solver,
            base_vars,
            base_elements,
            fresh_counter: 0,
        })
    }

    /// Get the number of base elements.
    #[must_use]
    pub fn base_size(&self) -> usize {
        self.base_elements.len()
    }

    /// Get a reference to the base elements.
    #[must_use]
    pub fn base_elements(&self) -> &[BaseElement] {
        &self.base_elements
    }

    /// Get the Boolean variable for base element at index `i`.
    ///
    /// Returns `true` in the model iff element `i` is in the chosen subset.
    #[must_use]
    pub fn base_var(&self, i: usize) -> Option<Term> {
        self.base_vars.get(i).copied()
    }

    /// Assert a constraint on the base variables.
    ///
    /// The term must be Bool-sorted and refer to the base variables.
    pub fn assert_constraint(&mut self, term: Term) {
        self.solver
            .try_assert_term(term)
            .expect("invariant: constraint must be Bool-sorted");
    }

    /// Assert that exactly `k` base elements are true (cardinality constraint).
    ///
    /// Encodes: sum(base_vars) = k using integer summation.
    pub fn assert_exact_cardinality(&mut self, k: usize) -> Z4Result<()> {
        let sum = self.build_cardinality_sum()?;
        let k_term = self.solver.int_const(k as i64);
        let eq = self.solver.try_eq(sum, k_term)?;
        self.solver.try_assert_term(eq)?;
        Ok(())
    }

    /// Assert that at most `k` base elements are true.
    pub fn assert_max_cardinality(&mut self, k: usize) -> Z4Result<()> {
        let sum = self.build_cardinality_sum()?;
        let k_term = self.solver.int_const(k as i64);
        let le = self.solver.try_le(sum, k_term)?;
        self.solver.try_assert_term(le)?;
        Ok(())
    }

    /// Assert that at least `k` base elements are true.
    pub fn assert_min_cardinality(&mut self, k: usize) -> Z4Result<()> {
        let sum = self.build_cardinality_sum()?;
        let k_term = self.solver.int_const(k as i64);
        let ge = self.solver.try_ge(sum, k_term)?;
        self.solver.try_assert_term(ge)?;
        Ok(())
    }

    /// Set a timeout for each solver `check_sat` call.
    pub fn set_timeout(&mut self, timeout: Option<std::time::Duration>) {
        self.solver.set_timeout(timeout);
    }

    /// Enumerate all satisfying subsets using AllSAT with blocking clauses.
    ///
    /// Returns a [`NestedPowersetSolution`] containing all satisfying assignments.
    ///
    /// # Errors
    /// Returns an error if the solver fails, times out, or max solutions is exceeded.
    pub fn enumerate_all(
        &mut self,
        config: &NestedPowersetConfig,
    ) -> Z4Result<NestedPowersetSolution> {
        if let Some(timeout) = config.solve_timeout {
            self.solver.set_timeout(Some(timeout));
        }

        // Degenerate case: no base elements means exactly one solution (the empty set).
        if self.base_vars.is_empty() {
            return Ok(NestedPowersetSolution {
                solutions: vec![Vec::new()],
            });
        }

        let mut solutions = Vec::new();

        loop {
            if solutions.len() >= config.max_solutions {
                return Err(Z4Error::UnsupportedOp(format!(
                    "nested powerset enumeration exceeded {} solutions",
                    config.max_solutions
                )));
            }

            let result = self.solver.try_check_sat()?;
            match result.into_inner() {
                SolveResult::Sat => {
                    let model = self.solver.try_get_model().map_err(|e| {
                        Z4Error::UnsupportedOp(format!("model extraction failed: {e}"))
                    })?;
                    let model = model.into_inner();

                    // Extract which base elements are true
                    let mut selected = Vec::new();
                    for (i, elem) in self.base_elements.iter().enumerate() {
                        let var_name = format!("__npow_base_{i}");
                        let is_true = model.bool_val(&var_name).unwrap_or(false);
                        if is_true {
                            selected.push(elem.clone());
                        }
                    }

                    // Add blocking clause: NOT(current assignment)
                    self.add_blocking_clause(&model)?;

                    solutions.push(selected);
                }
                SolveResult::Unsat(_) => {
                    // No more solutions
                    break;
                }
                SolveResult::Unknown => {
                    return Err(Z4Error::SolverUnknown);
                }
                _ => {
                    return Err(Z4Error::SolverUnknown);
                }
            }
        }

        Ok(NestedPowersetSolution { solutions })
    }

    /// Build the integer sum of all base variables (for cardinality constraints).
    fn build_cardinality_sum(&mut self) -> Z4Result<Term> {
        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);

        if self.base_vars.is_empty() {
            return Ok(zero);
        }

        let mut sum = zero;
        for &var in &self.base_vars {
            let contribution = self.solver.try_ite(var, one, zero)?;
            sum = self.solver.try_add(sum, contribution)?;
        }
        Ok(sum)
    }

    /// Add a blocking clause to exclude the current model.
    ///
    /// Asserts: NOT(b0=v0 /\ b1=v1 /\ ... /\ bn=vn)
    /// which is equivalent to: (b0!=v0) \/ (b1!=v1) \/ ... \/ (bn!=vn)
    fn add_blocking_clause(&mut self, model: &Model) -> Z4Result<()> {
        // Build the disjunction of negated assignments
        let mut disjuncts: Vec<Term> = Vec::with_capacity(self.base_vars.len());

        for (i, &var) in self.base_vars.iter().enumerate() {
            let var_name = format!("__npow_base_{i}");
            let model_val = model.bool_val(&var_name).unwrap_or(false);

            // If model says true, we want NOT(var); if false, we want var
            let disjunct = if model_val {
                self.solver.try_not(var)?
            } else {
                var
            };
            disjuncts.push(disjunct);
        }

        if disjuncts.is_empty() {
            // No variables = no blocking clause needed (degenerate case)
            return Ok(());
        }

        // Build the disjunction
        let mut blocking = disjuncts[0];
        for &d in &disjuncts[1..] {
            blocking = self.solver.try_or(blocking, d)?;
        }

        self.solver.try_assert_term(blocking)?;
        Ok(())
    }

    /// Generate a fresh variable name.
    #[allow(dead_code)]
    fn fresh_name(&mut self, prefix: &str) -> String {
        let id = self.fresh_counter;
        self.fresh_counter += 1;
        format!("__npow_{prefix}_{id}")
    }

    /// Mutable access to the solver for adding custom constraints.
    pub fn solver_mut(&mut self) -> &mut Solver {
        &mut self.solver
    }
}

/// Compute all k-element subsets of a set of integers.
///
/// Given a sorted list of elements and a target size k, returns all C(n,k) subsets
/// in lexicographic order. Each subset is sorted.
///
/// Used to compute the base elements for `SUBSET(SUBSET S)` with a Cardinality=k filter.
///
/// # Example
/// ```text
/// k_subsets(&[1, 2, 3, 4, 5], 2)
///   => [{1,2}, {1,3}, {1,4}, {1,5}, {2,3}, {2,4}, {2,5}, {3,4}, {3,5}, {4,5}]
/// ```
#[must_use]
pub fn k_subsets(elements: &[i64], k: usize) -> Vec<BaseElement> {
    let n = elements.len();
    if k > n {
        return Vec::new();
    }
    if k == 0 {
        return vec![BaseElement {
            members: Vec::new(),
        }];
    }

    let mut result = Vec::new();
    let mut indices = (0..k).collect::<Vec<_>>();

    loop {
        // Emit current combination
        let members: Vec<i64> = indices.iter().map(|&i| elements[i]).collect();
        result.push(BaseElement { members });

        // Advance to next combination
        let mut i = k;
        loop {
            if i == 0 {
                return result;
            }
            i -= 1;
            indices[i] += 1;
            if indices[i] <= n - k + i {
                break;
            }
        }
        // Reset subsequent indices
        for j in (i + 1)..k {
            indices[j] = indices[j - 1] + 1;
        }
    }
}

/// Compute binomial coefficient C(n, k).
///
/// Returns 0 if k > n.
#[must_use]
pub fn binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    if k == 0 || k == n {
        return 1;
    }
    // Use the smaller of k and n-k
    let k = k.min(n - k);
    let mut result = 1usize;
    for i in 0..k {
        result = result.saturating_mul(n - i) / (i + 1);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // k_subsets tests
    // =========================================================================

    #[test]
    fn test_k_subsets_basic() {
        let result = k_subsets(&[1, 2, 3], 2);
        assert_eq!(result.len(), 3);
        assert_eq!(result[0].members, vec![1, 2]);
        assert_eq!(result[1].members, vec![1, 3]);
        assert_eq!(result[2].members, vec![2, 3]);
    }

    #[test]
    fn test_k_subsets_five_choose_two() {
        let result = k_subsets(&[1, 2, 3, 4, 5], 2);
        assert_eq!(result.len(), 10); // C(5,2) = 10
                                      // First and last
        assert_eq!(result[0].members, vec![1, 2]);
        assert_eq!(result[9].members, vec![4, 5]);
    }

    #[test]
    fn test_k_subsets_empty() {
        let result = k_subsets(&[1, 2, 3], 0);
        assert_eq!(result.len(), 1);
        assert!(result[0].members.is_empty());
    }

    #[test]
    fn test_k_subsets_full() {
        let result = k_subsets(&[1, 2, 3], 3);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].members, vec![1, 2, 3]);
    }

    #[test]
    fn test_k_subsets_k_too_large() {
        let result = k_subsets(&[1, 2], 3);
        assert!(result.is_empty());
    }

    // =========================================================================
    // binomial tests
    // =========================================================================

    #[test]
    fn test_binomial_basic() {
        assert_eq!(binomial(5, 2), 10);
        assert_eq!(binomial(5, 0), 1);
        assert_eq!(binomial(5, 5), 1);
        assert_eq!(binomial(4, 2), 6);
        assert_eq!(binomial(10, 3), 120);
    }

    #[test]
    fn test_binomial_k_too_large() {
        assert_eq!(binomial(3, 5), 0);
    }

    // =========================================================================
    // NestedPowersetEncoder tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_empty_base() {
        let mut enc = NestedPowersetEncoder::new(Vec::new()).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();
        // One solution: the empty set
        assert_eq!(result.solutions.len(), 1);
        assert!(result.solutions[0].is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_single_element() {
        let base = vec![BaseElement {
            members: vec![1, 2],
        }];
        let mut enc = NestedPowersetEncoder::new(base).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();
        // Two solutions: {} and {{1,2}}
        assert_eq!(result.solutions.len(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_three_elements_unconstrained() {
        // Three base elements -> 2^3 = 8 subsets
        let base = vec![
            BaseElement {
                members: vec![1, 2],
            },
            BaseElement {
                members: vec![1, 3],
            },
            BaseElement {
                members: vec![2, 3],
            },
        ];
        let mut enc = NestedPowersetEncoder::new(base).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();
        assert_eq!(result.solutions.len(), 8);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_with_cardinality_constraint() {
        // Three base elements, exactly 2 must be selected
        let base = vec![
            BaseElement {
                members: vec![1, 2],
            },
            BaseElement {
                members: vec![1, 3],
            },
            BaseElement {
                members: vec![2, 3],
            },
        ];
        let mut enc = NestedPowersetEncoder::new(base).unwrap();
        enc.assert_exact_cardinality(2).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();
        // C(3,2) = 3 subsets of size exactly 2
        assert_eq!(result.solutions.len(), 3);
        for sol in &result.solutions {
            assert_eq!(sol.len(), 2);
        }
    }

    #[cfg_attr(test, ntest::timeout(60000))]
    #[test]
    fn test_encoder_spantree_pattern() {
        // SpanTreeTest5Nodes: 5 nodes, edges are 2-element subsets
        // C(5,2) = 10 edges, SUBSET of those = 2^10 = 1024
        let nodes: Vec<i64> = (1..=5).collect();
        let edges = k_subsets(&nodes, 2);
        assert_eq!(edges.len(), 10);

        let mut enc = NestedPowersetEncoder::new(edges).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();
        assert_eq!(result.solutions.len(), 1024); // 2^10
    }

    #[cfg_attr(test, ntest::timeout(60000))]
    #[test]
    fn test_encoder_spantree_with_min_edges() {
        // SpanTreeTest5Nodes with at least 4 edges (connected graph needs >= 4)
        let nodes: Vec<i64> = (1..=5).collect();
        let edges = k_subsets(&nodes, 2);
        assert_eq!(edges.len(), 10);

        let mut enc = NestedPowersetEncoder::new(edges).unwrap();
        enc.assert_min_cardinality(4).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();

        // All solutions have >= 4 edges
        for sol in &result.solutions {
            assert!(sol.len() >= 4, "expected >= 4 edges, got {}", sol.len());
        }

        // Count: sum_{k=4}^{10} C(10,k)
        // = C(10,4) + C(10,5) + ... + C(10,10)
        // = 210 + 252 + 210 + 120 + 45 + 10 + 1 = 848
        let expected: usize = (4..=10).map(|k| binomial(10, k)).sum();
        assert_eq!(expected, 848);
        assert_eq!(result.solutions.len(), expected);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_four_nodes_pattern() {
        // SpanTreeTest4Nodes: 4 nodes, C(4,2) = 6 edges, 2^6 = 64
        let nodes: Vec<i64> = (1..=4).collect();
        let edges = k_subsets(&nodes, 2);
        assert_eq!(edges.len(), 6);

        let mut enc = NestedPowersetEncoder::new(edges).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();
        assert_eq!(result.solutions.len(), 64);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_max_cardinality() {
        // 4 elements, at most 1 selected
        let base = vec![
            BaseElement { members: vec![1] },
            BaseElement { members: vec![2] },
            BaseElement { members: vec![3] },
            BaseElement { members: vec![4] },
        ];
        let mut enc = NestedPowersetEncoder::new(base).unwrap();
        enc.assert_max_cardinality(1).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();
        // C(4,0) + C(4,1) = 1 + 4 = 5
        assert_eq!(result.solutions.len(), 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_too_large_base() {
        let base: Vec<BaseElement> = (0..=MAX_NESTED_POWERSET_BASE as i64)
            .map(|i| BaseElement { members: vec![i] })
            .collect();
        let result = NestedPowersetEncoder::new(base);
        assert!(result.is_err());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_custom_constraint() {
        // 3 elements, assert: if element 0 is in, then element 1 must be in
        // (edge {1,2} => edge {1,3})
        let base = vec![
            BaseElement {
                members: vec![1, 2],
            },
            BaseElement {
                members: vec![1, 3],
            },
            BaseElement {
                members: vec![2, 3],
            },
        ];
        let mut enc = NestedPowersetEncoder::new(base).unwrap();

        // Assert: base_0 => base_1
        let b0 = enc.base_var(0).unwrap();
        let b1 = enc.base_var(1).unwrap();
        let implication = enc.solver_mut().try_implies(b0, b1).unwrap();
        enc.assert_constraint(implication);

        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();

        // Without constraint: 8 solutions
        // With b0 => b1: removes solutions where b0=T, b1=F
        // That removes: {b0=T, b1=F, b2=F} and {b0=T, b1=F, b2=T} = 2 solutions
        // Remaining: 8 - 2 = 6
        assert_eq!(result.solutions.len(), 6);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_encoder_solutions_are_unique() {
        let base = vec![
            BaseElement {
                members: vec![1, 2],
            },
            BaseElement {
                members: vec![3, 4],
            },
        ];
        let mut enc = NestedPowersetEncoder::new(base).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();

        // Check uniqueness by converting to sorted strings
        let mut seen = std::collections::HashSet::new();
        for sol in &result.solutions {
            let mut key: Vec<Vec<i64>> = sol.iter().map(|e| e.members.clone()).collect();
            key.sort();
            assert!(
                seen.insert(format!("{key:?}")),
                "duplicate solution: {key:?}"
            );
        }
    }

    // =========================================================================
    // Integration scenario: SpanTreeTest5Nodes Init encoding
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_spantree5_init_enumeration() {
        // Full SpanTreeTest5Nodes Init enumeration:
        // - 5 nodes, C(5,2) = 10 edges
        // - Edges \in SUBSET({2-element subsets of Nodes}) = 2^10 = 1024
        // - mom = [n \in Nodes |-> n] -- deterministic, 1 value
        // - dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality] -- deterministic, 1 value
        //
        // So the total Init states = 1024 (one per Edges configuration).

        let nodes: Vec<i64> = (1..=5).collect();
        let edges = k_subsets(&nodes, 2);
        assert_eq!(edges.len(), 10);

        let mut enc = NestedPowersetEncoder::new(edges).unwrap();
        let config = NestedPowersetConfig::default();
        let result = enc.enumerate_all(&config).unwrap();

        assert_eq!(
            result.solutions.len(),
            1024,
            "SpanTreeTest5Nodes should have exactly 1024 Init states for Edges"
        );

        // Verify some boundary cases
        let has_empty = result.solutions.iter().any(|s| s.is_empty());
        assert!(has_empty, "should include the empty graph (no edges)");

        let has_full = result.solutions.iter().any(|s| s.len() == 10);
        assert!(has_full, "should include the complete graph (all 10 edges)");

        // Verify that all solutions contain only 2-element subsets
        for sol in &result.solutions {
            for edge in sol {
                assert_eq!(edge.members.len(), 2, "all edges must be 2-element subsets");
            }
        }
    }
}
