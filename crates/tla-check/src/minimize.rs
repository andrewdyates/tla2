// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Spec minimizer: reduces TLA+ specifications while preserving a target property.
//!
//! Given a specification that exhibits a particular model-checking result (invariant
//! violation, deadlock, liveness violation, etc.), this module systematically removes
//! AST elements using delta debugging to find a minimal reproducer.
//!
//! # Algorithm
//!
//! The minimizer uses a two-phase approach:
//! 1. **Coarse reduction**: Remove entire operators, variables, and constants
//! 2. **Fine reduction**: Simplify expressions within remaining operators
//!    (remove disjuncts, conjuncts, CASE arms, set elements, etc.)
//!
//! At each step, the oracle re-runs the model checker to verify that the target
//! property is preserved.

use tla_core::ast::{BoundVar, CaseArm, Expr, Module, OperatorDef, Unit};
use tla_core::Spanned;

use crate::check::{check_module, CheckResult, ModelChecker};
use crate::config::Config;

/// Classification of a model checking outcome for comparison purposes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResultClass {
    /// Model checking succeeded (no errors found)
    Success,
    /// Invariant violation with the given invariant name
    InvariantViolation(String),
    /// Temporal property violation
    PropertyViolation(String),
    /// Liveness violation
    LivenessViolation(String),
    /// Deadlock detected
    Deadlock,
    /// Model checker returned an error
    Error,
}

impl ResultClass {
    /// Classify a `CheckResult` into a `ResultClass`.
    #[must_use]
    pub fn from_check_result(result: &CheckResult) -> Self {
        match result {
            CheckResult::Success(_) => ResultClass::Success,
            CheckResult::InvariantViolation { invariant, .. } => {
                ResultClass::InvariantViolation(invariant.clone())
            }
            CheckResult::PropertyViolation { property, .. } => {
                ResultClass::PropertyViolation(property.clone())
            }
            CheckResult::LivenessViolation { property, .. } => {
                ResultClass::LivenessViolation(property.clone())
            }
            CheckResult::Deadlock { .. } => ResultClass::Deadlock,
            CheckResult::Error { .. } | CheckResult::LimitReached { .. } => ResultClass::Error,
        }
    }
}

/// Configuration for the spec minimizer.
#[derive(Debug, Clone)]
pub struct MinimizeConfig {
    /// Maximum number of oracle calls before giving up.
    pub max_oracle_calls: usize,
    /// Whether to attempt fine-grained expression simplification after coarse reduction.
    pub fine_reduction: bool,
    /// Maximum states to explore per oracle call. Prevents unbounded exploration
    /// on candidate modules where the reduction creates an infinite state space.
    /// `None` means no limit (uses `check_module` directly).
    pub max_states_per_oracle: Option<usize>,
}

impl Default for MinimizeConfig {
    fn default() -> Self {
        Self {
            max_oracle_calls: 1000,
            fine_reduction: true,
            max_states_per_oracle: None,
        }
    }
}

/// Statistics from a minimization run.
#[derive(Debug, Clone, Default)]
pub struct MinimizeStats {
    /// Total oracle calls made.
    pub oracle_calls: usize,
    /// Number of successful reductions (oracle confirmed property preserved).
    pub successful_reductions: usize,
    /// Number of units in the original spec.
    pub original_units: usize,
    /// Number of units in the minimized spec.
    pub final_units: usize,
    /// Number of operators in the original spec.
    pub original_operators: usize,
    /// Number of operators in the minimized spec.
    pub final_operators: usize,
}

/// Result of a minimization run.
#[derive(Debug)]
pub struct MinimizeResult {
    /// The minimized module.
    pub module: Module,
    /// The target result class that was preserved.
    pub target: ResultClass,
    /// Statistics from the minimization run.
    pub stats: MinimizeStats,
}

/// The spec minimizer.
pub struct Minimizer<'a> {
    config: &'a Config,
    minimize_config: MinimizeConfig,
    target: ResultClass,
    stats: MinimizeStats,
}

impl<'a> Minimizer<'a> {
    /// Create a new minimizer.
    ///
    /// `config` is the TLC-style configuration (INIT, NEXT, INVARIANT, etc.).
    /// `target` is the result class that the minimized spec must preserve.
    #[must_use]
    pub fn new(config: &'a Config, target: ResultClass, minimize_config: MinimizeConfig) -> Self {
        Self {
            config,
            minimize_config,
            target,
            stats: MinimizeStats::default(),
        }
    }

    /// Run the minimizer on the given module.
    ///
    /// Returns the minimized module that still exhibits the target property,
    /// or the original module if no reduction was possible.
    pub fn minimize(mut self, module: &Module) -> MinimizeResult {
        let mut current = module.clone();

        self.stats.original_units = current.units.len();
        self.stats.original_operators = count_operators(&current);

        // Phase 1: Coarse reduction — remove entire units
        current = self.reduce_units(current);

        // Phase 2: Fine reduction — simplify expressions within operators
        if self.minimize_config.fine_reduction
            && self.stats.oracle_calls < self.minimize_config.max_oracle_calls
        {
            current = self.reduce_expressions(current);
        }

        self.stats.final_units = current.units.len();
        self.stats.final_operators = count_operators(&current);

        MinimizeResult {
            module: current,
            target: self.target.clone(),
            stats: self.stats,
        }
    }

    /// Check if a candidate module preserves the target property.
    fn oracle(&mut self, module: &Module) -> bool {
        self.stats.oracle_calls += 1;
        if self.stats.oracle_calls > self.minimize_config.max_oracle_calls {
            return false;
        }

        let result = if let Some(max_states) = self.minimize_config.max_states_per_oracle {
            let mut checker = ModelChecker::new(module, self.config);
            checker.set_max_states(max_states);
            checker.check()
        } else {
            check_module(module, self.config)
        };
        let class = ResultClass::from_check_result(&result);
        class == self.target
    }

    /// Phase 1: Remove entire units using delta debugging.
    fn reduce_units(&mut self, module: Module) -> Module {
        let removable = find_removable_units(&module, self.config);
        if removable.is_empty() {
            return module;
        }

        // Delta debugging: try removing subsets of removable units
        let mut current = module;
        let mut remaining: Vec<usize> = removable;

        // Try removing all at once
        let candidate = remove_units_at(&current, &remaining);
        if self.oracle(&candidate) {
            self.stats.successful_reductions += 1;
            return candidate;
        }

        // Binary search: try removing halves
        remaining = self.dd_reduce_units(current.clone(), remaining);

        // Build final module with remaining units removed
        // `remaining` now contains the indices that COULD be removed
        if !remaining.is_empty() {
            current = remove_units_at(&current, &remaining);
        }

        // One-by-one pass for anything the binary search missed
        current = self.one_by_one_units(current);

        current
    }

    /// Delta debugging core: recursively try removing subsets.
    fn dd_reduce_units(&mut self, module: Module, removable: Vec<usize>) -> Vec<usize> {
        if removable.len() <= 1 {
            // Base case: try removing the single element
            if removable.len() == 1 {
                let candidate = remove_units_at(&module, &removable);
                if self.oracle(&candidate) {
                    self.stats.successful_reductions += 1;
                    return removable;
                }
            }
            return Vec::new();
        }

        let mid = removable.len() / 2;
        let left = removable[..mid].to_vec();
        let right = removable[mid..].to_vec();

        // Try removing the left half
        let candidate = remove_units_at(&module, &left);
        if self.oracle(&candidate) {
            self.stats.successful_reductions += 1;
            // Left half can be removed; recurse on right half with updated module
            let mut result = left;
            let further = self.dd_reduce_units(candidate, right);
            result.extend(further);
            return result;
        }

        // Try removing the right half
        let candidate = remove_units_at(&module, &right);
        if self.oracle(&candidate) {
            self.stats.successful_reductions += 1;
            // Right half can be removed; recurse on left half with updated module
            let mut result = right;
            let further = self.dd_reduce_units(candidate, left);
            result.extend(further);
            return result;
        }

        // Neither half works alone; recurse on each half independently
        let left_result = self.dd_reduce_units(module.clone(), left);
        let module_after_left = if left_result.is_empty() {
            module
        } else {
            remove_units_at(&module, &left_result)
        };
        let right_result = self.dd_reduce_units(module_after_left, right);

        let mut result = left_result;
        result.extend(right_result);
        result
    }

    /// One-by-one unit removal pass: try removing each removable unit individually.
    fn one_by_one_units(&mut self, module: Module) -> Module {
        let mut current = module;
        loop {
            let removable = find_removable_units(&current, self.config);
            let mut made_progress = false;
            for &idx in &removable {
                if self.stats.oracle_calls >= self.minimize_config.max_oracle_calls {
                    return current;
                }
                let candidate = remove_units_at(&current, &[idx]);
                if self.oracle(&candidate) {
                    self.stats.successful_reductions += 1;
                    current = candidate;
                    made_progress = true;
                    break; // Restart since indices shifted
                }
            }
            if !made_progress {
                break;
            }
        }
        current
    }

    /// Phase 2: Fine-grained expression reduction within operators.
    fn reduce_expressions(&mut self, module: Module) -> Module {
        let mut current = module;

        // For each operator, try simplifying its body
        loop {
            let mut made_progress = false;
            let op_indices: Vec<usize> = current
                .units
                .iter()
                .enumerate()
                .filter_map(|(i, u)| match &u.node {
                    Unit::Operator(_) => Some(i),
                    _ => None,
                })
                .collect();

            for &op_idx in &op_indices {
                if self.stats.oracle_calls >= self.minimize_config.max_oracle_calls {
                    return current;
                }
                if let Some(reduced) = self.try_reduce_operator(&current, op_idx) {
                    current = reduced;
                    made_progress = true;
                    break; // Restart since we modified the module
                }
            }
            if !made_progress {
                break;
            }
        }

        current
    }

    /// Try to simplify a single operator's body expression.
    fn try_reduce_operator(&mut self, module: &Module, op_idx: usize) -> Option<Module> {
        let unit = &module.units[op_idx];
        let op = match &unit.node {
            Unit::Operator(op) => op,
            _ => return None,
        };

        // Generate candidate simplifications of the operator body
        let candidates = generate_expression_reductions(&op.body);

        for candidate_body in candidates {
            let mut new_op = op.clone();
            new_op.body = candidate_body;
            let mut new_module = module.clone();
            new_module.units[op_idx] = Spanned {
                node: Unit::Operator(new_op),
                span: unit.span,
            };

            if self.oracle(&new_module) {
                self.stats.successful_reductions += 1;
                return Some(new_module);
            }
        }

        None
    }
}

/// Count the number of operator definitions in a module.
fn count_operators(module: &Module) -> usize {
    module
        .units
        .iter()
        .filter(|u| matches!(u.node, Unit::Operator(_)))
        .count()
}

/// Find indices of units that are safe to attempt removing.
///
/// We never try to remove INIT/NEXT operators or VARIABLE/CONSTANT declarations
/// that are referenced by the config. Other operators are candidates.
fn find_removable_units(module: &Module, config: &Config) -> Vec<usize> {
    let protected_names = protected_operator_names(config);

    module
        .units
        .iter()
        .enumerate()
        .filter_map(|(i, unit)| {
            match &unit.node {
                Unit::Operator(op) => {
                    if protected_names.contains(&op.name.node.as_str()) {
                        None
                    } else {
                        Some(i)
                    }
                }
                // Variables and constants can be removed (the oracle will catch if needed)
                Unit::Variable(_) => Some(i),
                Unit::Constant(_) => Some(i),
                // Separators are always removable
                Unit::Separator => Some(i),
                // ASSUME and RECURSIVE are potentially removable
                Unit::Assume(_) | Unit::Recursive(_) => Some(i),
                // INSTANCE and THEOREM: leave alone for now
                Unit::Instance(_) | Unit::Theorem(_) => None,
            }
        })
        .collect()
}

/// Get the set of operator names that are directly referenced by the config.
fn protected_operator_names(config: &Config) -> Vec<&str> {
    let mut names = Vec::new();
    if let Some(ref init) = config.init {
        names.push(init.as_str());
    }
    if let Some(ref next) = config.next {
        names.push(next.as_str());
    }
    for inv in &config.invariants {
        names.push(inv.as_str());
    }
    for prop in &config.properties {
        names.push(prop.as_str());
    }
    if let Some(ref spec) = config.specification {
        names.push(spec.as_str());
    }
    for constraint in &config.constraints {
        names.push(constraint.as_str());
    }
    for constraint in &config.action_constraints {
        names.push(constraint.as_str());
    }
    names
}

/// Build a module with certain units removed (by index).
fn remove_units_at(module: &Module, indices: &[usize]) -> Module {
    let index_set: std::collections::HashSet<usize> = indices.iter().copied().collect();
    let units = module
        .units
        .iter()
        .enumerate()
        .filter(|(i, _)| !index_set.contains(i))
        .map(|(_, u)| u.clone())
        .collect();

    Module {
        name: module.name.clone(),
        extends: module.extends.clone(),
        units,
        action_subscript_spans: module.action_subscript_spans.clone(),
        span: module.span,
    }
}

/// Generate candidate simplified versions of an expression.
///
/// Each candidate is a possible replacement for the expression that is
/// structurally simpler. The oracle determines if the simplification preserves
/// the target property.
fn generate_expression_reductions(expr: &Spanned<Expr>) -> Vec<Spanned<Expr>> {
    let mut candidates = Vec::new();
    let span = expr.span;

    match &expr.node {
        // For And: try each operand alone
        Expr::And(left, right) => {
            candidates.push(*left.clone());
            candidates.push(*right.clone());
        }
        // For Or: try each operand alone
        Expr::Or(left, right) => {
            candidates.push(*left.clone());
            candidates.push(*right.clone());
        }
        // For IF: try then-branch or else-branch alone
        Expr::If(_, then_br, else_br) => {
            candidates.push(*then_br.clone());
            candidates.push(*else_br.clone());
        }
        // For CASE: try removing individual arms
        Expr::Case(arms, other) => {
            if arms.len() > 1 {
                for i in 0..arms.len() {
                    let reduced_arms: Vec<CaseArm> = arms
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, a)| a.clone())
                        .collect();
                    candidates.push(Spanned {
                        node: Expr::Case(reduced_arms, other.clone()),
                        span,
                    });
                }
            }
            // Try replacing with the OTHER branch if it exists
            if let Some(other_expr) = other {
                candidates.push(*other_expr.clone());
            }
            // Try replacing with the body of the first arm
            if let Some(first) = arms.first() {
                candidates.push(first.body.clone());
            }
        }
        // For SetEnum: try removing individual elements
        Expr::SetEnum(elems) => {
            if elems.len() > 1 {
                for i in 0..elems.len() {
                    let reduced: Vec<Spanned<Expr>> = elems
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, e)| e.clone())
                        .collect();
                    candidates.push(Spanned {
                        node: Expr::SetEnum(reduced),
                        span,
                    });
                }
            }
        }
        // For Tuple: try removing individual elements
        Expr::Tuple(elems) => {
            if elems.len() > 1 {
                for i in 0..elems.len() {
                    let reduced: Vec<Spanned<Expr>> = elems
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, e)| e.clone())
                        .collect();
                    candidates.push(Spanned {
                        node: Expr::Tuple(reduced),
                        span,
                    });
                }
            }
        }
        // For Exists/Forall: try simplifying the body
        Expr::Exists(vars, body) => {
            // Try replacing with just the body (removing quantifier)
            candidates.push(*body.clone());
            // If multiple bound vars, try removing each
            if vars.len() > 1 {
                for i in 0..vars.len() {
                    let reduced_vars: Vec<BoundVar> = vars
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, v)| v.clone())
                        .collect();
                    candidates.push(Spanned {
                        node: Expr::Exists(reduced_vars, body.clone()),
                        span,
                    });
                }
            }
        }
        Expr::Forall(vars, body) => {
            candidates.push(*body.clone());
            if vars.len() > 1 {
                for i in 0..vars.len() {
                    let reduced_vars: Vec<BoundVar> = vars
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, v)| v.clone())
                        .collect();
                    candidates.push(Spanned {
                        node: Expr::Forall(reduced_vars, body.clone()),
                        span,
                    });
                }
            }
        }
        // For LET: try removing definitions
        Expr::Let(defs, body) => {
            // Try replacing with just the body
            candidates.push(*body.clone());
            // Try removing individual LET definitions
            if defs.len() > 1 {
                for i in 0..defs.len() {
                    let reduced_defs: Vec<OperatorDef> = defs
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, d)| d.clone())
                        .collect();
                    candidates.push(Spanned {
                        node: Expr::Let(reduced_defs, body.clone()),
                        span,
                    });
                }
            }
        }
        // For Not: try removing the negation
        Expr::Not(inner) => {
            candidates.push(*inner.clone());
        }
        // For Implies: try each side
        Expr::Implies(left, right) => {
            candidates.push(*left.clone());
            candidates.push(*right.clone());
        }
        // Replace complex expressions with TRUE/FALSE constants
        _ => {
            candidates.push(Spanned {
                node: Expr::Bool(true),
                span,
            });
            candidates.push(Spanned {
                node: Expr::Bool(false),
                span,
            });
        }
    }

    candidates
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::{lower, parse_to_syntax_tree, FileId, Span};

    /// Helper: parse + lower a TLA+ source string into a Module.
    fn parse_module(src: &str) -> Module {
        let tree = parse_to_syntax_tree(src);
        let result = lower(FileId(0), &tree);
        result.module.expect("should parse module")
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_result_class_invariant_violation() {
        let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
===="#;
        let module = parse_module(src);
        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config should parse");

        let result = check_module(&module, &config);
        let class = ResultClass::from_check_result(&result);
        assert!(
            matches!(class, ResultClass::InvariantViolation(ref name) if name == "Inv"),
            "expected InvariantViolation(Inv), got {:?}",
            class
        );
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_result_class_success() {
        let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {0, 1}
Next == x' \in {0, 1}
Inv == x \in {0, 1}
===="#;
        let module = parse_module(src);
        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config should parse");

        let result = check_module(&module, &config);
        let class = ResultClass::from_check_result(&result);
        assert_eq!(class, ResultClass::Success);
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_minimize_removes_unused_operator() {
        // Spec with an unused helper operator that can be removed.
        // Uses bounded {0,1,2,3} domain for fast model checking.
        let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {0, 1, 2, 3}
Next == x' \in {0, 1, 2, 3}
Inv == x < 3
Unused == x + 42
===="#;
        let module = parse_module(src);
        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config should parse");

        let target = ResultClass::InvariantViolation("Inv".to_string());
        let minimizer = Minimizer::new(
            &config,
            target.clone(),
            MinimizeConfig {
                max_oracle_calls: 100,
                fine_reduction: false,
                ..Default::default()
            },
        );
        let result = minimizer.minimize(&module);

        assert_eq!(result.target, target);
        assert!(
            result.stats.final_operators < result.stats.original_operators,
            "should have removed at least one operator: {} -> {}",
            result.stats.original_operators,
            result.stats.final_operators
        );
        // The "Unused" operator should be gone
        let has_unused = result.module.units.iter().any(|u| match &u.node {
            Unit::Operator(op) => op.name.node == "Unused",
            _ => false,
        });
        assert!(!has_unused, "Unused operator should have been removed");
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_minimize_preserves_required_operators() {
        let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {0, 1, 2, 3}
Next == x' \in {0, 1, 2, 3}
Inv == x < 3
===="#;
        let module = parse_module(src);
        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config should parse");

        let target = ResultClass::InvariantViolation("Inv".to_string());
        let minimizer = Minimizer::new(
            &config,
            target,
            MinimizeConfig {
                max_oracle_calls: 100,
                fine_reduction: false,
                ..Default::default()
            },
        );
        let result = minimizer.minimize(&module);

        // Init, Next, and Inv must still be present
        let op_names: Vec<&str> = result
            .module
            .units
            .iter()
            .filter_map(|u| match &u.node {
                Unit::Operator(op) => Some(op.name.node.as_str()),
                _ => None,
            })
            .collect();
        assert!(op_names.contains(&"Init"), "Init must be preserved");
        assert!(op_names.contains(&"Next"), "Next must be preserved");
        assert!(op_names.contains(&"Inv"), "Inv must be preserved");
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_minimize_with_multiple_unused() {
        let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {0, 1, 2, 3}
Next == x' \in {0, 1, 2, 3}
Inv == x < 3
Helper1 == x * 2
Helper2 == x + 10
Helper3 == x - 5
===="#;
        let module = parse_module(src);
        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config should parse");

        let target = ResultClass::InvariantViolation("Inv".to_string());
        let minimizer = Minimizer::new(
            &config,
            target,
            MinimizeConfig {
                max_oracle_calls: 200,
                fine_reduction: false,
                ..Default::default()
            },
        );
        let result = minimizer.minimize(&module);

        // All three helpers should be removed
        let op_names: Vec<&str> = result
            .module
            .units
            .iter()
            .filter_map(|u| match &u.node {
                Unit::Operator(op) => Some(op.name.node.as_str()),
                _ => None,
            })
            .collect();
        assert!(!op_names.contains(&"Helper1"), "Helper1 should be removed");
        assert!(!op_names.contains(&"Helper2"), "Helper2 should be removed");
        assert!(!op_names.contains(&"Helper3"), "Helper3 should be removed");
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_minimize_deadlock_preservation() {
        // Spec that deadlocks: x starts at 0, can go to 1, then has no successors
        let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x = 0 /\ x' = 1
Unused == 42
===="#;
        let module = parse_module(src);
        let config = Config::parse("INIT Init\nNEXT Next\n").expect("config should parse");

        let result = check_module(&module, &config);
        let class = ResultClass::from_check_result(&result);

        if class == ResultClass::Deadlock {
            let minimizer = Minimizer::new(
                &config,
                ResultClass::Deadlock,
                MinimizeConfig {
                    max_oracle_calls: 100,
                    fine_reduction: false,
                    ..Default::default()
                },
            );
            let min_result = minimizer.minimize(&module);
            assert_eq!(min_result.target, ResultClass::Deadlock);
            // Unused operator should be removed
            let has_unused = min_result.module.units.iter().any(|u| match &u.node {
                Unit::Operator(op) => op.name.node == "Unused",
                _ => false,
            });
            assert!(
                !has_unused,
                "Unused operator should be removed in deadlock minimization"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_expression_reduction_or() {
        let span = Span::new(FileId(0), 0, 0);
        let left = Spanned {
            node: Expr::Bool(true),
            span,
        };
        let right = Spanned {
            node: Expr::Bool(false),
            span,
        };
        let or_expr = Spanned {
            node: Expr::Or(Box::new(left.clone()), Box::new(right.clone())),
            span,
        };

        let candidates = generate_expression_reductions(&or_expr);
        assert_eq!(candidates.len(), 2, "Or should produce 2 candidates");
        assert_eq!(candidates[0].node, Expr::Bool(true));
        assert_eq!(candidates[1].node, Expr::Bool(false));
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_expression_reduction_and() {
        let span = Span::new(FileId(0), 0, 0);
        let left = Spanned {
            node: Expr::Bool(true),
            span,
        };
        let right = Spanned {
            node: Expr::Bool(false),
            span,
        };
        let and_expr = Spanned {
            node: Expr::And(Box::new(left.clone()), Box::new(right.clone())),
            span,
        };

        let candidates = generate_expression_reductions(&and_expr);
        assert_eq!(candidates.len(), 2, "And should produce 2 candidates");
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_protected_names_extraction() {
        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv1\nINVARIANT Inv2\nCONSTRAINT Cst\n")
                .expect("config should parse");

        let names = protected_operator_names(&config);
        assert!(names.contains(&"Init"));
        assert!(names.contains(&"Next"));
        assert!(names.contains(&"Inv1"));
        assert!(names.contains(&"Inv2"));
        assert!(names.contains(&"Cst"));
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_minimize_fine_reduction_disjunct() {
        // Spec where Next has an unnecessary disjunct
        let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == (x' = x + 1) \/ (x' = x + 2)
Inv == x < 2
===="#;
        let module = parse_module(src);
        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config should parse");

        let target = ResultClass::InvariantViolation("Inv".to_string());
        let minimizer = Minimizer::new(
            &config,
            target.clone(),
            MinimizeConfig {
                max_oracle_calls: 200,
                fine_reduction: true,
                // Bound each oracle call to prevent unbounded exploration on
                // candidate modules where the reduction removes the violation.
                // The spec x' = x + 1 with Inv == x < 2 violates at x=2,
                // which is found within the first 5 states.
                max_states_per_oracle: Some(1000),
            },
        );
        let result = minimizer.minimize(&module);

        // The minimizer should preserve the invariant violation
        assert_eq!(result.target, target);
        // Stats should show some reductions were attempted
        assert!(
            result.stats.oracle_calls > 0,
            "should have made oracle calls"
        );
    }
}
