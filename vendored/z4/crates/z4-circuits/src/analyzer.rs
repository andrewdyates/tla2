// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Circuit analysis tools.
//!
//! Provides methods for analyzing Boolean circuits:
//! - Size (number of gates)
//! - Depth (longest path from input to output)
//! - Circuit class membership (AC0, TC0, etc.)
//! - Functional equivalence checking

use crate::{Circuit, Gate, TruthTable};

/// Circuit complexity classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitClass {
    /// AC0: Constant depth, unbounded fan-in AND/OR, polynomial size.
    /// Cannot compute PARITY.
    AC0,
    /// ACC0: AC0 with MOD gates.
    /// Cannot compute MAJORITY (for MOD_p with prime p).
    ACC0,
    /// TC0: AC0 with threshold gates.
    /// Can compute anything in NC1 (and more).
    TC0,
    /// NC1: Logarithmic depth, bounded fan-in (2), polynomial size.
    /// Equivalent to formulas (trees rather than DAGs).
    NC1,
    /// P/poly: Polynomial size (no depth restriction).
    /// The class of all polynomial-size circuits.
    PPoly,
}

impl CircuitClass {
    /// Returns true if this class is contained in the other class.
    pub fn contained_in(&self, other: &Self) -> bool {
        use CircuitClass::{PPoly, AC0, ACC0, NC1, TC0};
        match (self, other) {
            // Same class
            (a, b) if a == b => true,
            // Everything is in P/poly
            // AC0 ⊆ ACC0 ⊆ TC0
            // NC1 ⊆ TC0 (technically NC1 ⊆ TC0 ⊆ NC2)
            (_, PPoly) | (AC0, ACC0 | TC0) | (ACC0 | NC1, TC0) => true,
            _ => false,
        }
    }
}

/// Circuit analyzer providing various analysis methods.
pub struct CircuitAnalyzer;

impl CircuitAnalyzer {
    /// Compute the size of the circuit (number of non-input gates).
    pub fn size(circuit: &Circuit) -> usize {
        circuit
            .gates()
            .iter()
            .filter(|g| !g.is_input() && !g.is_constant())
            .count()
    }

    /// Compute the depth of the circuit (longest path from any input to any output).
    ///
    /// Depth is the maximum number of gates on any path from an input to an output.
    pub fn depth(circuit: &Circuit) -> usize {
        if circuit.outputs().is_empty() {
            return 0;
        }

        // Compute depth for each gate via dynamic programming
        let mut depths = vec![0usize; circuit.num_gates()];

        for (i, gate) in circuit.gates().iter().enumerate() {
            depths[i] = match gate {
                Gate::Input(_) | Gate::True | Gate::False => 0,
                _ => {
                    let max_input_depth =
                        gate.inputs().iter().map(|g| depths[g.0]).max().unwrap_or(0);
                    max_input_depth + 1
                }
            };
        }

        // Return max depth among outputs
        circuit
            .outputs()
            .iter()
            .map(|g| depths[g.0])
            .max()
            .unwrap_or(0)
    }

    /// Compute the maximum fan-in of any gate in the circuit.
    pub fn max_fan_in(circuit: &Circuit) -> usize {
        circuit.gates().iter().map(Gate::fan_in).max().unwrap_or(0)
    }

    /// Check if the circuit is in a given complexity class.
    ///
    /// This is a conservative check based on structural properties:
    /// - AC0: Constant depth, only AND/OR/NOT gates (unbounded fan-in OK)
    /// - ACC0: AC0 + MOD gates
    /// - TC0: ACC0 + threshold gates
    /// - NC1: Bounded fan-in (≤2), logarithmic depth
    /// - P/poly: Polynomial size (always true for explicit circuits)
    pub fn is_in_class(circuit: &Circuit, class: CircuitClass) -> bool {
        match class {
            CircuitClass::PPoly => {
                // All explicit circuits are in P/poly
                true
            }
            CircuitClass::NC1 => {
                // NC1: bounded fan-in (≤2), depth O(log n)
                let max_fan_in = Self::max_fan_in(circuit);
                if max_fan_in > 2 {
                    return false;
                }
                // Check no threshold or mod gates
                for gate in circuit.gates() {
                    match gate {
                        Gate::Threshold { .. }
                        | Gate::Mod { .. }
                        | Gate::NaryAnd(_)
                        | Gate::NaryOr(_) => return false,
                        _ => {}
                    }
                }
                // Check depth is O(log n) - we check depth <= 2 * log2(num_inputs)
                let n = circuit.num_inputs();
                if n == 0 {
                    return true;
                }
                let log_n = (n as f64).log2().ceil() as usize;
                let max_depth = 2 * log_n.max(1);
                Self::depth(circuit) <= max_depth
            }
            CircuitClass::TC0 => {
                // TC0: constant depth, allows threshold gates
                Self::is_constant_depth(circuit) && !Self::uses_mod_gates(circuit)
            }
            CircuitClass::ACC0 => {
                // ACC0: constant depth, allows mod gates but not threshold
                Self::is_constant_depth(circuit) && !Self::uses_threshold_gates(circuit)
            }
            CircuitClass::AC0 => {
                // AC0: constant depth, only AND/OR/NOT/XOR
                Self::is_constant_depth(circuit)
                    && !Self::uses_threshold_gates(circuit)
                    && !Self::uses_mod_gates(circuit)
            }
        }
    }

    /// Check if circuit has constant depth (depth doesn't grow with input size).
    ///
    /// We use a heuristic: depth <= 10 is considered "constant" for practical purposes.
    fn is_constant_depth(circuit: &Circuit) -> bool {
        const MAX_CONSTANT_DEPTH: usize = 10;
        Self::depth(circuit) <= MAX_CONSTANT_DEPTH
    }

    /// Check if circuit uses threshold gates.
    fn uses_threshold_gates(circuit: &Circuit) -> bool {
        circuit
            .gates()
            .iter()
            .any(|g| matches!(g, Gate::Threshold { .. }))
    }

    /// Check if circuit uses mod gates.
    fn uses_mod_gates(circuit: &Circuit) -> bool {
        circuit
            .gates()
            .iter()
            .any(|g| matches!(g, Gate::Mod { .. }))
    }

    /// Check if the circuit computes the given function (truth table).
    ///
    /// This evaluates the circuit on all 2^n inputs and compares to the truth table.
    /// Only practical for small n (n <= 20 or so).
    pub fn computes(circuit: &Circuit, function: &TruthTable) -> bool {
        assert_eq!(
            circuit.num_inputs(),
            function.num_inputs(),
            "Circuit and function must have same number of inputs"
        );
        assert_eq!(
            circuit.outputs().len(),
            1,
            "Circuit must have exactly one output"
        );

        let n = circuit.num_inputs();
        for i in 0..(1 << n) {
            let input: Vec<bool> = (0..n).map(|j| (i >> j) & 1 == 1).collect();
            let circuit_output = circuit.evaluate_single(&input);
            let function_output = function.evaluate(&input);
            if circuit_output != function_output {
                return false;
            }
        }
        true
    }

    /// Compute the truth table of a single-output circuit.
    pub fn truth_table(circuit: &Circuit) -> TruthTable {
        assert_eq!(
            circuit.outputs().len(),
            1,
            "Circuit must have exactly one output"
        );
        TruthTable::from_fn(circuit.num_inputs(), |inputs| {
            circuit.evaluate_single(inputs)
        })
    }

    /// Check if two circuits compute the same function.
    pub fn equivalent(c1: &Circuit, c2: &Circuit) -> bool {
        assert_eq!(
            c1.num_inputs(),
            c2.num_inputs(),
            "Circuits must have same number of inputs"
        );
        assert_eq!(
            c1.outputs().len(),
            c2.outputs().len(),
            "Circuits must have same number of outputs"
        );

        let n = c1.num_inputs();
        for i in 0..(1 << n) {
            let input: Vec<bool> = (0..n).map(|j| (i >> j) & 1 == 1).collect();
            let out1 = c1.evaluate(&input);
            let out2 = c2.evaluate(&input);
            if out1 != out2 {
                return false;
            }
        }
        true
    }

    /// Count the number of gates of each type.
    pub fn gate_counts(circuit: &Circuit) -> GateCounts {
        let mut counts = GateCounts::default();
        for gate in circuit.gates() {
            match gate {
                Gate::Input(_) => counts.inputs += 1,
                Gate::True | Gate::False => counts.constants += 1,
                Gate::Not(_) => counts.not += 1,
                Gate::And(_, _) => counts.and2 += 1,
                Gate::Or(_, _) => counts.or2 += 1,
                Gate::Xor(_, _) => counts.xor2 += 1,
                Gate::NaryAnd(_) => counts.nary_and += 1,
                Gate::NaryOr(_) => counts.nary_or += 1,
                Gate::Threshold { .. } => counts.threshold += 1,
                Gate::Mod { .. } => counts.modulo += 1,
            }
        }
        counts
    }
}

/// Counts of each gate type in a circuit.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct GateCounts {
    /// Number of primary input gates.
    pub inputs: usize,
    /// Number of constant (true/false) gates.
    pub constants: usize,
    /// Number of unary NOT gates.
    pub not: usize,
    /// Number of binary AND gates.
    pub and2: usize,
    /// Number of binary OR gates.
    pub or2: usize,
    /// Number of binary XOR gates.
    pub xor2: usize,
    /// Number of n-ary AND gates (fan-in > 2).
    pub nary_and: usize,
    /// Number of n-ary OR gates (fan-in > 2).
    pub nary_or: usize,
    /// Number of threshold gates.
    pub threshold: usize,
    /// Number of modulo gates.
    pub modulo: usize,
}

impl GateCounts {
    /// Total number of non-input gates.
    pub fn total_gates(&self) -> usize {
        self.constants
            + self.not
            + self.and2
            + self.or2
            + self.xor2
            + self.nary_and
            + self.nary_or
            + self.threshold
            + self.modulo
    }
}

#[cfg(test)]
#[path = "analyzer_tests.rs"]
mod tests;
