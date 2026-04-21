// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Circuit synthesis algorithms.
//!
//! Provides methods for:
//! - Finding minimum-size circuits for Boolean functions
//! - Enumerating all circuits of a given size
//! - SAT-based circuit synthesis

use crate::{Circuit, CircuitAnalyzer, Gate, GateId, TruthTable};
use z4_sat::{Literal, Solver as SatSolver};

/// Circuit synthesizer for finding optimal or bounded circuits.
pub struct CircuitSynthesizer;

/// Gate type for enumeration (excluding n-ary gates for simplicity).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimpleGateType {
    Not,
    And,
    Or,
    Xor,
}

impl CircuitSynthesizer {
    /// Find a minimum-size circuit that computes the given function.
    ///
    /// Uses brute-force enumeration, so only practical for small functions (n <= 4)
    /// and small circuit sizes (size <= 6).
    ///
    /// Returns `None` if no circuit of size <= `max_size` computes the function.
    pub fn synthesize_minimum(function: &TruthTable, max_size: usize) -> Option<Circuit> {
        // Try each size from 0 up to max_size
        for size in 0..=max_size {
            if let Some(circuit) = Self::find_circuit_of_size(function, size) {
                return Some(circuit);
            }
        }
        None
    }

    /// Find any circuit of exactly the given size that computes the function.
    pub fn find_circuit_of_size(function: &TruthTable, size: usize) -> Option<Circuit> {
        let n = function.num_inputs();

        // Size 0: check if function is an input variable or constant
        if size == 0 {
            // Check constants
            if function.is_true() {
                return Some(Circuit::constant(n, true));
            }
            if function.is_false() {
                return Some(Circuit::constant(n, false));
            }
            // Check input variables
            for i in 0..n {
                if *function == TruthTable::variable(n, i) {
                    return Some(Circuit::identity(n, i));
                }
            }
            return None;
        }

        // For larger sizes, enumerate circuits
        Self::enumerate_circuits(n, size)
            .find(|circuit| CircuitAnalyzer::computes(circuit, function))
    }

    /// Enumerate all circuits with the given number of inputs and non-input gates.
    ///
    /// This is exponential in size, so only use for small sizes (size <= 6).
    pub fn enumerate_circuits(num_inputs: usize, num_gates: usize) -> CircuitEnumerator {
        CircuitEnumerator::new(num_inputs, num_gates)
    }

    /// Use SAT to check if there exists a circuit of given size that computes the function.
    ///
    /// This encodes "does there exist a circuit C of size s such that C computes f?"
    /// as a SAT problem and uses Z4 to solve it.
    ///
    /// More efficient than brute-force enumeration for larger circuits.
    pub fn sat_synthesize(
        function: &TruthTable,
        size: usize,
        gate_types: &[SimpleGateType],
    ) -> Option<Circuit> {
        let n = function.num_inputs();

        // For small cases, fall back to enumeration (simpler and fast enough)
        if n <= 4 && size <= 5 {
            return Self::find_circuit_of_size(function, size);
        }

        // For larger cases, use SAT encoding
        Self::sat_encode_and_solve(function, size, gate_types)
    }

    /// Full SAT encoding for circuit synthesis.
    fn sat_encode_and_solve(
        function: &TruthTable,
        size: usize,
        gate_types: &[SimpleGateType],
    ) -> Option<Circuit> {
        let n = function.num_inputs();
        let num_nodes = n + size;
        let num_types = gate_types.len();
        let num_inputs_per_tt = 1 << n;

        // Variable allocation:
        // - type_var(g, t): gate g has type t
        // - input_var(g, slot, j): gate g's input slot connects to node j
        // - value_var(g, x): gate g outputs 1 on truth table row x

        // Compute total number of variables needed
        let type_vars_count = size * num_types;
        let input_vars_count = size * 2 * num_nodes;
        let value_vars_count = num_nodes * num_inputs_per_tt;
        let total_vars = type_vars_count + input_vars_count + value_vars_count;

        // Helper to compute variable indices (1-indexed for SAT)
        let type_var = |g: usize, t: usize| -> i32 {
            let g_idx = g - n; // gate index within gates (0 to size-1)
            (g_idx * num_types + t + 1) as i32
        };

        let type_var_offset = size * num_types;

        // Each gate has 2 input slots (for binary gates)
        // For NOT, we only use slot 0
        let input_var = |g: usize, slot: usize, j: usize| -> i32 {
            let g_idx = g - n;
            let idx = g_idx * 2 * num_nodes + slot * num_nodes + j;
            (type_var_offset + idx + 1) as i32
        };

        let input_var_offset = type_var_offset + size * 2 * num_nodes;

        let value_var = |g: usize, x: usize| -> i32 {
            let idx = g * num_inputs_per_tt + x;
            (input_var_offset + idx + 1) as i32
        };

        let mut solver = SatSolver::new(total_vars + 1);

        // Constraint 1: Each gate has exactly one type
        for g in n..num_nodes {
            // At least one type
            let clause: Vec<Literal> = (0..num_types)
                .map(|t| Literal::from(type_var(g, t)))
                .collect();
            solver.add_clause(clause);

            // At most one type (pairwise exclusion)
            for t1 in 0..num_types {
                for t2 in (t1 + 1)..num_types {
                    solver.add_clause(vec![
                        Literal::from(-type_var(g, t1)),
                        Literal::from(-type_var(g, t2)),
                    ]);
                }
            }
        }

        // Constraint 2: Each input slot selects exactly one previous node
        for g in n..num_nodes {
            for slot in 0..2 {
                // At least one selection
                let clause: Vec<Literal> = (0..g)
                    .map(|j| Literal::from(input_var(g, slot, j)))
                    .collect();
                if !clause.is_empty() {
                    solver.add_clause(clause);
                }

                // At most one selection
                for j1 in 0..g {
                    for j2 in (j1 + 1)..g {
                        solver.add_clause(vec![
                            Literal::from(-input_var(g, slot, j1)),
                            Literal::from(-input_var(g, slot, j2)),
                        ]);
                    }
                }
            }
        }

        // Constraint 3: Input node values are fixed by truth table row
        for i in 0..n {
            for x in 0..num_inputs_per_tt {
                let input_val = (x >> i) & 1 == 1;
                let lit = if input_val {
                    Literal::from(value_var(i, x))
                } else {
                    Literal::from(-value_var(i, x))
                };
                solver.add_clause(vec![lit]);
            }
        }

        // Constraint 4: Gate semantics
        // For each gate g, each type t, each input x, encode what the output should be
        for g in n..num_nodes {
            for (t, &gate_type) in gate_types.iter().enumerate() {
                for x in 0..num_inputs_per_tt {
                    // For each possible input selection, encode the gate function
                    for j0 in 0..g {
                        for j1 in 0..g {
                            // If gate g has type t and inputs j0, j1, then:
                            // value[g][x] = gate_function(value[j0][x], value[j1][x])

                            let implies_prefix =
                                vec![-type_var(g, t), -input_var(g, 0, j0), -input_var(g, 1, j1)];

                            match gate_type {
                                SimpleGateType::Not => {
                                    // value[g][x] = NOT value[j0][x]
                                    // (prefix AND value[j0][x]) => NOT value[g][x]
                                    // (prefix AND NOT value[j0][x]) => value[g][x]
                                    let mut clause1 = implies_prefix.clone();
                                    clause1.push(-value_var(j0, x));
                                    clause1.push(value_var(g, x));
                                    solver.add_clause(
                                        clause1.iter().map(|&v| Literal::from(v)).collect(),
                                    );

                                    let mut clause2 = implies_prefix.clone();
                                    clause2.push(value_var(j0, x));
                                    clause2.push(-value_var(g, x));
                                    solver.add_clause(
                                        clause2.iter().map(|&v| Literal::from(v)).collect(),
                                    );
                                }
                                SimpleGateType::And => {
                                    // value[g][x] = value[j0][x] AND value[j1][x]
                                    // (prefix AND j0 AND j1) => g
                                    let mut clause1 = implies_prefix.clone();
                                    clause1.push(-value_var(j0, x));
                                    clause1.push(-value_var(j1, x));
                                    clause1.push(value_var(g, x));
                                    solver.add_clause(
                                        clause1.iter().map(|&v| Literal::from(v)).collect(),
                                    );

                                    // (prefix AND NOT j0) => NOT g
                                    let mut clause2 = implies_prefix.clone();
                                    clause2.push(value_var(j0, x));
                                    clause2.push(-value_var(g, x));
                                    solver.add_clause(
                                        clause2.iter().map(|&v| Literal::from(v)).collect(),
                                    );

                                    // (prefix AND NOT j1) => NOT g
                                    let mut clause3 = implies_prefix.clone();
                                    clause3.push(value_var(j1, x));
                                    clause3.push(-value_var(g, x));
                                    solver.add_clause(
                                        clause3.iter().map(|&v| Literal::from(v)).collect(),
                                    );
                                }
                                SimpleGateType::Or => {
                                    // value[g][x] = value[j0][x] OR value[j1][x]
                                    // (prefix AND NOT j0 AND NOT j1) => NOT g
                                    let mut clause1 = implies_prefix.clone();
                                    clause1.push(value_var(j0, x));
                                    clause1.push(value_var(j1, x));
                                    clause1.push(-value_var(g, x));
                                    solver.add_clause(
                                        clause1.iter().map(|&v| Literal::from(v)).collect(),
                                    );

                                    // (prefix AND j0) => g
                                    let mut clause2 = implies_prefix.clone();
                                    clause2.push(-value_var(j0, x));
                                    clause2.push(value_var(g, x));
                                    solver.add_clause(
                                        clause2.iter().map(|&v| Literal::from(v)).collect(),
                                    );

                                    // (prefix AND j1) => g
                                    let mut clause3 = implies_prefix.clone();
                                    clause3.push(-value_var(j1, x));
                                    clause3.push(value_var(g, x));
                                    solver.add_clause(
                                        clause3.iter().map(|&v| Literal::from(v)).collect(),
                                    );
                                }
                                SimpleGateType::Xor => {
                                    // value[g][x] = value[j0][x] XOR value[j1][x]
                                    // Four cases based on j0 and j1 values
                                    // (prefix AND j0 AND j1) => NOT g
                                    let mut clause1 = implies_prefix.clone();
                                    clause1.push(-value_var(j0, x));
                                    clause1.push(-value_var(j1, x));
                                    clause1.push(-value_var(g, x));
                                    solver.add_clause(
                                        clause1.iter().map(|&v| Literal::from(v)).collect(),
                                    );

                                    // (prefix AND j0 AND NOT j1) => g
                                    let mut clause2 = implies_prefix.clone();
                                    clause2.push(-value_var(j0, x));
                                    clause2.push(value_var(j1, x));
                                    clause2.push(value_var(g, x));
                                    solver.add_clause(
                                        clause2.iter().map(|&v| Literal::from(v)).collect(),
                                    );

                                    // (prefix AND NOT j0 AND j1) => g
                                    let mut clause3 = implies_prefix.clone();
                                    clause3.push(value_var(j0, x));
                                    clause3.push(-value_var(j1, x));
                                    clause3.push(value_var(g, x));
                                    solver.add_clause(
                                        clause3.iter().map(|&v| Literal::from(v)).collect(),
                                    );

                                    // (prefix AND NOT j0 AND NOT j1) => NOT g
                                    let mut clause4 = implies_prefix.clone();
                                    clause4.push(value_var(j0, x));
                                    clause4.push(value_var(j1, x));
                                    clause4.push(-value_var(g, x));
                                    solver.add_clause(
                                        clause4.iter().map(|&v| Literal::from(v)).collect(),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }

        // Constraint 5: Output gate (last gate) must match function
        let output_gate = num_nodes - 1;
        for x in 0..num_inputs_per_tt {
            let expected = function.entries()[x];
            let lit = if expected {
                Literal::from(value_var(output_gate, x))
            } else {
                Literal::from(-value_var(output_gate, x))
            };
            solver.add_clause(vec![lit]);
        }

        // Solve
        solver.solve().into_model().and_then(|model| {
            Self::extract_circuit_from_model(n, size, gate_types, &model, type_var, input_var)
        })
    }

    /// Extract a circuit from a SAT model.
    fn extract_circuit_from_model<F1, F2>(
        n: usize,
        size: usize,
        gate_types: &[SimpleGateType],
        model: &[bool],
        type_var: F1,
        input_var: F2,
    ) -> Option<Circuit>
    where
        F1: Fn(usize, usize) -> i32,
        F2: Fn(usize, usize, usize) -> i32,
    {
        let mut circuit = Circuit::new(n);
        let num_nodes = n + size;

        // Helper to check if variable is true in model (model is 0-indexed, vars are 1-indexed)
        let is_true = |var: i32| -> bool {
            let idx = var.unsigned_abs() as usize;
            if idx < model.len() {
                model[idx]
            } else {
                false
            }
        };

        for g in n..num_nodes {
            // Find gate type
            let mut gate_type = None;
            for (t, &gt) in gate_types.iter().enumerate() {
                if is_true(type_var(g, t)) {
                    gate_type = Some(gt);
                    break;
                }
            }
            let gate_type = gate_type?;

            // Find inputs
            let mut input0 = None;
            let mut input1 = None;
            for j in 0..g {
                if is_true(input_var(g, 0, j)) {
                    input0 = Some(GateId(j));
                }
                if is_true(input_var(g, 1, j)) {
                    input1 = Some(GateId(j));
                }
            }
            let input0 = input0?;
            let input1 = input1.unwrap_or(input0); // For NOT, use same input

            // Create gate
            let gate = match gate_type {
                SimpleGateType::Not => Gate::Not(input0),
                SimpleGateType::And => Gate::And(input0, input1),
                SimpleGateType::Or => Gate::Or(input0, input1),
                SimpleGateType::Xor => Gate::Xor(input0, input1),
            };
            circuit.add_gate(gate);
        }

        // Set output to last gate
        circuit.set_output(GateId(num_nodes - 1));
        Some(circuit)
    }
}

/// Iterator over all circuits with given number of inputs and gates.
pub struct CircuitEnumerator {
    num_inputs: usize,
    num_gates: usize,
    /// Current state: for each gate, (type, input0, input1)
    /// Type: 0=NOT, 1=AND, 2=OR, 3=XOR
    state: Vec<(usize, usize, usize)>,
    done: bool,
}

impl CircuitEnumerator {
    fn new(num_inputs: usize, num_gates: usize) -> Self {
        if num_gates == 0 {
            return Self {
                num_inputs,
                num_gates,
                state: vec![],
                done: true,
            };
        }

        // Initialize state: all gates are NOT of input 0
        let mut state = Vec::with_capacity(num_gates);
        for _i in 0..num_gates {
            state.push((0, 0, 0)); // NOT of first available node
        }

        Self {
            num_inputs,
            num_gates,
            state,
            done: false,
        }
    }

    fn build_circuit(&self) -> Circuit {
        let mut circuit = Circuit::new(self.num_inputs);

        for &(gate_type, input0, input1) in &self.state {
            let gate = match gate_type {
                0 => Gate::Not(GateId(input0)),
                1 => Gate::And(GateId(input0), GateId(input1)),
                2 => Gate::Or(GateId(input0), GateId(input1)),
                3 => Gate::Xor(GateId(input0), GateId(input1)),
                _ => unreachable!(),
            };
            circuit.add_gate(gate);
        }

        // Output is the last gate
        circuit.set_output(GateId(self.num_inputs + self.num_gates - 1));
        circuit
    }

    fn increment(&mut self) -> bool {
        // Increment state like a multi-digit number
        // For each gate i (from 0 to num_gates-1):
        //   - type: 0-3 (NOT, AND, OR, XOR)
        //   - input0: 0 to (num_inputs + i - 1)
        //   - input1: 0 to (num_inputs + i - 1) for binary gates, unused for NOT

        for i in 0..self.num_gates {
            let max_input = self.num_inputs + i;
            let (gate_type, input0, input1) = self.state[i];

            // Try incrementing input1 (for binary gates)
            if gate_type != 0 && input1 + 1 < max_input {
                self.state[i] = (gate_type, input0, input1 + 1);
                return true;
            }

            // Try incrementing input0
            if input0 + 1 < max_input {
                self.state[i] = (gate_type, input0 + 1, 0);
                return true;
            }

            // Try incrementing gate type
            if gate_type + 1 < 4 {
                self.state[i] = (gate_type + 1, 0, 0);
                return true;
            }

            // Reset this digit and carry to next
            self.state[i] = (0, 0, 0);
        }

        // All digits wrapped around - we're done
        false
    }
}

impl Iterator for CircuitEnumerator {
    type Item = Circuit;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let circuit = self.build_circuit();

        if !self.increment() {
            self.done = true;
        }

        Some(circuit)
    }
}

#[cfg(test)]
#[path = "synthesis_tests.rs"]
mod tests;
