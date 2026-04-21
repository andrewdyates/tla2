// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean circuit representation.
//!
//! A Boolean circuit is a directed acyclic graph (DAG) where:
//! - Source nodes are inputs (variables)
//! - Internal nodes are gates (AND, OR, NOT, etc.)
//! - One or more nodes are designated as outputs

use std::fmt;

/// Index of a gate in the circuit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GateId(pub usize);

impl fmt::Display for GateId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "g{}", self.0)
    }
}

/// A Boolean gate in the circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gate {
    /// Input variable (index 0..num_inputs-1)
    Input(usize),
    /// Constant true
    True,
    /// Constant false
    False,
    /// Logical NOT
    Not(GateId),
    /// Binary AND
    And(GateId, GateId),
    /// Binary OR
    Or(GateId, GateId),
    /// Binary XOR
    Xor(GateId, GateId),
    /// N-ary AND (unbounded fan-in, for AC0)
    NaryAnd(Vec<GateId>),
    /// N-ary OR (unbounded fan-in, for AC0)
    NaryOr(Vec<GateId>),
    /// Threshold gate: output 1 iff at least `threshold` inputs are 1 (for TC0)
    Threshold {
        /// Input gates counted by the threshold gate.
        inputs: Vec<GateId>,
        /// Minimum number of true inputs required for output 1.
        threshold: usize,
    },
    /// Mod gate: output 1 iff (sum of inputs) mod modulus == 0 (for ACC0)
    Mod {
        /// Input gates counted for modular parity.
        inputs: Vec<GateId>,
        /// Modulus used for `(sum(inputs) mod modulus) == 0`.
        modulus: usize,
    },
}

impl Gate {
    /// Returns the input GateIds this gate depends on.
    pub fn inputs(&self) -> Vec<GateId> {
        match self {
            Self::Input(_) | Self::True | Self::False => vec![],
            Self::Not(a) => vec![*a],
            Self::And(a, b) | Self::Or(a, b) | Self::Xor(a, b) => vec![*a, *b],
            Self::NaryAnd(inputs)
            | Self::NaryOr(inputs)
            | Self::Threshold { inputs, .. }
            | Self::Mod { inputs, .. } => inputs.clone(),
        }
    }

    /// Returns true if this is an input gate.
    pub fn is_input(&self) -> bool {
        matches!(self, Self::Input(_))
    }

    /// Returns true if this is a constant gate.
    pub fn is_constant(&self) -> bool {
        matches!(self, Self::True | Self::False)
    }

    /// Returns the fan-in (number of inputs) of this gate.
    pub fn fan_in(&self) -> usize {
        match self {
            Self::Input(_) | Self::True | Self::False => 0,
            Self::Not(_) => 1,
            Self::And(_, _) | Self::Or(_, _) | Self::Xor(_, _) => 2,
            Self::NaryAnd(inputs)
            | Self::NaryOr(inputs)
            | Self::Threshold { inputs, .. }
            | Self::Mod { inputs, .. } => inputs.len(),
        }
    }

    /// Evaluate the gate given input values.
    pub fn evaluate(&self, values: &[bool]) -> bool {
        match self {
            Self::Input(i) => values[*i],
            Self::True => true,
            Self::False => false,
            Self::Not(a) => !values[a.0],
            Self::And(a, b) => values[a.0] && values[b.0],
            Self::Or(a, b) => values[a.0] || values[b.0],
            Self::Xor(a, b) => values[a.0] ^ values[b.0],
            Self::NaryAnd(inputs) => inputs.iter().all(|g| values[g.0]),
            Self::NaryOr(inputs) => inputs.iter().any(|g| values[g.0]),
            Self::Threshold { inputs, threshold } => {
                let count: usize = inputs.iter().filter(|g| values[g.0]).count();
                count >= *threshold
            }
            Self::Mod { inputs, modulus } => {
                let sum: usize = inputs.iter().filter(|g| values[g.0]).count();
                sum.is_multiple_of(*modulus)
            }
        }
    }
}

/// A Boolean circuit represented as a DAG of gates.
#[derive(Debug, Clone)]
pub struct Circuit {
    /// Number of input variables
    num_inputs: usize,
    /// All gates in the circuit (including inputs)
    gates: Vec<Gate>,
    /// Output gate IDs
    outputs: Vec<GateId>,
}

impl Circuit {
    /// Create a new circuit with the given number of inputs.
    ///
    /// Input gates are automatically created as gates 0..num_inputs-1.
    pub fn new(num_inputs: usize) -> Self {
        let mut gates = Vec::with_capacity(num_inputs);
        for i in 0..num_inputs {
            gates.push(Gate::Input(i));
        }
        Self {
            num_inputs,
            gates,
            outputs: vec![],
        }
    }

    /// Get the number of input variables.
    pub fn num_inputs(&self) -> usize {
        self.num_inputs
    }

    /// Get the total number of gates (including inputs).
    pub fn num_gates(&self) -> usize {
        self.gates.len()
    }

    /// Get the gate ID for input variable i.
    pub fn input(&self, i: usize) -> GateId {
        assert!(i < self.num_inputs, "Input index out of bounds");
        GateId(i)
    }

    /// Add a gate to the circuit and return its ID.
    pub fn add_gate(&mut self, gate: Gate) -> GateId {
        // Validate that all referenced gates exist
        for input in gate.inputs() {
            assert!(
                input.0 < self.gates.len(),
                "Gate references non-existent gate {input}"
            );
        }
        // Validate Mod gate has non-zero modulus (would panic in evaluate)
        if let Gate::Mod { modulus, .. } = &gate {
            assert!(*modulus > 0, "Mod gate modulus must be positive");
        }
        let id = GateId(self.gates.len());
        self.gates.push(gate);
        id
    }

    /// Set the output of the circuit (single output).
    pub fn set_output(&mut self, gate: GateId) {
        assert!(gate.0 < self.gates.len(), "Output gate does not exist");
        self.outputs = vec![gate];
    }

    /// Set multiple outputs for the circuit.
    pub fn set_outputs(&mut self, gates: Vec<GateId>) {
        for gate in &gates {
            assert!(gate.0 < self.gates.len(), "Output gate does not exist");
        }
        self.outputs = gates;
    }

    /// Get the output gate IDs.
    pub fn outputs(&self) -> &[GateId] {
        &self.outputs
    }

    /// Get a gate by its ID.
    pub fn gate(&self, id: GateId) -> &Gate {
        &self.gates[id.0]
    }

    /// Get all gates in the circuit.
    pub fn gates(&self) -> &[Gate] {
        &self.gates
    }

    /// Evaluate the circuit on the given input assignment.
    /// Returns the values of all output gates.
    pub fn evaluate(&self, inputs: &[bool]) -> Vec<bool> {
        assert_eq!(
            inputs.len(),
            self.num_inputs,
            "Wrong number of inputs: expected {}, got {}",
            self.num_inputs,
            inputs.len()
        );

        // Evaluate all gates in topological order (they're already ordered)
        let mut values = vec![false; self.gates.len()];
        for (i, gate) in self.gates.iter().enumerate() {
            values[i] = gate.evaluate(&values);
            // For input gates, override with actual input
            if let Gate::Input(idx) = gate {
                values[i] = inputs[*idx];
            }
        }

        // Return output values
        self.outputs.iter().map(|g| values[g.0]).collect()
    }

    /// Evaluate the circuit for a single output (assumes single output circuit).
    pub fn evaluate_single(&self, inputs: &[bool]) -> bool {
        let outputs = self.evaluate(inputs);
        assert_eq!(outputs.len(), 1, "Circuit has multiple outputs");
        outputs[0]
    }

    /// Create a circuit that computes the constant function.
    pub fn constant(num_inputs: usize, value: bool) -> Self {
        let mut circuit = Self::new(num_inputs);
        let gate = if value { Gate::True } else { Gate::False };
        let id = circuit.add_gate(gate);
        circuit.set_output(id);
        circuit
    }

    /// Create a circuit that returns the value of input i.
    pub fn identity(num_inputs: usize, input_idx: usize) -> Self {
        assert!(input_idx < num_inputs);
        let mut circuit = Self::new(num_inputs);
        circuit.set_output(circuit.input(input_idx));
        circuit
    }

    /// Create a circuit that computes NOT of input i.
    pub fn not_input(num_inputs: usize, input_idx: usize) -> Self {
        assert!(input_idx < num_inputs);
        let mut circuit = Self::new(num_inputs);
        let inp = circuit.input(input_idx);
        let not = circuit.add_gate(Gate::Not(inp));
        circuit.set_output(not);
        circuit
    }

    /// Create a circuit that computes AND of two inputs.
    pub fn and2(num_inputs: usize, a: usize, b: usize) -> Self {
        assert!(a < num_inputs && b < num_inputs);
        let mut circuit = Self::new(num_inputs);
        let ga = circuit.input(a);
        let gb = circuit.input(b);
        let and = circuit.add_gate(Gate::And(ga, gb));
        circuit.set_output(and);
        circuit
    }

    /// Create a circuit that computes OR of two inputs.
    pub fn or2(num_inputs: usize, a: usize, b: usize) -> Self {
        assert!(a < num_inputs && b < num_inputs);
        let mut circuit = Self::new(num_inputs);
        let ga = circuit.input(a);
        let gb = circuit.input(b);
        let or = circuit.add_gate(Gate::Or(ga, gb));
        circuit.set_output(or);
        circuit
    }

    /// Create a circuit that computes XOR of two inputs.
    pub fn xor2(num_inputs: usize, a: usize, b: usize) -> Self {
        assert!(a < num_inputs && b < num_inputs);
        let mut circuit = Self::new(num_inputs);
        let ga = circuit.input(a);
        let gb = circuit.input(b);
        let xor = circuit.add_gate(Gate::Xor(ga, gb));
        circuit.set_output(xor);
        circuit
    }
}

#[cfg(test)]
#[path = "circuit_tests.rs"]
mod tests;
