#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean Circuit Analysis and Synthesis
//!
//! This crate provides tools for analyzing and synthesizing Boolean circuits.
//! It is a foundation for complexity analysis in the Archimedes platform.
//!
//! ## Features
//!
//! - **Circuit representation**: DAG of gates (AND, OR, NOT, XOR, threshold, mod)
//! - **Analysis**: Size, depth, circuit class membership
//! - **Synthesis**: Find minimum circuit for a function (brute force for small n)
//! - **Enumeration**: Generate all circuits of given size
//! - **SAT encoding**: Check if circuit computes a function via Z4
//!
//! ## Example
//!
//! ```
//! use z4_circuits::{Circuit, Gate, GateId, TruthTable, CircuitAnalyzer};
//!
//! // Build XOR circuit: (x AND NOT y) OR (NOT x AND y)
//! let mut circuit = Circuit::new(2);
//! let x = GateId(0);  // input x
//! let y = GateId(1);  // input y
//! let not_x = circuit.add_gate(Gate::Not(x));
//! let not_y = circuit.add_gate(Gate::Not(y));
//! let x_and_not_y = circuit.add_gate(Gate::And(x, not_y));
//! let not_x_and_y = circuit.add_gate(Gate::And(not_x, y));
//! let xor = circuit.add_gate(Gate::Or(x_and_not_y, not_x_and_y));
//! circuit.set_output(xor);
//!
//! // Analyze
//! assert_eq!(CircuitAnalyzer::size(&circuit), 5);  // 5 gates (not counting inputs)
//! assert_eq!(CircuitAnalyzer::depth(&circuit), 3); // longest path: y -> not_y -> x_and_not_y -> xor
//!
//! // Verify it computes XOR
//! let xor_table = TruthTable::from_fn(2, |inputs| inputs[0] ^ inputs[1]);
//! assert!(CircuitAnalyzer::computes(&circuit, &xor_table));
//! ```
//!
//! ## Circuit Classes
//!
//! - **AC0**: Constant depth, unbounded fan-in AND/OR, polynomial size
//! - **ACC0**: AC0 with MOD gates
//! - **TC0**: AC0 with threshold gates
//! - **NC1**: Logarithmic depth, bounded fan-in, polynomial size
//! - **P/poly**: Polynomial size
//!
//! ## References
//!
//! - Jukna, "Boolean Function Complexity: Advances and Frontiers"
//! - Williams, "Non-uniform ACC Circuit Lower Bounds"
//! - Arora & Barak, "Computational Complexity: A Modern Approach"

mod analyzer;
mod circuit;
mod synthesis;
mod truth_table;

pub use analyzer::{CircuitAnalyzer, CircuitClass};
pub use circuit::{Circuit, Gate, GateId};
pub use synthesis::CircuitSynthesizer;
pub use truth_table::TruthTable;
