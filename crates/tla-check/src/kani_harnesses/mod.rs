// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kani formal verification harnesses for TLA2 core components
//!
//! This module contains Kani proofs for critical properties of the model checker:
//! - Fingerprint determinism: Same value → same fingerprint
//! - Value equality reflexivity: v == v for all v
//! - Value equality symmetry: v1 == v2 implies v2 == v1
//! - State fingerprint determinism: Same state → same fingerprint
//!
//! These harnesses are only compiled when running `cargo kani`.
//! They verify formal properties of the core data structures.
//!
//! # Running Verification
//!
//! ```bash
//! # Install Kani first: cargo install --locked kani-verifier
//! # Then verify:
//! cargo kani --harness verify_value_fingerprint_deterministic
//! cargo kani --harness verify_value_equality_reflexive
//! cargo kani --harness verify_state_fingerprint_deterministic
//! ```
//!
//! # Properties Verified
//!
//! ## P1: Fingerprint Determinism
//! For any value v, calling value_fingerprint(v) twice returns the same result.
//! This is critical for correct state deduplication.
//!
//! ## P2: Value Equality Reflexivity
//! For any value v, v == v is always true.
//! Required for Eq trait correctness.
//!
//! ## P3: Value Equality Symmetry
//! For any values v1, v2: (v1 == v2) implies (v2 == v1).
//! Required for Eq trait correctness.
//!
//! ## P4: State Fingerprint Determinism
//! For any state s, calling s.fingerprint() twice returns the same result.
//! Critical for state deduplication in model checking.
//!
//! ## P5: Type Discrimination
//! Values of different primitive types are never equal.
//! E.g., Bool(true) != Int(1).

mod arithmetic_bool_algebra;
#[cfg(any(kani, test))]
mod compat_helpers;
mod equality;
mod fingerprint;
mod functions;
mod intervals;
mod ordering;
mod property_classification;
mod records_tuples_sequences;
mod set_ops;
mod state_props;

// =========================================================================
// Shared generators for Kani harnesses
// =========================================================================

#[cfg(kani)]
pub(super) mod kani_generators {
    pub use super::compat_helpers::*;

    use crate::value::{FuncValue, IntervalValue, Value};
    use num_bigint::BigInt;
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;
    use std::sync::Arc;

    /// Generate an arbitrary boolean value
    pub fn any_bool_value() -> Value {
        Value::Bool(kani::any())
    }

    /// Generate an arbitrary small integer value (-128..127)
    /// Uses SmallInt to avoid BigInt unwinding that crashes CBMC (SIGSEGV at 2047 iterations).
    pub fn any_small_int_value() -> Value {
        let n: i8 = kani::any();
        Value::SmallInt(n as i64)
    }

    /// Generate an arbitrary short string value (0-4 chars from limited alphabet)
    /// We limit string length and alphabet for tractable verification
    pub fn any_short_string_value() -> Value {
        // Use a very limited string space for tractability
        let choice: u8 = kani::any();
        kani::assume(choice < 8);
        let s = match choice {
            0 => "",
            1 => "a",
            2 => "b",
            3 => "ab",
            4 => "ba",
            5 => "x",
            6 => "y",
            _ => "z",
        };
        Value::String(Arc::from(s))
    }

    /// Generate an arbitrary primitive value (Bool, Int, or String)
    pub fn any_primitive_value() -> Value {
        let choice: u8 = kani::any();
        kani::assume(choice < 3);
        match choice {
            0 => any_bool_value(),
            1 => any_small_int_value(),
            _ => any_short_string_value(),
        }
    }

    /// Generate an arbitrary small set (0-3 elements)
    pub fn any_small_set() -> Value {
        let choice: u8 = kani::any();
        kani::assume(choice < 8);
        match choice {
            0 => make_set(vec![]),
            1 => make_set(vec![Value::int(1)]),
            2 => make_set(vec![Value::int(2)]),
            3 => make_set(vec![Value::int(1), Value::int(2)]),
            4 => make_set(vec![Value::Bool(true)]),
            5 => make_set(vec![Value::Bool(false)]),
            6 => make_set(vec![Value::Bool(true), Value::Bool(false)]),
            _ => make_set(vec![Value::int(1), Value::int(2), Value::int(3)]),
        }
    }

    /// Generate an arbitrary small sequence
    pub fn any_small_seq() -> Value {
        let choice: u8 = kani::any();
        kani::assume(choice < 5);

        match choice {
            0 => Value::Seq(Arc::new(Vec::new().into())),
            1 => Value::Seq(Arc::new(vec![Value::Bool(kani::any())].into())),
            2 => {
                let n: i8 = kani::any();
                Value::Seq(Arc::new(vec![Value::int(n as i64)].into()))
            }
            3 => Value::Seq(Arc::new(
                vec![Value::Bool(kani::any()), Value::Bool(kani::any())].into(),
            )),
            _ => {
                let n1: i8 = kani::any();
                let n2: i8 = kani::any();
                Value::Seq(Arc::new(
                    vec![Value::int(n1 as i64), Value::int(n2 as i64)].into(),
                ))
            }
        }
    }

    /// Generate an arbitrary small tuple
    pub fn any_small_tuple() -> Value {
        let choice: u8 = kani::any();
        kani::assume(choice < 4);

        match choice {
            0 => Value::Tuple(Vec::new().into()),
            1 => Value::Tuple(vec![Value::Bool(kani::any())].into()),
            2 => {
                let n: i8 = kani::any();
                Value::Tuple(vec![Value::int(n as i64)].into())
            }
            _ => Value::Tuple(vec![Value::Bool(kani::any()), Value::Bool(kani::any())].into()),
        }
    }

    /// Generate an arbitrary small function
    pub fn any_small_func() -> FuncValue {
        let choice: u8 = kani::any();
        kani::assume(choice < 6);

        match choice {
            0 => make_func(vec![]),
            1 => {
                // {1} -> Bool
                make_func(vec![(Value::int(1), Value::Bool(kani::any()))])
            }
            2 => {
                // {1, 2} -> Bool
                make_func(vec![
                    (Value::int(1), Value::Bool(kani::any())),
                    (Value::int(2), Value::Bool(kani::any())),
                ])
            }
            3 => {
                // {TRUE, FALSE} -> Int
                let n1: i8 = kani::any();
                let n2: i8 = kani::any();
                make_func(vec![
                    (Value::Bool(true), Value::int(n1 as i64)),
                    (Value::Bool(false), Value::int(n2 as i64)),
                ])
            }
            4 => {
                // {1} -> Int (identity-like)
                make_func(vec![(Value::int(1), Value::int(1))])
            }
            _ => {
                // {0, 1} -> {0, 1}
                let b1: bool = kani::any();
                let b2: bool = kani::any();
                make_func(vec![
                    (Value::int(0), Value::int(if b1 { 1 } else { 0 })),
                    (Value::int(1), Value::int(if b2 { 1 } else { 0 })),
                ])
            }
        }
    }

    /// Helper: Create a small function value (fixed values for deterministic testing)
    pub fn any_small_func_fixed() -> FuncValue {
        let choice: u8 = kani::any();
        kani::assume(choice < 3);

        match choice {
            0 => make_func(vec![]),
            1 => make_func(vec![(Value::int(1), Value::Bool(true))]),
            _ => make_func(vec![
                (Value::int(1), Value::Bool(true)),
                (Value::int(2), Value::Bool(false)),
            ]),
        }
    }

    /// Generate an arbitrary small record
    pub fn any_small_record() -> Value {
        use crate::value::RecordValue;
        let choice: u8 = kani::any();
        kani::assume(choice < 4);

        let entries: Vec<(Arc<str>, Value)> = match choice {
            0 => vec![],
            1 => vec![(Arc::from("x"), Value::Bool(kani::any()))],
            2 => {
                let n: i8 = kani::any();
                vec![(Arc::from("x"), Value::int(n as i64))]
            }
            _ => {
                let n: i8 = kani::any();
                vec![
                    (Arc::from("x"), Value::Bool(kani::any())),
                    (Arc::from("y"), Value::int(n as i64)),
                ]
            }
        };
        Value::Record(RecordValue::from_sorted_entries(entries))
    }

    /// Helper: Create a small record value as sorted entries
    pub fn any_small_record_entries() -> Vec<(Arc<str>, Value)> {
        let choice: u8 = kani::any();
        kani::assume(choice < 3);

        match choice {
            0 => vec![],
            1 => vec![(Arc::from("x"), Value::int(1))],
            _ => vec![
                (Arc::from("x"), Value::int(1)),
                (Arc::from("y"), Value::Bool(true)),
            ],
        }
    }

    /// Generate an arbitrary small interval
    pub fn any_small_interval() -> IntervalValue {
        let low: i8 = kani::any();
        let high: i8 = kani::any();
        kani::assume(low >= -10 && low <= 10);
        kani::assume(high >= -10 && high <= 10);
        IntervalValue::new(BigInt::from(low as i64), BigInt::from(high as i64))
    }

    /// Generate an arbitrary model value name
    pub fn any_model_value_name() -> Arc<str> {
        let choice: u8 = kani::any();
        kani::assume(choice < 6);
        match choice {
            0 => Arc::from("m1"),
            1 => Arc::from("m2"),
            2 => Arc::from("m3"),
            3 => Arc::from("a"),
            4 => Arc::from("b"),
            _ => Arc::from("c"),
        }
    }

    /// Generate an arbitrary small set of booleans only (0-3 elements)
    /// This variant avoids BigInt for Kani tractability
    pub fn any_small_set_boolonly() -> Value {
        let choice: u8 = kani::any();
        kani::assume(choice < 4);
        match choice {
            0 => make_set(vec![]),
            1 => make_set(vec![Value::Bool(true)]),
            2 => make_set(vec![Value::Bool(false)]),
            _ => make_set(vec![Value::Bool(true), Value::Bool(false)]),
        }
    }

    /// Generate an arbitrary small sequence of booleans only (0-3 elements)
    pub fn any_small_seq_boolonly() -> Value {
        let choice: u8 = kani::any();
        kani::assume(choice < 5);
        match choice {
            0 => Value::Seq(Arc::new(Vec::new().into())),
            1 => Value::Seq(Arc::new(vec![Value::Bool(true)].into())),
            2 => Value::Seq(Arc::new(vec![Value::Bool(false)].into())),
            3 => Value::Seq(Arc::new(vec![Value::Bool(true), Value::Bool(false)].into())),
            _ => Value::Seq(Arc::new(
                vec![Value::Bool(true), Value::Bool(true), Value::Bool(false)].into(),
            )),
        }
    }

    /// Helper: Create nested function f where f[1] is a function {1 -> true, 2 -> false}
    pub fn create_nested_func() -> FuncValue {
        // Inner function: {1 -> true, 2 -> false}
        let inner = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), Value::Bool(false)),
        ]);

        // Outer function: {1 -> inner}
        make_func(vec![(Value::int(1), Value::Func(Arc::new(inner)))])
    }
}

// =========================================================================
// Shared helpers for test mirrors
// =========================================================================

#[cfg(test)]
pub(super) mod test_helpers {
    pub(super) use super::compat_helpers::*;

    use crate::value::{FuncValue, Value};
    use std::sync::Arc;

    /// Helper: Create nested function f where f[1] is a function {1 -> true, 2 -> false}
    pub fn create_nested_func() -> FuncValue {
        let inner = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), Value::Bool(false)),
        ]);

        make_func(vec![(Value::int(1), Value::Func(Arc::new(inner)))])
    }
}
