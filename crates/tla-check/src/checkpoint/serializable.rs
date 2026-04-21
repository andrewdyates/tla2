// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Serializable representations of TLA+ values and states for checkpoint I/O.
//!
//! [`SerializableValue`] converts between TLA+ [`Value`] types and a
//! JSON-safe tagged enum. [`SerializableState`] wraps a list of named
//! variable–value pairs.

use crate::state::State;
use crate::value::{intern_string, IntIntervalFunc, RecordValue, SortedSet, Value};
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::io;
use std::sync::Arc;

/// Serializable value representation for JSON export
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", content = "value")]
#[non_exhaustive]
pub enum SerializableValue {
    Bool(bool),
    Int(String), // BigInt as string
    String(String),
    Set(Vec<SerializableValue>),
    Seq(Vec<SerializableValue>),
    Record(Vec<(String, SerializableValue)>),
    Tuple(Vec<SerializableValue>),
    ModelValue(String),
    // Lazy values are enumerated for checkpoint
    Interval { lo: String, hi: String },
}

impl SerializableValue {
    fn parse_bigint(input: &str, context: &str) -> io::Result<BigInt> {
        input.parse::<BigInt>().map_err(|e| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("invalid integer in checkpoint {context}: {e}"),
            )
        })
    }

    /// Convert a Value to its serializable form.
    ///
    /// Returns an error for values that cannot be serialized without an evaluation
    /// context: `SetPred`, `LazyFunc`, `Closure`, infinite sets (`StringSet`,
    /// `AnySet`, `SeqSet`). States must be materialized (via
    /// `materialize_array_state`) before checkpointing to avoid data loss.
    pub fn from_value(value: &Value) -> io::Result<Self> {
        match value {
            Value::Bool(b) => Ok(SerializableValue::Bool(*b)),
            Value::SmallInt(n) => Ok(SerializableValue::Int(n.to_string())),
            Value::Int(n) => Ok(SerializableValue::Int(n.to_string())),
            Value::String(s) => Ok(SerializableValue::String(s.to_string())),
            Value::Set(s) => {
                let elems: Vec<_> = s
                    .iter()
                    .map(SerializableValue::from_value)
                    .collect::<io::Result<_>>()?;
                Ok(SerializableValue::Set(elems))
            }
            Value::Interval(iv) => Ok(SerializableValue::Interval {
                lo: iv.low().to_string(),
                hi: iv.high().to_string(),
            }),
            // SetPred MUST be handled before the lazy-set catch-all.
            // SetPred.iter_set() returns None (needs EvalCtx for materialization),
            // so the old code silently serialized it as an empty set — data loss.
            // Fix for #2115: fail loudly instead.
            Value::SetPred(_) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Cannot serialize SetPred value for checkpoint: SetPred requires an \
                 EvalCtx for materialization. States must be materialized before \
                 checkpointing (see materialize_array_state).",
            )),
            Value::Subset(_)
            | Value::FuncSet(_)
            | Value::RecordSet(_)
            | Value::TupleSet(_)
            | Value::SetCup(_)
            | Value::SetCap(_)
            | Value::SetDiff(_)
            | Value::KSubset(_)
            | Value::BigUnion(_) => {
                // Lazy set types (excluding SetPred) — enumerate for checkpoint
                if let Some(iter) = value.iter_set() {
                    let elements: Vec<_> = iter
                        .map(|v| SerializableValue::from_value(&v))
                        .collect::<io::Result<_>>()?;
                    Ok(SerializableValue::Set(elements))
                } else {
                    // Can't enumerate — shouldn't happen for these types,
                    // but fail loudly rather than silently corrupting data
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "Cannot serialize lazy set value for checkpoint: iter_set() \
                             returned None for {}. States must be materialized before \
                             checkpointing (see materialize_array_state).",
                            value.type_name()
                        ),
                    ))
                }
            }
            Value::Func(f) => {
                // Serialize function as set of tuples
                let pairs: Vec<_> = f
                    .mapping_iter()
                    .map(|(k, v)| {
                        Ok(SerializableValue::Tuple(vec![
                            SerializableValue::from_value(k)?,
                            SerializableValue::from_value(v)?,
                        ]))
                    })
                    .collect::<io::Result<_>>()?;
                Ok(SerializableValue::Set(pairs))
            }
            Value::IntFunc(f) => {
                // Serialize IntFunc as set of tuples (like Func)
                let pairs: Vec<_> = f
                    .values()
                    .iter()
                    .enumerate()
                    .map(|(i, value)| {
                        let k = Value::SmallInt(IntIntervalFunc::min(f) + i as i64);
                        Ok(SerializableValue::Tuple(vec![
                            SerializableValue::from_value(&k)?,
                            SerializableValue::from_value(value)?,
                        ]))
                    })
                    .collect::<io::Result<_>>()?;
                Ok(SerializableValue::Set(pairs))
            }
            Value::LazyFunc(_) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Cannot serialize LazyFunc value for checkpoint: LazyFunc requires an \
                 EvalCtx for materialization. States must be materialized before \
                 checkpointing (see materialize_array_state).",
            )),
            Value::Seq(s) => {
                let elems = s
                    .iter()
                    .map(SerializableValue::from_value)
                    .collect::<io::Result<_>>()?;
                Ok(SerializableValue::Seq(elems))
            }
            Value::Record(r) => {
                let fields = r
                    .iter_str()
                    .map(|(k, v)| Ok((k.to_string(), SerializableValue::from_value(v)?)))
                    .collect::<io::Result<_>>()?;
                Ok(SerializableValue::Record(fields))
            }
            Value::Tuple(t) => {
                let elems = t
                    .iter()
                    .map(SerializableValue::from_value)
                    .collect::<io::Result<_>>()?;
                Ok(SerializableValue::Tuple(elems))
            }
            Value::ModelValue(m) => Ok(SerializableValue::ModelValue(m.to_string())),
            Value::Closure(_) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Cannot serialize Closure value for checkpoint: Closures cannot appear \
                 in state variables. States must be materialized before checkpointing.",
            )),
            Value::StringSet | Value::AnySet | Value::SeqSet(_) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Cannot serialize infinite set {} for checkpoint: infinite sets \
                     cannot appear in state variables.",
                    value.type_name()
                ),
            )),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Cannot serialize unknown Value variant {} for checkpoint.",
                    value.type_name()
                ),
            )),
        }
    }

    /// Convert back to a Value
    pub fn to_value(&self) -> io::Result<Value> {
        match self {
            SerializableValue::Bool(b) => Ok(Value::Bool(*b)),
            SerializableValue::Int(s) => {
                // Use big_int to normalize to SmallInt when value fits
                Ok(Value::big_int(Self::parse_bigint(s, "Int")?))
            }
            SerializableValue::String(s) => Ok(Value::String(intern_string(s.as_str()))),
            SerializableValue::Set(elems) => {
                let set: SortedSet = elems
                    .iter()
                    .map(SerializableValue::to_value)
                    .collect::<io::Result<_>>()?;
                Ok(Value::from_sorted_set(set))
            }
            SerializableValue::Seq(elems) => {
                let seq_values: Vec<Value> = elems
                    .iter()
                    .map(SerializableValue::to_value)
                    .collect::<io::Result<_>>()?;
                Ok(Value::seq(seq_values))
            }
            SerializableValue::Record(fields) => {
                let record: RecordValue = fields
                    .iter()
                    .map(|(k, v)| Ok((intern_string(k.as_str()), v.to_value()?)))
                    .collect::<io::Result<_>>()?;
                Ok(Value::Record(record))
            }
            SerializableValue::Tuple(elems) => Ok(Value::Tuple(
                elems
                    .iter()
                    .map(SerializableValue::to_value)
                    .collect::<io::Result<_>>()?,
            )),
            SerializableValue::ModelValue(m) => Value::try_model_value(m.as_str()).map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("invalid model value in checkpoint {:?}: {}", m, e),
                )
            }),
            SerializableValue::Interval { lo, hi } => {
                let lo = Self::parse_bigint(lo, "Interval.lo")?;
                let hi = Self::parse_bigint(hi, "Interval.hi")?;
                Ok(Value::Interval(Arc::new(crate::value::IntervalValue::new(
                    lo, hi,
                ))))
            }
        }
    }
}

/// Serializable state representation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SerializableState {
    pub vars: Vec<(String, SerializableValue)>,
}

impl SerializableState {
    /// Convert a State to serializable form.
    ///
    /// Returns an error if any variable holds an unmaterialized `SetPred`.
    pub fn from_state(state: &State) -> io::Result<Self> {
        let vars = state
            .vars()
            .map(|(k, v)| Ok((k.to_string(), SerializableValue::from_value(v)?)))
            .collect::<io::Result<_>>()?;
        Ok(SerializableState { vars })
    }

    /// Convert back to a State
    pub fn to_state(&self) -> io::Result<State> {
        let mut state = State::new();
        for (name, value) in &self.vars {
            state = state.with_var(name.as_str(), value.to_value()?);
        }
        Ok(state)
    }
}
