// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! JSON-to-Value decoding: `json_to_value` (simple) and `json_to_value_with_path` (with path tracking).

use std::cell::RefCell;
use std::sync::Arc;

use crate::json_output::JsonValue;
use crate::json_path::append_json_path_key;
use crate::value::{FuncValue, IntervalValue, Value};

use super::{
    json_key_string, parse_big_int_decimal, JsonValueDecodeError, JsonValueDecodeErrorAtPath,
};

pub fn json_to_value(value: &JsonValue) -> Result<Value, JsonValueDecodeError> {
    Ok(match value {
        JsonValue::Bool(b) => Value::bool(*b),
        JsonValue::Int(n) => Value::int(*n),
        JsonValue::BigInt(s) => Value::big_int(parse_big_int_decimal(s)?),
        JsonValue::String(s) => Value::string(s.as_str()),
        JsonValue::Set(items) => Value::set(
            items
                .iter()
                .map(json_to_value)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        JsonValue::Seq(items) => Value::seq(
            items
                .iter()
                .map(json_to_value)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        JsonValue::Tuple(items) => Value::tuple(
            items
                .iter()
                .map(json_to_value)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        JsonValue::Record(fields) => {
            let mut items: Vec<_> = fields.iter().collect();
            items.sort_unstable_by(|(ka, _), (kb, _)| ka.cmp(kb));

            Value::record(
                items
                    .into_iter()
                    .map(|(k, v)| Ok((k.as_str(), json_to_value(v)?)))
                    .collect::<Result<Vec<_>, JsonValueDecodeError>>()?,
            )
        }
        JsonValue::Function { domain, mapping } => {
            let mut domain_values: Vec<(Value, String, usize)> = domain
                .iter()
                .enumerate()
                .map(|(i, key)| Ok((json_to_value(key)?, json_key_string(key), i)))
                .collect::<Result<Vec<_>, _>>()?;
            domain_values.sort_unstable_by(|(a, _, ai), (b, _, bi)| a.cmp(b).then(ai.cmp(bi)));
            if let Some(dup) = domain_values.windows(2).find(|w| w[0].0 == w[1].0) {
                return Err(JsonValueDecodeError::DuplicateFunctionDomainKey {
                    key: dup[1].1.clone(),
                });
            }

            let mut entries: Vec<(Value, String, Value, usize)> = Vec::with_capacity(mapping.len());
            for (i, (k, v)) in mapping.iter().enumerate() {
                entries.push((json_to_value(k)?, json_key_string(k), json_to_value(v)?, i));
            }
            entries.sort_unstable_by(|(a, _, _, ai), (b, _, _, bi)| a.cmp(b).then(ai.cmp(bi)));
            if let Some(dup) = entries.windows(2).find(|w| w[0].0 == w[1].0) {
                return Err(JsonValueDecodeError::DuplicateFunctionKey {
                    key: dup[1].1.clone(),
                });
            }

            // Ensure the explicit domain list matches the mapping keys exactly.
            let mut di = 0usize;
            let mut mi = 0usize;
            while di < domain_values.len() && mi < entries.len() {
                match domain_values[di].0.cmp(&entries[mi].0) {
                    std::cmp::Ordering::Equal => {
                        di += 1;
                        mi += 1;
                    }
                    std::cmp::Ordering::Less => {
                        return Err(JsonValueDecodeError::FunctionDomainMissingKey {
                            key: domain_values[di].1.clone(),
                        });
                    }
                    std::cmp::Ordering::Greater => {
                        return Err(JsonValueDecodeError::FunctionMappingKeyNotInDomain {
                            key: entries[mi].1.clone(),
                        });
                    }
                }
            }
            if di < domain_values.len() {
                return Err(JsonValueDecodeError::FunctionDomainMissingKey {
                    key: domain_values[di].1.clone(),
                });
            }
            if mi < entries.len() {
                return Err(JsonValueDecodeError::FunctionMappingKeyNotInDomain {
                    key: entries[mi].1.clone(),
                });
            }

            let entries: Vec<(Value, Value)> =
                entries.into_iter().map(|(k, _, v, _)| (k, v)).collect();
            Value::Func(Arc::new(FuncValue::from_sorted_entries(entries)))
        }
        JsonValue::ModelValue(name) => Value::try_model_value(name)
            .map_err(|e| JsonValueDecodeError::ModelValueError(format!("{name:?}: {e}")))?,
        JsonValue::Interval { lo, hi } => Value::Interval(Arc::new(IntervalValue::new(
            parse_big_int_decimal(lo)?,
            parse_big_int_decimal(hi)?,
        ))),
        JsonValue::Undefined => return Err(JsonValueDecodeError::Undefined),
    })
}

pub fn json_to_value_with_path(value: &JsonValue) -> Result<Value, JsonValueDecodeErrorAtPath> {
    let path = PathBuilder::root();
    json_to_value_inner(value, &path)
}

struct PathBuilder {
    buf: RefCell<String>,
}

#[must_use]
struct PathGuard<'a> {
    builder: &'a PathBuilder,
    prev_len: usize,
}

impl Drop for PathGuard<'_> {
    fn drop(&mut self) {
        self.builder.buf.borrow_mut().truncate(self.prev_len);
    }
}

impl PathBuilder {
    fn root() -> Self {
        Self {
            buf: RefCell::new("$".to_string()),
        }
    }

    fn path_string(&self) -> String {
        self.buf.borrow().clone()
    }

    fn error(&self, source: JsonValueDecodeError) -> JsonValueDecodeErrorAtPath {
        JsonValueDecodeErrorAtPath {
            path: self.buf.borrow().clone(),
            source,
        }
    }

    fn push_dot(&self, segment: &str) -> PathGuard<'_> {
        let mut buf = self.buf.borrow_mut();
        let prev_len = buf.len();
        buf.push('.');
        buf.push_str(segment);
        PathGuard {
            builder: self,
            prev_len,
        }
    }

    fn push_value(&self) -> PathGuard<'_> {
        self.push_dot("value")
    }

    fn push_index(&self, index: usize) -> PathGuard<'_> {
        use std::fmt::Write;
        let mut buf = self.buf.borrow_mut();
        let prev_len = buf.len();
        buf.push('[');
        write!(buf, "{index}").expect("invariant: String fmt::Write is infallible");
        buf.push(']');
        PathGuard {
            builder: self,
            prev_len,
        }
    }

    fn push_record_key(&self, key: &str) -> PathGuard<'_> {
        let mut buf = self.buf.borrow_mut();
        let prev_len = buf.len();
        append_json_path_key(&mut buf, key);
        PathGuard {
            builder: self,
            prev_len,
        }
    }
}

fn json_to_value_inner(
    value: &JsonValue,
    path: &PathBuilder,
) -> Result<Value, JsonValueDecodeErrorAtPath> {
    Ok(match value {
        JsonValue::Bool(b) => Value::bool(*b),
        JsonValue::Int(n) => Value::int(*n),
        JsonValue::BigInt(s) => {
            let _g = path.push_value();
            Value::big_int(parse_big_int_decimal(s).map_err(|e| path.error(e))?)
        }
        JsonValue::String(s) => Value::string(s.as_str()),
        JsonValue::Set(items) => {
            let _g = path.push_value();
            let mut decoded = Vec::with_capacity(items.len());
            for (i, item) in items.iter().enumerate() {
                let _i = path.push_index(i);
                decoded.push(json_to_value_inner(item, path)?);
            }
            Value::set(decoded)
        }
        JsonValue::Seq(items) => {
            let _g = path.push_value();
            let mut decoded = Vec::with_capacity(items.len());
            for (i, item) in items.iter().enumerate() {
                let _i = path.push_index(i);
                decoded.push(json_to_value_inner(item, path)?);
            }
            Value::seq(decoded)
        }
        JsonValue::Tuple(items) => {
            let _g = path.push_value();
            let mut decoded = Vec::with_capacity(items.len());
            for (i, item) in items.iter().enumerate() {
                let _i = path.push_index(i);
                decoded.push(json_to_value_inner(item, path)?);
            }
            Value::tuple(decoded)
        }
        JsonValue::Record(fields) => {
            let _g = path.push_value();
            let mut decoded = Vec::with_capacity(fields.len());
            let mut items: Vec<_> = fields.iter().collect();
            items.sort_unstable_by(|(ka, _), (kb, _)| ka.cmp(kb));

            for (k, v) in items {
                let _k = path.push_record_key(k.as_str());
                decoded.push((k.as_str(), json_to_value_inner(v, path)?));
            }
            Value::record(decoded)
        }
        JsonValue::Function { domain, mapping } => {
            let _g = path.push_value();

            let mut domain_values: Vec<(Value, String, usize)> = Vec::with_capacity(domain.len());
            {
                let _dom = path.push_dot("domain");
                for (i, key) in domain.iter().enumerate() {
                    let _i = path.push_index(i);
                    domain_values.push((json_to_value_inner(key, path)?, json_key_string(key), i));
                }
            }
            domain_values.sort_unstable_by(|(a, _, ai), (b, _, bi)| a.cmp(b).then(ai.cmp(bi)));
            if let Some(dup) = domain_values.windows(2).find(|w| w[0].0 == w[1].0) {
                let dup_idx = dup[1].2;
                let dup_key = dup[1].1.clone();
                return Err(JsonValueDecodeErrorAtPath {
                    path: format!("{}.domain[{dup_idx}]", path.path_string()),
                    source: JsonValueDecodeError::DuplicateFunctionDomainKey { key: dup_key },
                });
            }

            let mut entries: Vec<(Value, String, Value, usize)> = Vec::with_capacity(mapping.len());
            {
                let _map = path.push_dot("mapping");
                for (i, (k, v)) in mapping.iter().enumerate() {
                    let _i = path.push_index(i);

                    let key_value = {
                        let _k = path.push_index(0);
                        json_to_value_inner(k, path)?
                    };
                    let key_string = json_key_string(k);
                    let value_value = {
                        let _v = path.push_index(1);
                        json_to_value_inner(v, path)?
                    };
                    entries.push((key_value, key_string, value_value, i));
                }
            }
            entries.sort_unstable_by(|(a, _, _, ai), (b, _, _, bi)| a.cmp(b).then(ai.cmp(bi)));
            if let Some(dup) = entries.windows(2).find(|w| w[0].0 == w[1].0) {
                let dup_idx = dup[1].3;
                let dup_key = dup[1].1.clone();
                return Err(JsonValueDecodeErrorAtPath {
                    path: format!("{}.mapping[{dup_idx}][0]", path.path_string()),
                    source: JsonValueDecodeError::DuplicateFunctionKey { key: dup_key },
                });
            }

            let mut di = 0usize;
            let mut mi = 0usize;
            while di < domain_values.len() && mi < entries.len() {
                match domain_values[di].0.cmp(&entries[mi].0) {
                    std::cmp::Ordering::Equal => {
                        di += 1;
                        mi += 1;
                    }
                    std::cmp::Ordering::Less => {
                        let (_, key_str, orig_idx) = &domain_values[di];
                        return Err(JsonValueDecodeErrorAtPath {
                            path: format!("{}.domain[{orig_idx}]", path.path_string()),
                            source: JsonValueDecodeError::FunctionDomainMissingKey {
                                key: key_str.clone(),
                            },
                        });
                    }
                    std::cmp::Ordering::Greater => {
                        let (_, key_str, _, orig_idx) = &entries[mi];
                        return Err(JsonValueDecodeErrorAtPath {
                            path: format!("{}.mapping[{orig_idx}][0]", path.path_string()),
                            source: JsonValueDecodeError::FunctionMappingKeyNotInDomain {
                                key: key_str.clone(),
                            },
                        });
                    }
                }
            }
            if di < domain_values.len() {
                let (_, key_str, orig_idx) = &domain_values[di];
                return Err(JsonValueDecodeErrorAtPath {
                    path: format!("{}.domain[{orig_idx}]", path.path_string()),
                    source: JsonValueDecodeError::FunctionDomainMissingKey {
                        key: key_str.clone(),
                    },
                });
            }
            if mi < entries.len() {
                let (_, key_str, _, orig_idx) = &entries[mi];
                return Err(JsonValueDecodeErrorAtPath {
                    path: format!("{}.mapping[{orig_idx}][0]", path.path_string()),
                    source: JsonValueDecodeError::FunctionMappingKeyNotInDomain {
                        key: key_str.clone(),
                    },
                });
            }

            let entries: Vec<(Value, Value)> =
                entries.into_iter().map(|(k, _, v, _)| (k, v)).collect();
            Value::Func(Arc::new(FuncValue::from_sorted_entries(entries)))
        }
        JsonValue::ModelValue(name) => {
            let _g = path.push_value();
            Value::try_model_value(name).map_err(|e| {
                path.error(JsonValueDecodeError::ModelValueError(format!(
                    "{name:?}: {e}"
                )))
            })?
        }
        JsonValue::Interval { lo, hi } => {
            let _g = path.push_value();
            let low = {
                let _lo = path.push_dot("lo");
                parse_big_int_decimal(lo).map_err(|e| path.error(e))?
            };
            let high = {
                let _hi = path.push_dot("hi");
                parse_big_int_decimal(hi).map_err(|e| path.error(e))?
            };
            Value::Interval(Arc::new(IntervalValue::new(low, high)))
        }
        JsonValue::Undefined => {
            let _g = path.push_dot("type");
            return Err(path.error(JsonValueDecodeError::Undefined));
        }
    })
}
