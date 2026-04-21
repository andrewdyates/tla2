// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{EvalError, EvalResult, FuncValue, Value};
use crate::value::intern_string;
use num_traits::ToPrimitive;
use std::sync::Arc;
use tla_core::Span;
// === SVG conversion helpers ===

/// Convert an SVG element record to its string representation
/// SVG elements are records with fields: name, attrs, children, innerText
pub(super) fn svg_elem_to_string(elem: &Value, span: Option<Span>) -> EvalResult<String> {
    // Handle sequence of elements - concatenate their strings
    if let Some(seq) = elem.as_seq() {
        let parts: Vec<String> = seq
            .iter()
            .map(|e| svg_elem_to_string(e, span))
            .collect::<EvalResult<Vec<_>>>()?;
        return Ok(parts.join("\n"));
    }

    // Get the element as a function/record
    let func = elem.to_func_coerced().ok_or_else(|| EvalError::Internal {
        message: "SVGElemToString: element must be a record".into(),
        span,
    })?;

    // Extract fields
    let name_key = Value::String(intern_string("name"));
    let attrs_key = Value::String(intern_string("attrs"));
    let children_key = Value::String(intern_string("children"));
    let inner_text_key = Value::String(intern_string("innerText"));

    let name = func
        .apply(&name_key)
        .and_then(|v| v.as_string().map(std::string::ToString::to_string))
        .unwrap_or_default();

    let inner_text = func
        .apply(&inner_text_key)
        .and_then(|v| v.as_string().map(std::string::ToString::to_string))
        .unwrap_or_default();

    // Format attributes
    let attrs_str = if let Some(attrs) = func.apply(&attrs_key) {
        svg_attrs_to_string(attrs)?
    } else {
        String::new()
    };

    // Format children
    let children_str = if let Some(children) = func.apply(&children_key) {
        if let Some(seq) = children.as_seq() {
            let parts: Vec<String> = seq
                .iter()
                .map(|c| svg_elem_to_string(c, span))
                .collect::<EvalResult<Vec<_>>>()?;
            parts.join("")
        } else {
            String::new()
        }
    } else {
        String::new()
    };

    // Build the SVG string
    if name.is_empty() {
        // Just return inner content
        Ok(format!("{children_str}{inner_text}"))
    } else if children_str.is_empty() && inner_text.is_empty() {
        // Self-closing tag
        Ok(format!("<{name}{attrs_str} />"))
    } else {
        // Tag with content
        Ok(format!(
            "<{name}{attrs_str}>{children_str}{inner_text}</{name}>"
        ))
    }
}

/// Convert SVG attributes record to string
pub(super) fn svg_attrs_to_string(attrs: &Value) -> EvalResult<String> {
    let func = match attrs.to_func_coerced() {
        Some(f) => f,
        None => return Ok(String::new()),
    };

    let mut attr_strs: Vec<String> = Vec::new();
    for (key, val) in func.mapping_iter() {
        let key_str = key.as_string().unwrap_or_default();
        let val_str = match val {
            Value::String(s) => s.to_string(),
            Value::SmallInt(n) => n.to_string(),
            Value::Int(n) => n.to_string(),
            Value::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            _ => format!("{val}"),
        };
        attr_strs.push(format!(" {}=\"{}\"", key_str, escape_xml(&val_str)));
    }

    Ok(attr_strs.join(""))
}

/// Escape special characters for XML/SVG
pub(super) fn escape_xml(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&apos;")
}

/// Convert a TLA+ value to a string representation for SVG attributes
/// This is simpler than JSON - just converts to plain string
pub(super) fn value_to_string(val: &Value) -> String {
    match val {
        Value::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        Value::SmallInt(n) => n.to_string(),
        Value::Int(n) => n.to_string(),
        Value::String(s) => s.to_string(),
        Value::ModelValue(s) => s.to_string(),
        _ => format!("{val}"),
    }
}

/// Merge two values (records/functions) - first argument takes priority for overlapping keys
/// This mirrors the TLA+ @@ operator behavior
pub(super) fn merge_values(left: &Value, right: &Value) -> EvalResult<Value> {
    match (left, right) {
        (Value::Record(l), Value::Record(r)) => {
            // Merge records: l overrides r
            let mut merged = r.clone();
            for (k, v) in l.iter() {
                merged = merged.insert(k, v.clone());
            }
            Ok(Value::Record(merged))
        }
        (Value::Func(l), Value::Func(r)) => {
            // Merge functions: l overrides r
            // Use a BTreeMap to handle overrides and maintain sorted order
            #[allow(clippy::mutable_key_type)]
            let mut pairs: std::collections::BTreeMap<Value, Value> = r
                .mapping_iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            for (k, v) in l.mapping_iter() {
                pairs.insert(k.clone(), v.clone());
            }
            let sorted_pairs: Vec<(Value, Value)> = pairs.into_iter().collect();
            Ok(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                sorted_pairs,
            ))))
        }
        // If either is empty record, return the other
        (Value::Record(l), _) if l.is_empty() => Ok(right.clone()),
        (_, Value::Record(r)) if r.is_empty() => Ok(left.clone()),
        // TLC raises a type error for incompatible @@ operands
        _ => Err(EvalError::TypeError {
            expected: "Record or Function",
            got: left.type_name(),
            span: None,
        }),
    }
}

// === JSON conversion helpers ===

/// Convert a TLA+ value to its JSON string representation
pub(super) fn value_to_json(val: &Value) -> String {
    match val {
        Value::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        Value::SmallInt(n) => n.to_string(),
        Value::Int(n) => n.to_string(),
        Value::String(s) => format!("\"{}\"", escape_json_string(s)),
        Value::ModelValue(s) => format!("\"{}\"", escape_json_string(s)),
        Value::Seq(elems) => {
            let items: Vec<String> = elems.iter().map(value_to_json).collect();
            format!("[{}]", items.join(","))
        }
        Value::Tuple(elems) => {
            let items: Vec<String> = elems.iter().map(value_to_json).collect();
            format!("[{}]", items.join(","))
        }
        Value::Set(set) => {
            let items: Vec<String> = set.iter().map(value_to_json).collect();
            format!("[{}]", items.join(","))
        }
        Value::Record(fields) => {
            let items: Vec<String> = fields
                .iter_str()
                .map(|(k, v)| format!("\"{}\":{}", escape_json_string(&k), value_to_json(v)))
                .collect();
            format!("{{{}}}", items.join(","))
        }
        Value::Func(func) => {
            // Functions with integer domains: convert to array
            // Functions with string domains: convert to object
            let domain: Vec<_> = func.domain_iter().cloned().collect();
            let all_ints = domain.iter().all(tla_value::Value::is_int);
            let all_strings = domain.iter().all(|k| k.as_string().is_some());

            if all_strings && !domain.is_empty() {
                // Convert to JSON object
                let items: Vec<String> = func
                    .mapping_iter()
                    .map(|(k, v)| {
                        let key_str = if let Some(s) = k.as_string() {
                            s.to_string()
                        } else {
                            // Defensive fallback: all_strings should guarantee string keys.
                            format!("{k}")
                        };
                        format!("\"{}\":{}", escape_json_string(&key_str), value_to_json(v))
                    })
                    .collect();
                format!("{{{}}}", items.join(","))
            } else if all_ints && !domain.is_empty() {
                // Convert to JSON array (sorted by key) - entries are already sorted
                let items: Vec<String> =
                    func.mapping_iter().map(|(_, v)| value_to_json(v)).collect();
                format!("[{}]", items.join(","))
            } else {
                // Mixed domain: convert to array of [key, value] pairs
                let items: Vec<String> = func
                    .mapping_iter()
                    .map(|(k, v)| format!("[{},{}]", value_to_json(k), value_to_json(v)))
                    .collect();
                format!("[{}]", items.join(","))
            }
        }
        Value::IntFunc(func) => {
            // IntFunc is always integer-indexed: convert to JSON array
            let items: Vec<String> = func.values().iter().map(value_to_json).collect();
            format!("[{}]", items.join(","))
        }
        Value::Interval(interval) => {
            if let (Some(lo), Some(hi)) = (interval.low().to_i64(), interval.high().to_i64()) {
                let items: Vec<String> = (lo..=hi).map(|i| i.to_string()).collect();
                format!("[{}]", items.join(","))
            } else {
                // Large intervals: represent as object with bounds
                format!("{{\"from\":{},\"to\":{}}}", interval.low(), interval.high())
            }
        }
        Value::Subset(sv) => {
            // SUBSET S is too large; represent as special object
            format!("{{\"subset\":{}}}", value_to_json(sv.base()))
        }
        Value::FuncSet(fv) => {
            format!(
                "{{\"funcset\":{{\"domain\":{},\"codomain\":{}}}}}",
                value_to_json(fv.domain()),
                value_to_json(fv.codomain())
            )
        }
        Value::RecordSet(rv) => {
            let items: Vec<String> = rv
                .fields_iter()
                .map(|(k, v)| format!("\"{}\":{}", escape_json_string(k), value_to_json(v)))
                .collect();
            format!("{{\"recordset\":{{{}}}}}", items.join(","))
        }
        Value::TupleSet(tv) => {
            let items: Vec<String> = tv.components_iter().map(value_to_json).collect();
            format!("{{\"tupleset\":[{}]}}", items.join(","))
        }
        Value::SetCup(scv) => {
            // Lazy union - if enumerable, convert to array; otherwise represent as structure
            // Phase 1A (#3073): use to_sorted_set() to avoid OrdSet B-tree overhead
            if let Some(set) = scv.to_sorted_set() {
                let items: Vec<String> = set.iter().map(value_to_json).collect();
                format!("[{}]", items.join(","))
            } else {
                format!(
                    "{{\"setcup\":[{},{}]}}",
                    value_to_json(scv.set1()),
                    value_to_json(scv.set2())
                )
            }
        }
        Value::SetCap(scv) => {
            // Lazy intersection - if enumerable, convert to array; otherwise represent as structure
            // Phase 1A (#3073): use to_sorted_set() to avoid OrdSet B-tree overhead
            if let Some(set) = scv.to_sorted_set() {
                let items: Vec<String> = set.iter().map(value_to_json).collect();
                format!("[{}]", items.join(","))
            } else {
                format!(
                    "{{\"setcap\":[{},{}]}}",
                    value_to_json(scv.set1()),
                    value_to_json(scv.set2())
                )
            }
        }
        Value::SetDiff(sdv) => {
            // Lazy difference - if enumerable, convert to array; otherwise represent as structure
            // Phase 1A (#3073): use to_sorted_set() to avoid OrdSet B-tree overhead
            if let Some(set) = sdv.to_sorted_set() {
                let items: Vec<String> = set.iter().map(value_to_json).collect();
                format!("[{}]", items.join(","))
            } else {
                format!(
                    "{{\"setdiff\":[{},{}]}}",
                    value_to_json(sdv.set1()),
                    value_to_json(sdv.set2())
                )
            }
        }
        Value::SetPred(spv) => {
            // SetPred can't be enumerated without evaluation context
            format!(
                "{{\"setpred\":{{\"source\":{},\"id\":{}}}}}",
                value_to_json(spv.source()),
                spv.id()
            )
        }
        Value::KSubset(ksv) => {
            // KSubset - if enumerable, convert to array; otherwise represent as structure
            if let Some(set) = ksv.to_sorted_set() {
                let items: Vec<String> = set.iter().map(value_to_json).collect();
                format!("[{}]", items.join(","))
            } else {
                format!(
                    "{{\"ksubset\":{{\"base\":{},\"k\":{}}}}}",
                    value_to_json(ksv.base()),
                    ksv.k()
                )
            }
        }
        Value::BigUnion(uv) => {
            // BigUnion - if enumerable, convert to array; otherwise represent as structure
            // Phase 1A (#3073): use to_sorted_set() to avoid OrdSet B-tree overhead
            if let Some(set) = uv.to_sorted_set() {
                let items: Vec<String> = set.iter().map(value_to_json).collect();
                format!("[{}]", items.join(","))
            } else {
                format!("{{\"union\":{}}}", value_to_json(uv.set()))
            }
        }
        Value::LazyFunc(_) => "\"<lazy-function>\"".to_string(),
        Value::Closure(_) => "\"<closure>\"".to_string(),
        Value::StringSet => "\"STRING\"".to_string(),
        Value::AnySet => "\"ANY\"".to_string(),
        Value::SeqSet(_) => "\"Seq(...)\"".to_string(),
        _ => format!("\"<{}>\"", val.type_name()),
    }
}

/// Convert a TLA+ sequence/tuple value to JSON array string
pub(super) fn value_to_json_array(val: &Value) -> EvalResult<String> {
    match val {
        Value::Seq(elems) => {
            let items: Vec<String> = elems.iter().map(value_to_json).collect();
            Ok(format!("[{}]", items.join(",")))
        }
        Value::Tuple(elems) => {
            let items: Vec<String> = elems.iter().map(value_to_json).collect();
            Ok(format!("[{}]", items.join(",")))
        }
        Value::Set(set) => {
            let items: Vec<String> = set.iter().map(value_to_json).collect();
            Ok(format!("[{}]", items.join(",")))
        }
        _ => Err(EvalError::Internal {
            message: format!("ToJsonArray requires Seq/Tuple/Set, got {val:?}"),
            span: None,
        }),
    }
}

/// Convert a TLA+ record/function value to JSON object string
pub(super) fn value_to_json_object(val: &Value) -> EvalResult<String> {
    match val {
        Value::Record(fields) => {
            let items: Vec<String> = fields
                .iter_str()
                .map(|(k, v)| format!("\"{}\":{}", escape_json_string(&k), value_to_json(v)))
                .collect();
            Ok(format!("{{{}}}", items.join(",")))
        }
        Value::Func(func) => {
            // Convert function to object (keys must be strings or ints)
            let items: Vec<String> = func
                .mapping_iter()
                .map(|(k, v)| {
                    let key_str = match k {
                        Value::String(s) => s.to_string(),
                        Value::Int(n) => n.to_string(),
                        _ => format!("{k}"),
                    };
                    format!("\"{}\":{}", escape_json_string(&key_str), value_to_json(v))
                })
                .collect();
            Ok(format!("{{{}}}", items.join(",")))
        }
        _ => {
            if let Some(elements) = val.to_tuple_like_elements() {
                let items: Vec<String> = elements
                    .iter()
                    .enumerate()
                    .map(|(idx, value)| format!("\"{}\":{}", idx + 1, value_to_json(value)))
                    .collect();
                Ok(format!("{{{}}}", items.join(",")))
            } else {
                Err(EvalError::Internal {
                    message: format!("ToJsonObject requires Record/Func/Seq, got {val:?}"),
                    span: None,
                })
            }
        }
    }
}

/// Escape special characters in a JSON string
pub(super) fn escape_json_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c.is_control() => {
                use std::fmt::Write;
                let _ = write!(result, "\\u{:04x}", c as u32);
            }
            c => result.push(c),
        }
    }
    result
}
