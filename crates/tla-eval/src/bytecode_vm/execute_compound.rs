// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode VM compound-value opcode handlers.
//!
//! Owns set operations, records, function operations, tuples, sequences,
//! strings, and cross-product types. Extracted from `execute.rs` per #3611.

use std::sync::Arc;
use tla_tir::bytecode::{BuiltinOp, ConstantPool, Opcode};
use tla_value::{RecordValue, SortedSet, Value};

use super::execute::{BytecodeVm, VmError};
use super::execute_helpers::{func_apply, to_bigint, to_sorted_set, value_domain, value_except};

impl<'a> BytecodeVm<'a> {
    pub(super) fn execute_compound_opcode(
        &mut self,
        opcode: &Opcode,
        constants: &ConstantPool,
        regs: &mut [Value],
    ) -> Result<(), VmError> {
        match opcode {
            // === Set Operations ===
            Opcode::SetEnum { rd, start, count } => {
                let elements: Vec<Value> = (0..*count as usize)
                    .map(|i| regs[*start as usize + i].clone())
                    .collect();
                regs[*rd as usize] = Value::Set(Arc::new(SortedSet::from_iter(elements)));
            }
            Opcode::SetIn { rd, elem, set } => {
                let e = &regs[*elem as usize];
                let s = &regs[*set as usize];
                match s.set_contains(e) {
                    Some(b) => regs[*rd as usize] = Value::Bool(b),
                    None => {
                        return Err(VmError::TypeError {
                            expected: "enumerable set for \\in",
                            actual: format!("{s:?}"),
                        });
                    }
                }
            }
            Opcode::SetUnion { rd, r1, r2 } => {
                let a = to_sorted_set(&regs[*r1 as usize])?;
                let b = to_sorted_set(&regs[*r2 as usize])?;
                regs[*rd as usize] = Value::Set(Arc::new(a.union(&b)));
            }
            Opcode::SetIntersect { rd, r1, r2 } => {
                let a = to_sorted_set(&regs[*r1 as usize])?;
                let b = to_sorted_set(&regs[*r2 as usize])?;
                regs[*rd as usize] = Value::Set(Arc::new(a.intersection(&b)));
            }
            Opcode::SetDiff { rd, r1, r2 } => {
                let a = to_sorted_set(&regs[*r1 as usize])?;
                let b = to_sorted_set(&regs[*r2 as usize])?;
                regs[*rd as usize] = Value::Set(Arc::new(a.difference(&b)));
            }
            Opcode::Subseteq { rd, r1, r2 } => {
                let a = to_sorted_set(&regs[*r1 as usize])?;
                let b = to_sorted_set(&regs[*r2 as usize])?;
                regs[*rd as usize] = Value::Bool(a.is_subset(&b));
            }
            Opcode::Powerset { rd, rs } => {
                let s = to_sorted_set(&regs[*rs as usize])?;
                regs[*rd as usize] = tla_value::powerset(&s).map_err(VmError::Eval)?;
            }
            Opcode::KSubset { rd, base, k } => {
                let base_val = &regs[*base as usize];
                if !base_val.is_set() {
                    return Err(VmError::TypeError {
                        expected: "set for KSubset base",
                        actual: format!("{base_val:?}"),
                    });
                }
                let k_val = to_bigint(&regs[*k as usize])?;
                use num_traits::ToPrimitive;
                let k_usize = k_val.to_usize().ok_or_else(|| VmError::TypeError {
                    expected: "non-negative integer for KSubset k",
                    actual: format!("{k_val}"),
                })?;
                regs[*rd as usize] =
                    Value::KSubset(tla_value::KSubsetValue::new(base_val.clone(), k_usize));
            }
            Opcode::BigUnion { rd, rs } => {
                let outer = to_sorted_set(&regs[*rs as usize])?;
                let mut result = SortedSet::new();
                for elem in outer.iter() {
                    let inner = elem.to_sorted_set().ok_or_else(|| VmError::TypeError {
                        expected: "set element in UNION",
                        actual: format!("{elem:?}"),
                    })?;
                    result = result.union(&inner);
                }
                regs[*rd as usize] = Value::Set(Arc::new(result));
            }
            Opcode::Range { rd, lo, hi } => {
                let lo_val = to_bigint(&regs[*lo as usize])?;
                let hi_val = to_bigint(&regs[*hi as usize])?;
                regs[*rd as usize] = tla_value::range_set(&lo_val, &hi_val);
            }

            // === Records ===
            Opcode::RecordNew {
                rd,
                fields_start,
                values_start,
                count,
            } => {
                let mut entries = Vec::with_capacity(*count as usize);
                for i in 0..*count as usize {
                    let field_name = constants.get_value(*fields_start + i as u16);
                    let value = regs[*values_start as usize + i].clone();
                    let name_str = match field_name {
                        Value::String(s) => s.as_ref(),
                        _ => {
                            return Err(VmError::TypeError {
                                expected: "string field name in record",
                                actual: format!("{field_name:?}"),
                            });
                        }
                    };
                    entries.push((tla_core::intern_name(name_str), value));
                }
                entries.sort_by_key(|(k, _)| *k);
                regs[*rd as usize] = Value::Record(RecordValue::from_sorted_entries(entries));
            }
            Opcode::RecordGet { rd, rs, field_idx } => {
                let field_id = tla_core::NameId(constants.get_field_id(*field_idx));
                match &regs[*rs as usize] {
                    Value::Record(rec) => match rec.get_by_id(field_id) {
                        Some(v) => regs[*rd as usize] = v.clone(),
                        None => {
                            return Err(VmError::TypeError {
                                expected: "record field exists",
                                actual: format!(
                                    "field {:?} not found",
                                    tla_core::resolve_name_id(field_id)
                                ),
                            });
                        }
                    },
                    other => {
                        return Err(VmError::TypeError {
                            expected: "record",
                            actual: format!("{other:?}"),
                        });
                    }
                }
            }

            // === Function Operations ===
            Opcode::FuncApply { rd, func, arg } => {
                let f = &regs[*func as usize];
                let a = &regs[*arg as usize];
                regs[*rd as usize] = func_apply(f, a)?;
            }
            Opcode::Domain { rd, rs } => {
                regs[*rd as usize] = value_domain(&regs[*rs as usize])?;
            }
            Opcode::FuncExcept {
                rd,
                func,
                path,
                val,
            } => {
                let f = regs[*func as usize].clone();
                let p = regs[*path as usize].clone();
                let v = regs[*val as usize].clone();
                regs[*rd as usize] = value_except(f, p, v)?;
            }

            // === Tuples ===
            Opcode::TupleNew { rd, start, count } => {
                let elements: Vec<Value> = (0..*count as usize)
                    .map(|i| regs[*start as usize + i].clone())
                    .collect();
                regs[*rd as usize] = Value::Tuple(elements.into());
            }
            Opcode::TupleGet { rd, rs, idx } => match &regs[*rs as usize] {
                Value::Tuple(elems) => {
                    let i = *idx as usize;
                    if i >= 1 && i <= elems.len() {
                        regs[*rd as usize] = elems[i - 1].clone();
                    } else {
                        return Err(VmError::TypeError {
                            expected: "valid tuple index",
                            actual: format!("index {i} out of bounds (len {})", elems.len()),
                        });
                    }
                }
                other => {
                    return Err(VmError::TypeError {
                        expected: "tuple",
                        actual: format!("{other:?}"),
                    });
                }
            },

            // === Sequences ===
            Opcode::SeqNew { rd, start, count } => {
                let elements: Vec<Value> = (0..*count as usize)
                    .map(|i| regs[*start as usize + i].clone())
                    .collect();
                regs[*rd as usize] = Value::seq(elements);
            }

            // === String ===
            Opcode::StrConcat { rd, r1, r2 } => match (&regs[*r1 as usize], &regs[*r2 as usize]) {
                (Value::String(a), Value::String(b)) => {
                    let mut s = a.to_string();
                    s.push_str(b);
                    regs[*rd as usize] = Value::string(s);
                }
                (a, b) => {
                    return Err(VmError::TypeError {
                        expected: "strings for concatenation",
                        actual: format!("{a:?} \\o {b:?}"),
                    });
                }
            },

            // === Not yet implemented / cross-product types ===
            Opcode::FuncDef { .. } => {
                return Err(VmError::Unsupported(
                    "FuncDef (non-loop variant)".to_string(),
                ));
            }
            Opcode::FuncSet { rd, domain, range } => {
                let d = regs[*domain as usize].clone();
                let r = regs[*range as usize].clone();
                regs[*rd as usize] = Value::FuncSet(tla_value::FuncSetValue::new(d, r));
            }
            Opcode::RecordSet {
                rd,
                fields_start,
                values_start,
                count,
            } => {
                let mut field_entries: Vec<(Arc<str>, Value)> = Vec::with_capacity(*count as usize);
                for i in 0..*count as usize {
                    let field_name = constants.get_value(*fields_start + i as u16);
                    let field_set = regs[*values_start as usize + i].clone();
                    let name_str: Arc<str> = match field_name {
                        Value::String(s) => s.clone(),
                        _ => {
                            return Err(VmError::TypeError {
                                expected: "string field name",
                                actual: format!("{field_name:?}"),
                            });
                        }
                    };
                    field_entries.push((name_str, field_set));
                }
                regs[*rd as usize] = Value::record_set(field_entries);
            }
            Opcode::Times { rd, start, count } => {
                let components: Vec<Value> = (0..*count as usize)
                    .map(|i| regs[*start as usize + i].clone())
                    .collect();
                regs[*rd as usize] = Value::tuple_set(components);
            }

            // === Closures ===
            Opcode::MakeClosure {
                rd,
                template_idx,
                captures_start,
                capture_count,
            } => {
                let template = constants.get_value(*template_idx);
                let closure_arc = match template {
                    Value::Closure(c) => c,
                    _ => {
                        return Err(VmError::TypeError {
                            expected: "closure template in MakeClosure",
                            actual: format!("{template:?}"),
                        });
                    }
                };
                // Build captured environment from consecutive constant-pool names
                // and consecutive register values.
                let mut env = tla_core::kani_types::HashMap::new();
                for i in 0..*capture_count as usize {
                    let name_val = constants.get_value(*template_idx + 1 + i as u16);
                    let name: Arc<str> = match name_val {
                        Value::String(s) => s.clone(),
                        _ => {
                            return Err(VmError::TypeError {
                                expected: "string capture name in MakeClosure",
                                actual: format!("{name_val:?}"),
                            });
                        }
                    };
                    let value = regs[*captures_start as usize + i].clone();
                    env.insert(name, value);
                }
                // Clone template and inject the captured env.
                let new_closure = closure_arc.as_ref().clone().with_env(Arc::new(env));
                regs[*rd as usize] = Value::Closure(Arc::new(new_closure));
            }

            // === Concat (polymorphic \o) ===
            Opcode::Concat { rd, r1, r2 } => {
                let v1 = &regs[*r1 as usize];
                let v2 = &regs[*r2 as usize];
                regs[*rd as usize] = execute_concat(v1, v2)?;
            }

            // === Standard-library builtin calls ===
            Opcode::CallBuiltin {
                rd,
                builtin,
                args_start,
                argc,
            } => {
                let args: &[Value] = &regs[*args_start as usize..][..*argc as usize];
                regs[*rd as usize] = execute_builtin(*builtin, args)?;
            }

            _ => unreachable!("non-compound opcode routed to execute_compound_opcode"),
        }

        Ok(())
    }
}

/// Execute the polymorphic `\o` (concat) operator on two values.
///
/// Handles string-string concatenation, sequence-sequence concatenation,
/// and sequence-like values (Tuple, IntFunc, Func with 1..n domains).
/// Part of #3789.
fn execute_concat(v1: &Value, v2: &Value) -> Result<Value, VmError> {
    // String concatenation
    if let (Value::String(s1), Value::String(s2)) = (v1, v2) {
        let mut s = s1.to_string();
        s.push_str(s2);
        return Ok(Value::String(crate::value::intern_string(&s)));
    }
    // Sequence concatenation (accept Seq, Tuple, and tuple-like Func/IntFunc)
    let s1 = v1
        .as_seq()
        .or_else(|| v1.to_tuple_like_elements())
        .ok_or_else(|| VmError::TypeError {
            expected: "sequence or string for \\o",
            actual: format!("{v1:?}"),
        })?;
    let s2 = v2
        .as_seq()
        .or_else(|| v2.to_tuple_like_elements())
        .ok_or_else(|| VmError::TypeError {
            expected: "sequence or string for \\o",
            actual: format!("{v2:?}"),
        })?;
    let mut result: Vec<Value> = Vec::with_capacity(s1.len() + s2.len());
    result.extend(s1.iter().cloned());
    result.extend(s2.iter().cloned());
    Ok(Value::Seq(Arc::new(result.into())))
}

/// Execute a standard-library builtin operator on already-evaluated arguments.
///
/// This is the value-level equivalent of `eval_builtin_sequences` /
/// `eval_builtin_finite_sets` / `eval_builtin_tlc` — but operates on `Value`
/// directly without needing `EvalCtx` or `Expr`.
/// Part of #3789: cross-module stdlib operator support in bytecode VM.
fn execute_builtin(op: BuiltinOp, args: &[Value]) -> Result<Value, VmError> {
    match op {
        BuiltinOp::Len => {
            let v = &args[0];
            match v {
                Value::Seq(s) => Ok(Value::int(s.len() as i64)),
                Value::Tuple(s) => Ok(Value::int(s.len() as i64)),
                Value::String(s) => Ok(Value::int(crate::value::tlc_string_len(s.as_ref()) as i64)),
                Value::IntFunc(f) => {
                    if tla_value::IntIntervalFunc::min(f) == 1 {
                        Ok(Value::int(f.len() as i64))
                    } else {
                        Err(VmError::TypeError {
                            expected: "sequence for Len",
                            actual: format!("{v:?}"),
                        })
                    }
                }
                Value::Func(f) => {
                    // Sequences are functions with domain 1..n
                    let mut expected: i64 = 1;
                    for key in f.domain_iter() {
                        let Some(k) = key.as_i64() else {
                            return Err(VmError::TypeError {
                                expected: "sequence for Len",
                                actual: format!("{v:?}"),
                            });
                        };
                        if k != expected {
                            return Err(VmError::TypeError {
                                expected: "sequence for Len",
                                actual: format!("{v:?}"),
                            });
                        }
                        expected += 1;
                    }
                    Ok(Value::int(expected - 1))
                }
                _ => Err(VmError::TypeError {
                    expected: "sequence for Len",
                    actual: format!("{v:?}"),
                }),
            }
        }

        BuiltinOp::Head => {
            let v = &args[0];
            let seq = v
                .as_seq()
                .or_else(|| v.to_tuple_like_elements())
                .ok_or_else(|| VmError::TypeError {
                    expected: "sequence for Head",
                    actual: format!("{v:?}"),
                })?;
            seq.first().cloned().ok_or_else(|| {
                VmError::Eval(tla_value::error::EvalError::ApplyEmptySeq {
                    op: "Head",
                    span: None,
                })
            })
        }

        BuiltinOp::Tail => {
            let v = &args[0];
            // Fast path: use O(log n) tail for SeqValue
            if let Some(seq_value) = v.as_seq_value() {
                if seq_value.is_empty() {
                    return Err(VmError::Eval(tla_value::error::EvalError::ApplyEmptySeq {
                        op: "Tail",
                        span: None,
                    }));
                }
                return Ok(Value::Seq(Arc::new(seq_value.tail())));
            }
            let seq = v
                .as_seq()
                .or_else(|| v.to_tuple_like_elements())
                .ok_or_else(|| VmError::TypeError {
                    expected: "sequence for Tail",
                    actual: format!("{v:?}"),
                })?;
            if seq.is_empty() {
                return Err(VmError::Eval(tla_value::error::EvalError::ApplyEmptySeq {
                    op: "Tail",
                    span: None,
                }));
            }
            Ok(Value::Seq(Arc::new(seq[1..].to_vec().into())))
        }

        BuiltinOp::Append => {
            let sv = &args[0];
            let elem = args[1].clone();
            if let Some(seq_value) = sv.as_seq_value() {
                return Ok(Value::Seq(Arc::new(seq_value.append(elem))));
            }
            let s = sv
                .as_seq()
                .or_else(|| sv.to_tuple_like_elements())
                .ok_or_else(|| VmError::TypeError {
                    expected: "sequence for Append",
                    actual: format!("{sv:?}"),
                })?;
            let mut v = s.to_vec();
            v.push(elem);
            Ok(Value::Seq(Arc::new(v.into())))
        }

        BuiltinOp::SubSeq => {
            let sv = &args[0];
            let m = args[1].as_i64().ok_or_else(|| VmError::TypeError {
                expected: "integer for SubSeq start",
                actual: format!("{:?}", args[1]),
            })?;
            let n = args[2].as_i64().ok_or_else(|| VmError::TypeError {
                expected: "integer for SubSeq end",
                actual: format!("{:?}", args[2]),
            })?;
            if m > n {
                return match sv {
                    Value::String(_) => Ok(Value::String(crate::value::intern_string(""))),
                    _ => Ok(Value::Seq(Arc::new(Vec::new().into()))),
                };
            }
            match sv {
                Value::String(s) => {
                    let len = crate::value::tlc_string_len(s.as_ref());
                    if m < 1 || (m as usize) > len || n < 1 || (n as usize) > len {
                        return Err(VmError::Eval(
                            tla_value::error::EvalError::IndexOutOfBounds {
                                index: if m < 1 || (m as usize) > len { m } else { n },
                                len,
                                value_display: None,
                                span: None,
                            },
                        ));
                    }
                    let start_off = (m - 1) as usize;
                    let end_off = n as usize;
                    let substr = crate::value::tlc_string_subseq_utf16_offsets(
                        s.as_ref(),
                        start_off..end_off,
                    );
                    Ok(Value::String(crate::value::intern_string(substr.as_ref())))
                }
                Value::Seq(seq_value) => {
                    let len = seq_value.len();
                    if m < 1 || (m as usize) > len || n < 1 || (n as usize) > len {
                        return Err(VmError::Eval(
                            tla_value::error::EvalError::IndexOutOfBounds {
                                index: if m < 1 || (m as usize) > len { m } else { n },
                                len,
                                value_display: None,
                                span: None,
                            },
                        ));
                    }
                    let start = (m - 1) as usize;
                    let end = n as usize;
                    Ok(Value::Seq(Arc::new(seq_value.subseq(start, end))))
                }
                Value::Tuple(seq) => {
                    let len = seq.len();
                    if m < 1 || (m as usize) > len || n < 1 || (n as usize) > len {
                        return Err(VmError::Eval(
                            tla_value::error::EvalError::IndexOutOfBounds {
                                index: if m < 1 || (m as usize) > len { m } else { n },
                                len,
                                value_display: None,
                                span: None,
                            },
                        ));
                    }
                    let start = (m - 1) as usize;
                    let end = n as usize;
                    Ok(Value::Seq(Arc::new(seq[start..end].to_vec().into())))
                }
                _ => Err(VmError::TypeError {
                    expected: "sequence or string for SubSeq",
                    actual: format!("{sv:?}"),
                }),
            }
        }

        BuiltinOp::Seq => {
            // Seq(S) = set of all finite sequences over S
            let base = args[0].clone();
            Ok(Value::SeqSet(tla_value::SeqSetValue::new(base)))
        }

        BuiltinOp::Cardinality => {
            let v = &args[0];
            match v.set_len() {
                Some(n) => Ok(Value::big_int(n)),
                None if v.is_set() => Err(VmError::Unsupported(
                    "Cardinality not supported for this set value".to_string(),
                )),
                None => Err(VmError::TypeError {
                    expected: "set for Cardinality",
                    actual: format!("{v:?}"),
                }),
            }
        }

        BuiltinOp::IsFiniteSet => {
            let v = &args[0];
            Ok(Value::Bool(v.is_finite_set()))
        }

        BuiltinOp::FoldFunctionOnSetSum => {
            if args.len() != 2 {
                return Err(VmError::TypeError {
                    expected: "function and set for FoldFunctionOnSet(+, 0, f, S)",
                    actual: format!("{} arguments", args.len()),
                });
            }
            let f = &args[0];
            let s = &args[1];
            let mut sum = num_bigint::BigInt::from(0);
            let iter = s.iter_set().ok_or_else(|| VmError::TypeError {
                expected: "finite set for FoldFunctionOnSet(+, 0, f, S)",
                actual: format!("{s:?}"),
            })?;
            for elem in iter {
                let value = func_apply(f, &elem)?;
                sum += to_bigint(&value)?;
            }
            Ok(Value::big_int(sum))
        }

        BuiltinOp::ToString => {
            let v = &args[0];
            Ok(Value::String(crate::value::intern_string(&format!("{v}"))))
        }
    }
}
