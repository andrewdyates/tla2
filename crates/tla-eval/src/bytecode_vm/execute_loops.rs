// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop opcode handlers extracted from execute.rs (#3594).
//!
//! Owns the iterator-loop state machine: quantifier loops (Forall/Exists),
//! set builders, set filters, function-definition loops, and CHOOSE.

use std::sync::Arc;
use tla_value::error::EvalError;
use tla_value::{FuncValue, SortedSet, Value};

use super::execute::VmError;
use super::execute_helpers::as_bool;

/// Action returned by loop helpers to tell the dispatch loop what to do next.
pub(super) enum LoopAction {
    /// Fall through to `pc += 1`.
    Continue,
    /// Jump to the given absolute `pc` (caller should `continue` without incrementing).
    Jump(usize),
}

/// Iterator state for quantifier and loop opcodes.
pub(super) enum LoopState {
    Quantifier {
        elements: Vec<Value>,
        index: usize,
    },
    SetFilter {
        elements: Vec<Value>,
        index: usize,
        collected: Vec<Value>,
        rd: u8,
    },
    SetBuilder {
        elements: Vec<Value>,
        index: usize,
        collected: Vec<Value>,
        rd: u8,
    },
    FuncDef {
        elements: Vec<Value>,
        index: usize,
        entries: Vec<(Value, Value)>,
        rd: u8,
    },
    Choose {
        elements: Vec<Value>,
        index: usize,
        #[allow(dead_code)]
        rd: u8,
    },
}

pub(super) fn forall_begin(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
    loop_end: i32,
) -> Result<LoopAction, VmError> {
    let domain = &regs[r_domain as usize];
    let elements: Vec<Value> = domain
        .iter_set()
        .ok_or_else(|| VmError::TypeError {
            expected: "enumerable set for FORALL domain",
            actual: format!("{domain:?}"),
        })?
        .collect();
    if elements.is_empty() {
        regs[rd as usize] = Value::Bool(true);
        return Ok(LoopAction::Jump(((pc as i64) + (loop_end as i64)) as usize));
    }
    regs[r_binding as usize] = elements[0].clone();
    regs[rd as usize] = Value::Bool(true);
    iter_stack.push(LoopState::Quantifier { elements, index: 0 });
    Ok(LoopAction::Continue)
}

pub(super) fn forall_next(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    rd: u8,
    r_binding: u8,
    r_body: u8,
    loop_begin: i32,
) -> Result<LoopAction, VmError> {
    let body_val = as_bool(&regs[r_body as usize])?;
    if !body_val {
        regs[rd as usize] = Value::Bool(false);
        iter_stack.pop();
    } else if let Some(LoopState::Quantifier { elements, index }) = iter_stack.last_mut() {
        *index += 1;
        if *index < elements.len() {
            regs[r_binding as usize] = elements[*index].clone();
            return Ok(LoopAction::Jump(
                ((pc as i64) + (loop_begin as i64)) as usize,
            ));
        } else {
            regs[rd as usize] = Value::Bool(true);
            iter_stack.pop();
        }
    } else {
        return Err(VmError::Unsupported(
            "ForallNext without matching ForallBegin".to_string(),
        ));
    }
    Ok(LoopAction::Continue)
}

pub(super) fn exists_begin(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
    loop_end: i32,
) -> Result<LoopAction, VmError> {
    let domain = &regs[r_domain as usize];
    let elements: Vec<Value> = domain
        .iter_set()
        .ok_or_else(|| VmError::TypeError {
            expected: "enumerable set for EXISTS domain",
            actual: format!("{domain:?}"),
        })?
        .collect();
    if elements.is_empty() {
        regs[rd as usize] = Value::Bool(false);
        return Ok(LoopAction::Jump(((pc as i64) + (loop_end as i64)) as usize));
    }
    regs[r_binding as usize] = elements[0].clone();
    regs[rd as usize] = Value::Bool(false);
    iter_stack.push(LoopState::Quantifier { elements, index: 0 });
    Ok(LoopAction::Continue)
}

pub(super) fn exists_next(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    rd: u8,
    r_binding: u8,
    r_body: u8,
    loop_begin: i32,
) -> Result<LoopAction, VmError> {
    let body_val = as_bool(&regs[r_body as usize])?;
    if body_val {
        regs[rd as usize] = Value::Bool(true);
        iter_stack.pop();
    } else if let Some(LoopState::Quantifier { elements, index }) = iter_stack.last_mut() {
        *index += 1;
        if *index < elements.len() {
            regs[r_binding as usize] = elements[*index].clone();
            return Ok(LoopAction::Jump(
                ((pc as i64) + (loop_begin as i64)) as usize,
            ));
        } else {
            regs[rd as usize] = Value::Bool(false);
            iter_stack.pop();
        }
    } else {
        return Err(VmError::Unsupported(
            "ExistsNext without matching ExistsBegin".to_string(),
        ));
    }
    Ok(LoopAction::Continue)
}

pub(super) fn set_filter_begin(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
    loop_end: i32,
) -> Result<LoopAction, VmError> {
    let domain = &regs[r_domain as usize];
    let elements: Vec<Value> = domain
        .iter_set()
        .ok_or_else(|| VmError::TypeError {
            expected: "enumerable set for set filter",
            actual: format!("{domain:?}"),
        })?
        .collect();
    if elements.is_empty() {
        regs[rd as usize] = Value::empty_set();
        return Ok(LoopAction::Jump(((pc as i64) + (loop_end as i64)) as usize));
    }
    regs[r_binding as usize] = elements[0].clone();
    iter_stack.push(LoopState::SetFilter {
        elements,
        index: 0,
        collected: Vec::new(),
        rd,
    });
    Ok(LoopAction::Continue)
}

pub(super) fn set_builder_begin(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
    loop_end: i32,
) -> Result<LoopAction, VmError> {
    let domain = &regs[r_domain as usize];
    let elements: Vec<Value> = domain
        .iter_set()
        .ok_or_else(|| VmError::TypeError {
            expected: "enumerable set for set builder",
            actual: format!("{domain:?}"),
        })?
        .collect();
    if elements.is_empty() {
        regs[rd as usize] = Value::empty_set();
        return Ok(LoopAction::Jump(((pc as i64) + (loop_end as i64)) as usize));
    }
    regs[r_binding as usize] = elements[0].clone();
    iter_stack.push(LoopState::SetBuilder {
        elements,
        index: 0,
        collected: Vec::new(),
        rd,
    });
    Ok(LoopAction::Continue)
}

pub(super) fn func_def_begin(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
    loop_end: i32,
) -> Result<LoopAction, VmError> {
    let domain = &regs[r_domain as usize];
    let elements: Vec<Value> = domain
        .iter_set()
        .ok_or_else(|| VmError::TypeError {
            expected: "enumerable set for function definition",
            actual: format!("{domain:?}"),
        })?
        .collect();
    if elements.is_empty() {
        regs[rd as usize] = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![])));
        return Ok(LoopAction::Jump(((pc as i64) + (loop_end as i64)) as usize));
    }
    regs[r_binding as usize] = elements[0].clone();
    iter_stack.push(LoopState::FuncDef {
        elements,
        index: 0,
        entries: Vec::new(),
        rd,
    });
    Ok(LoopAction::Continue)
}

pub(super) fn loop_next(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    r_binding: u8,
    r_body: u8,
    loop_begin: i32,
) -> Result<LoopAction, VmError> {
    match iter_stack.last_mut() {
        Some(LoopState::SetFilter {
            elements,
            index,
            collected,
            rd,
        }) => {
            if as_bool(&regs[r_body as usize])? {
                collected.push(elements[*index].clone());
            }
            *index += 1;
            if *index < elements.len() {
                regs[r_binding as usize] = elements[*index].clone();
                return Ok(LoopAction::Jump(
                    ((pc as i64) + (loop_begin as i64)) as usize,
                ));
            } else {
                let rd_idx = *rd;
                let result = std::mem::take(collected);
                iter_stack.pop();
                regs[rd_idx as usize] = Value::Set(Arc::new(SortedSet::from_iter(result)));
            }
        }
        Some(LoopState::SetBuilder {
            elements,
            index,
            collected,
            rd,
        }) => {
            collected.push(regs[r_body as usize].clone());
            *index += 1;
            if *index < elements.len() {
                regs[r_binding as usize] = elements[*index].clone();
                return Ok(LoopAction::Jump(
                    ((pc as i64) + (loop_begin as i64)) as usize,
                ));
            } else {
                let rd_idx = *rd;
                let result = std::mem::take(collected);
                iter_stack.pop();
                regs[rd_idx as usize] = Value::Set(Arc::new(SortedSet::from_iter(result)));
            }
        }
        Some(LoopState::FuncDef {
            elements,
            index,
            entries,
            rd,
        }) => {
            let key = elements[*index].clone();
            let val = regs[r_body as usize].clone();
            entries.push((key, val));
            *index += 1;
            if *index < elements.len() {
                regs[r_binding as usize] = elements[*index].clone();
                return Ok(LoopAction::Jump(
                    ((pc as i64) + (loop_begin as i64)) as usize,
                ));
            } else {
                let rd_idx = *rd;
                let result = std::mem::take(entries);
                iter_stack.pop();
                regs[rd_idx as usize] =
                    Value::Func(Arc::new(FuncValue::from_sorted_entries(result)));
            }
        }
        _ => {
            return Err(VmError::Unsupported(
                "LoopNext without matching loop begin".to_string(),
            ));
        }
    }
    Ok(LoopAction::Continue)
}

pub(super) fn choose_begin(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    _pc: usize,
    rd: u8,
    r_binding: u8,
    r_domain: u8,
) -> Result<LoopAction, VmError> {
    let domain = &regs[r_domain as usize];
    if !domain.is_set() {
        return Err(VmError::TypeError {
            expected: "set for CHOOSE domain",
            actual: format!("{domain:?}"),
        });
    }
    let elements: Vec<Value> = match domain.iter_set_tlc_normalized() {
        Ok(iter) => iter.collect(),
        Err(EvalError::SetTooLarge { .. }) => {
            return Err(VmError::Unsupported(
                "CHOOSE domain requires tree-walk iteration".to_string(),
            ));
        }
        Err(err) => return Err(VmError::Eval(err)),
    };
    if elements.is_empty() {
        return Err(VmError::ChooseFailed);
    }
    regs[r_binding as usize] = elements[0].clone();
    regs[rd as usize] = Value::Bool(false);
    iter_stack.push(LoopState::Choose {
        elements,
        index: 0,
        rd,
    });
    Ok(LoopAction::Continue)
}

pub(super) fn choose_next(
    regs: &mut [Value],
    iter_stack: &mut Vec<LoopState>,
    pc: usize,
    rd: u8,
    r_binding: u8,
    r_body: u8,
    loop_begin: i32,
) -> Result<LoopAction, VmError> {
    let body_val = as_bool(&regs[r_body as usize])?;
    if body_val {
        regs[rd as usize] = regs[r_binding as usize].clone();
        iter_stack.pop();
    } else if let Some(LoopState::Choose {
        elements, index, ..
    }) = iter_stack.last_mut()
    {
        *index += 1;
        if *index < elements.len() {
            regs[r_binding as usize] = elements[*index].clone();
            return Ok(LoopAction::Jump(
                ((pc as i64) + (loop_begin as i64)) as usize,
            ));
        } else {
            iter_stack.pop();
            return Err(VmError::ChooseFailed);
        }
    } else {
        return Err(VmError::Unsupported(
            "ChooseNext without matching ChooseBegin".to_string(),
        ));
    }
    Ok(LoopAction::Continue)
}
