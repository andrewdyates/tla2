// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode VM scalar/control opcode handlers.
//!
//! Owns value loading, integer arithmetic, comparisons, booleans,
//! control flow, and special opcodes. Extracted from `execute.rs` per #3611.

use num_bigint::BigInt;
use num_traits::Signed;
use tla_tir::bytecode::{ConstantPool, Opcode};
use tla_value::Value;

use super::execute::{BytecodeVm, VmError};
use super::execute_dispatch::DispatchOutcome;
use super::execute_helpers::{
    as_bool, call_external, enter_vm_call, exit_vm_call, int_arith, int_cmp, int_div, int_pow,
    load_prime_var, load_state_var, value_apply,
};

impl<'a> BytecodeVm<'a> {
    pub(super) fn execute_scalar_opcode(
        &mut self,
        opcode: &Opcode,
        constants: &ConstantPool,
        regs: &mut [Value],
        pc: usize,
    ) -> Result<DispatchOutcome, VmError> {
        match opcode {
            // === Value Loading ===
            Opcode::LoadImm { rd, value } => {
                regs[*rd as usize] = Value::SmallInt(*value);
            }
            Opcode::LoadBool { rd, value } => {
                regs[*rd as usize] = Value::Bool(*value);
            }
            Opcode::LoadConst { rd, idx } => {
                regs[*rd as usize] = constants.get_value(*idx).clone();
            }
            Opcode::LoadVar { rd, var_idx } => {
                regs[*rd as usize] = if self.prime_mode {
                    load_prime_var(self.next_state, self.next_state_cache.as_mut(), *var_idx)?
                } else {
                    load_state_var(self.state, &mut self.state_cache, *var_idx)?
                };
            }
            Opcode::LoadPrime { rd, var_idx } => {
                regs[*rd as usize] =
                    load_prime_var(self.next_state, self.next_state_cache.as_mut(), *var_idx)?;
            }
            Opcode::StoreVar { .. } => {
                return Err(VmError::Unsupported(
                    "StoreVar (invariant-only path)".to_string(),
                ));
            }
            Opcode::Move { rd, rs } => {
                regs[*rd as usize] = regs[*rs as usize].clone();
            }

            // === Integer Arithmetic ===
            Opcode::AddInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_arith(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| a.checked_add(b),
                    |a, b| a + b,
                )?;
            }
            Opcode::SubInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_arith(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| a.checked_sub(b),
                    |a, b| a - b,
                )?;
            }
            Opcode::MulInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_arith(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| a.checked_mul(b),
                    |a, b| a * b,
                )?;
            }
            Opcode::DivInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_div(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| a.checked_div(b),
                    |a, b| a / b,
                )?;
            }
            Opcode::IntDiv { rd, r1, r2 } => {
                regs[*rd as usize] = int_div(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| {
                        if b == 0 {
                            return None;
                        }
                        let q = a / b;
                        if (a ^ b) < 0 && a % b != 0 {
                            Some(q - 1)
                        } else {
                            Some(q)
                        }
                    },
                    |a, b| {
                        let q = &a / &b;
                        if (a.sign() != b.sign()) && (&a % &b) != BigInt::from(0) {
                            q - 1
                        } else {
                            q
                        }
                    },
                )?;
            }
            Opcode::ModInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_div(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| {
                        if b == 0 {
                            return None;
                        }
                        let r = a % b;
                        Some(if r < 0 { r + b.abs() } else { r })
                    },
                    |a, b| {
                        let r = &a % &b;
                        if r < BigInt::from(0) {
                            r + b.abs()
                        } else {
                            r
                        }
                    },
                )?;
            }
            Opcode::NegInt { rd, rs } => {
                regs[*rd as usize] = match &regs[*rs as usize] {
                    Value::SmallInt(n) => match n.checked_neg() {
                        Some(neg) => Value::SmallInt(neg),
                        None => Value::big_int(-BigInt::from(*n)),
                    },
                    Value::Int(n) => Value::big_int(-n.as_ref().clone()),
                    other => {
                        return Err(VmError::TypeError {
                            expected: "integer",
                            actual: format!("{other:?}"),
                        });
                    }
                };
            }
            Opcode::PowInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_pow(&regs[*r1 as usize], &regs[*r2 as usize])?;
            }

            // === Comparison ===
            Opcode::Eq { rd, r1, r2 } => {
                regs[*rd as usize] = Value::Bool(&regs[*r1 as usize] == &regs[*r2 as usize]);
            }
            Opcode::Neq { rd, r1, r2 } => {
                regs[*rd as usize] = Value::Bool(&regs[*r1 as usize] != &regs[*r2 as usize]);
            }
            Opcode::LtInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_cmp(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| a < b,
                    |a, b| a < b,
                )?;
            }
            Opcode::LeInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_cmp(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| a <= b,
                    |a, b| a <= b,
                )?;
            }
            Opcode::GtInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_cmp(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| a > b,
                    |a, b| a > b,
                )?;
            }
            Opcode::GeInt { rd, r1, r2 } => {
                regs[*rd as usize] = int_cmp(
                    &regs[*r1 as usize],
                    &regs[*r2 as usize],
                    |a, b| a >= b,
                    |a, b| a >= b,
                )?;
            }

            // === Boolean Operations ===
            Opcode::And { rd, r1, r2 } => {
                let a = as_bool(&regs[*r1 as usize])?;
                let b = as_bool(&regs[*r2 as usize])?;
                regs[*rd as usize] = Value::Bool(a && b);
            }
            Opcode::Or { rd, r1, r2 } => {
                let a = as_bool(&regs[*r1 as usize])?;
                let b = as_bool(&regs[*r2 as usize])?;
                regs[*rd as usize] = Value::Bool(a || b);
            }
            Opcode::Not { rd, rs } => {
                regs[*rd as usize] = Value::Bool(!as_bool(&regs[*rs as usize])?);
            }
            Opcode::Implies { rd, r1, r2 } => {
                let a = as_bool(&regs[*r1 as usize])?;
                let b = as_bool(&regs[*r2 as usize])?;
                regs[*rd as usize] = Value::Bool(!a || b);
            }
            Opcode::Equiv { rd, r1, r2 } => {
                let a = as_bool(&regs[*r1 as usize])?;
                let b = as_bool(&regs[*r2 as usize])?;
                regs[*rd as usize] = Value::Bool(a == b);
            }

            // === Control Flow ===
            Opcode::Jump { offset } => {
                return Ok(DispatchOutcome::Jump(
                    ((pc as i64) + (*offset as i64)) as usize,
                ));
            }
            Opcode::JumpTrue { rs, offset } => {
                if as_bool(&regs[*rs as usize])? {
                    return Ok(DispatchOutcome::Jump(
                        ((pc as i64) + (*offset as i64)) as usize,
                    ));
                }
            }
            Opcode::JumpFalse { rs, offset } => {
                if !as_bool(&regs[*rs as usize])? {
                    return Ok(DispatchOutcome::Jump(
                        ((pc as i64) + (*offset as i64)) as usize,
                    ));
                }
            }
            Opcode::Call {
                rd,
                op_idx,
                args_start,
                argc,
            } => {
                let callee = self.chunk.get_function(*op_idx);
                if callee.arity != *argc {
                    return Err(VmError::TypeError {
                        expected: "matching arity",
                        actual: format!(
                            "operator {} expects {} args, got {}",
                            callee.name, callee.arity, argc
                        ),
                    });
                }
                enter_vm_call()?;
                let mut callee_regs = vec![Value::Bool(false); (callee.max_register as usize) + 1];
                for i in 0..(*argc as usize) {
                    callee_regs[i] = regs[*args_start as usize + i].clone();
                }
                let result =
                    self.execute_with_regs(callee, &self.chunk.constants, &mut callee_regs);
                exit_vm_call();
                regs[*rd as usize] = result?;
            }
            Opcode::ValueApply {
                rd,
                func,
                args_start,
                argc,
            } => {
                // Part of #3697: If the callable is a closure with a compiled
                // bytecode function, execute it via Call instead of tree-walking.
                if let Value::Closure(closure) = &regs[*func as usize] {
                    if let Some(bc_idx) = closure.bytecode_func_idx() {
                        if (bc_idx as usize) < self.chunk.functions.len() {
                            let callee = self.chunk.get_function(bc_idx);
                            // Collect capture values from the closure env to pass
                            // as extra arguments after the real args. Sort by key
                            // so the order matches the compiler's alphabetical
                            // capture parameter order (HashMap iteration is unordered).
                            // Part of #3697: Both sides must agree on canonical order.
                            let mut capture_entries: Vec<_> = closure
                                .env()
                                .iter()
                                .map(|(k, v)| (k.clone(), v.clone()))
                                .collect();
                            capture_entries.sort_by(|(a, _), (b, _)| a.cmp(b));
                            let capture_values: Vec<Value> =
                                capture_entries.into_iter().map(|(_, v)| v).collect();
                            let total_argc = *argc as usize + capture_values.len();
                            if callee.arity as usize == total_argc {
                                enter_vm_call()?;
                                let mut callee_regs =
                                    vec![Value::Bool(false); (callee.max_register as usize) + 1];
                                // Copy real arguments.
                                for i in 0..(*argc as usize) {
                                    callee_regs[i] = regs[*args_start as usize + i].clone();
                                }
                                // Copy capture values as extra parameters.
                                for (i, v) in capture_values.into_iter().enumerate() {
                                    callee_regs[*argc as usize + i] = v;
                                }
                                let result = self.execute_with_regs(
                                    callee,
                                    &self.chunk.constants,
                                    &mut callee_regs,
                                );
                                exit_vm_call();
                                regs[*rd as usize] = result?;
                                return Ok(DispatchOutcome::Continue);
                            }
                        }
                    }
                }
                let args: Vec<Value> = (0..(*argc as usize))
                    .map(|i| regs[*args_start as usize + i].clone())
                    .collect();
                regs[*rd as usize] = value_apply(self.eval_ctx, &regs[*func as usize], &args)?;
            }
            Opcode::Ret { rs } => {
                return Ok(DispatchOutcome::Return(regs[*rs as usize].clone()));
            }

            // === External Call (INSTANCE-imported operator fallback) ===
            Opcode::CallExternal {
                rd,
                name_idx,
                args_start,
                argc,
            } => {
                let name = match constants.get_value(*name_idx) {
                    Value::String(s) => s.clone(),
                    other => {
                        return Err(VmError::TypeError {
                            expected: "string operator name in constant pool",
                            actual: format!("{other:?}"),
                        });
                    }
                };
                let args: Vec<Value> = (0..(*argc as usize))
                    .map(|i| regs[*args_start as usize + i].clone())
                    .collect();
                regs[*rd as usize] = call_external(self.eval_ctx, &name, &args)?;
            }

            // === Special ===
            Opcode::CondMove { rd, cond, rs } => {
                if as_bool(&regs[*cond as usize])? {
                    regs[*rd as usize] = regs[*rs as usize].clone();
                }
            }
            Opcode::Unchanged { rd, start, count } => {
                let ns = self.next_state.ok_or_else(|| VmError::TypeError {
                    expected: "next state for UNCHANGED",
                    actual: "no next state bound".to_string(),
                })?;
                let mut all_equal = true;
                for i in 0..(*count as u16) {
                    let var_idx = match constants.get_value(*start + i) {
                        Value::SmallInt(idx) => *idx as usize,
                        other => {
                            return Err(VmError::TypeError {
                                expected: "integer var index in constant pool",
                                actual: format!("{other:?}"),
                            });
                        }
                    };
                    let cur = load_state_var(self.state, &mut self.state_cache, var_idx as u16)?;
                    let next =
                        load_prime_var(Some(ns), self.next_state_cache.as_mut(), var_idx as u16)?;
                    if cur != next {
                        all_equal = false;
                        break;
                    }
                }
                regs[*rd as usize] = Value::Bool(all_equal);
            }

            _ => unreachable!("non-scalar opcode routed to execute_scalar_opcode"),
        }

        Ok(DispatchOutcome::Continue)
    }
}
