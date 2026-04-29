// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Invariant and constraint checking for parallel successor processing.
//!
//! Part of #2492: extracted from `successors/` to keep file sizes
//! under the 500-line limit.

#[cfg(debug_assertions)]
use super::super::tla2_debug;
use super::super::trace_value_for_fp;
use super::InvariantCheckCtx;
use crate::check::CheckError;
use crate::checker_ops::InvariantOutcome;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, Fingerprint};
// Part of #4267 Gate 1 Batch C: collapse Cranelift-backed JIT type paths.
#[cfg(test)]
use tla_jit::bytecode_lower::JitInvariantCache as JitInvariantCacheImpl;

fn jit_verify_results_match(
    left: &Result<Option<String>, CheckError>,
    right: &Result<Option<String>, CheckError>,
) -> bool {
    match (left, right) {
        (Ok(left), Ok(right)) => left == right,
        (Err(left), Err(right)) => format!("{left:?}") == format!("{right:?}"),
        _ => false,
    }
}

fn format_jit_verify_result(result: &Result<Option<String>, CheckError>) -> String {
    match result {
        Ok(Some(invariant)) => format!("Ok(Some({invariant}))"),
        Ok(None) => "Ok(None)".to_string(),
        Err(error) => format!("Err({error:?})"),
    }
}

fn cross_check_jit_invariants(
    ctx: &mut EvalCtx,
    ic: &InvariantCheckCtx<'_>,
    succ_arr: &ArrayState,
    succ_fp: Fingerprint,
    jit_result: Result<Option<String>, CheckError>,
) -> Result<Option<String>, CheckError> {
    if !ic.config.jit_verify {
        return jit_result;
    }

    ic.jit_verify_checked.set(ic.jit_verify_checked.get() + 1);
    let interpreter_result =
        crate::checker_ops::check_invariants_array_state(ctx, &ic.config.invariants, succ_arr);
    if !jit_verify_results_match(&jit_result, &interpreter_result) {
        ic.jit_verify_mismatches
            .set(ic.jit_verify_mismatches.get() + 1);
        eprintln!(
            "[jit-verify] mismatch at state {succ_fp}: jit={} interpreter={}",
            format_jit_verify_result(&jit_result),
            format_jit_verify_result(&interpreter_result),
        );
    }
    interpreter_result
}

/// Check invariants on a successor state.
///
/// Returns an [`InvariantOutcome`] so the caller can decide how to proceed
/// without duplicating the match logic.
pub(super) fn check_successor_invariants(
    ctx: &mut EvalCtx,
    ic: &InvariantCheckCtx<'_>,
    succ_arr: &ArrayState,
    succ_fp: Fingerprint,
    succ_level: u32,
) -> InvariantOutcome {
    if ic.uses_trace && ic.store_full_states {
        debug_eprintln!(
            tla2_debug(),
            "[trace] parallel TLCExt!Trace reconstruction enabled: succ_fp={succ_fp}"
        );
        let trace_val = trace_value_for_fp(succ_fp, ic.parent_log, ic.seen, ic.var_registry);
        ctx.set_tlc_trace_value(Some(trace_val));
    }

    let outcome = if ic.config.invariants.is_empty() && ic.eval_state_invariants.is_empty() {
        InvariantOutcome::Ok
    } else {
        ctx.set_tlc_level(succ_level);
        crate::eval::clear_for_bound_state_eval_scope(ctx);

        let mut unchecked_by_jit: Option<Vec<String>> = None;

        // Part of #3908: Use selective flattening — only serialize compound
        // vars that JIT invariants actually reference.
        // Optimized: uses check_all (no per-invariant counter overhead) and
        // inlines jit_verify check to skip function call when disabled.
        if let Some(ref jit_cache) = ic.jit_cache {
            let mut state_i64 = ic.jit_state_scratch.borrow_mut();
            if crate::check::model_checker::invariants::flatten_state_to_i64_selective(
                succ_arr,
                &mut state_i64,
                jit_cache.required_vars(),
            ) {
                let mut unchecked = Vec::new();
                match jit_cache.check_all(&ic.config.invariants, &state_i64, &mut unchecked) {
                    Ok(Some(invariant)) => {
                        ic.jit_hits.set(ic.jit_hits.get() + 1);
                        let unchecked_count = unchecked.len();
                        ic.jit_not_compiled
                            .set(ic.jit_not_compiled.get() + unchecked_count);
                        // Inline jit_verify: skip cross-check when disabled.
                        if !ic.config.jit_verify {
                            let outcome = InvariantOutcome::Violation {
                                invariant: invariant.to_string(),
                                state_fp: succ_fp,
                            };
                            return finish_invariant_dispatch(ctx, ic, outcome);
                        }
                        let verified_result = cross_check_jit_invariants(
                            ctx,
                            ic,
                            succ_arr,
                            succ_fp,
                            Ok(Some(invariant.to_string())),
                        );
                        let outcome = match verified_result {
                            Ok(Some(invariant)) => InvariantOutcome::Violation {
                                invariant,
                                state_fp: succ_fp,
                            },
                            Err(error) => InvariantOutcome::Error(error),
                            Ok(None) => check_eval_state_invariants(ctx, ic, succ_arr, succ_fp),
                        };
                        return finish_invariant_dispatch(ctx, ic, outcome);
                    }
                    Ok(None) => {
                        let unchecked_count = unchecked.len();
                        ic.jit_not_compiled
                            .set(ic.jit_not_compiled.get() + unchecked_count);
                        if unchecked.is_empty() {
                            ic.jit_hits.set(ic.jit_hits.get() + 1);
                            // Inline jit_verify: skip cross-check when disabled.
                            if !ic.config.jit_verify {
                                let outcome =
                                    check_eval_state_invariants(ctx, ic, succ_arr, succ_fp);
                                return finish_invariant_dispatch(ctx, ic, outcome);
                            }
                            let verified_result =
                                cross_check_jit_invariants(ctx, ic, succ_arr, succ_fp, Ok(None));
                            let outcome = match verified_result {
                                Ok(Some(invariant)) => InvariantOutcome::Violation {
                                    invariant,
                                    state_fp: succ_fp,
                                },
                                Err(error) => InvariantOutcome::Error(error),
                                Ok(None) => check_eval_state_invariants(ctx, ic, succ_arr, succ_fp),
                            };
                            return finish_invariant_dispatch(ctx, ic, outcome);
                        }
                        ic.jit_misses.set(ic.jit_misses.get() + 1);
                        unchecked_by_jit = Some(
                            unchecked
                                .into_iter()
                                .map(str::to_string)
                                .collect::<Vec<_>>(),
                        );
                    }
                    Err(_) => {
                        ic.jit_misses.set(ic.jit_misses.get() + 1);
                    }
                }
            } else {
                ic.jit_misses.set(ic.jit_misses.get() + 1);
            }
        }

        let invariants = unchecked_by_jit.as_deref().unwrap_or(&ic.config.invariants);

        if let Some(ref bytecode) = ic.bytecode {
            check_successor_invariants_hybrid_bytecode(
                ctx, bytecode, invariants, ic, succ_arr, succ_fp,
            )
        } else {
            check_successor_invariants_tree_walk(ctx, invariants, ic, succ_arr, succ_fp)
        }
    };

    finish_invariant_dispatch(ctx, ic, outcome)
}

fn finish_invariant_dispatch(
    ctx: &mut EvalCtx,
    ic: &InvariantCheckCtx<'_>,
    outcome: InvariantOutcome,
) -> InvariantOutcome {
    if ic.uses_trace {
        ctx.set_tlc_trace_value(None);
    }

    match outcome {
        InvariantOutcome::Violation {
            invariant,
            state_fp,
        } if ic.continue_on_error => {
            let _ = ic.first_violation.set((invariant, state_fp));
            InvariantOutcome::ViolationContinued
        }
        other => other,
    }
}

fn check_successor_invariants_hybrid_bytecode(
    ctx: &mut EvalCtx,
    bytecode: &tla_eval::bytecode_vm::CompiledBytecode,
    invariants: &[String],
    ic: &InvariantCheckCtx<'_>,
    succ_arr: &ArrayState,
    succ_fp: Fingerprint,
) -> InvariantOutcome {
    use tla_eval::bytecode_vm::BytecodeVm;

    let mut unchecked = Vec::new();
    let mut bytecode_violation: Option<(usize, String)> = None;

    {
        let mut vm = BytecodeVm::from_state_env(&bytecode.chunk, succ_arr.env_ref(), None)
            .with_eval_ctx(ctx);

        for (idx, inv_name) in invariants.iter().enumerate() {
            let Some(&func_idx) = bytecode.op_indices.get(inv_name) else {
                unchecked.push(inv_name.clone());
                continue;
            };

            match vm.execute_function(func_idx) {
                Ok(tla_value::Value::Bool(true)) => {
                    tla_eval::note_bytecode_vm_execution();
                }
                Ok(tla_value::Value::Bool(false)) => {
                    tla_eval::note_bytecode_vm_execution();
                    bytecode_violation = Some((idx, inv_name.clone()));
                    break;
                }
                Ok(_) => {
                    tla_eval::note_bytecode_vm_execution();
                    return InvariantOutcome::Error(
                        crate::EvalCheckError::InvariantNotBoolean(inv_name.clone()).into(),
                    );
                }
                Err(_) => {
                    tla_eval::note_bytecode_vm_fallback();
                    unchecked.push(inv_name.clone());
                }
            }
        }
    }

    if let Some((violation_idx, inv_name)) = bytecode_violation {
        // A bytecode FALSE is a candidate violation, but the canonical evaluator
        // owns TLC error precedence for cases like non-enumerable set equality.
        match crate::checker_ops::check_invariants_array_state(
            ctx,
            std::slice::from_ref(&inv_name),
            succ_arr,
        ) {
            Ok(Some(invariant)) => {
                return InvariantOutcome::Violation {
                    invariant,
                    state_fp: succ_fp,
                };
            }
            Err(e) => return InvariantOutcome::Error(e),
            Ok(None) => unchecked.extend(invariants.iter().skip(violation_idx + 1).cloned()),
        }
    }

    if !unchecked.is_empty() {
        match crate::checker_ops::check_invariants_array_state(ctx, &unchecked, succ_arr) {
            Ok(Some(invariant)) => {
                return InvariantOutcome::Violation {
                    invariant,
                    state_fp: succ_fp,
                };
            }
            Err(e) => return InvariantOutcome::Error(e),
            Ok(None) => {}
        }
    }

    check_eval_state_invariants(ctx, ic, succ_arr, succ_fp)
}

fn check_successor_invariants_tree_walk(
    ctx: &mut EvalCtx,
    invariants: &[String],
    ic: &InvariantCheckCtx<'_>,
    succ_arr: &ArrayState,
    succ_fp: Fingerprint,
) -> InvariantOutcome {
    match crate::checker_ops::check_invariants_array_state(ctx, invariants, succ_arr) {
        Ok(Some(invariant)) => InvariantOutcome::Violation {
            invariant,
            state_fp: succ_fp,
        },
        Err(error) => InvariantOutcome::Error(error),
        Ok(None) => check_eval_state_invariants(ctx, ic, succ_arr, succ_fp),
    }
}

fn check_eval_state_invariants(
    ctx: &mut EvalCtx,
    ic: &InvariantCheckCtx<'_>,
    succ_arr: &ArrayState,
    succ_fp: Fingerprint,
) -> InvariantOutcome {
    match crate::checker_ops::check_eval_state_invariants(ctx, ic.eval_state_invariants, succ_arr) {
        Ok(Some(invariant)) => InvariantOutcome::Violation {
            invariant,
            state_fp: succ_fp,
        },
        Err(e) => InvariantOutcome::Error(e),
        Ok(None) => InvariantOutcome::Ok,
    }
}

/// Check state/action constraints for a successor using ArrayState.
///
/// Part of #2484: parallel path uses the shared canonical ArrayState
/// constraint helpers, matching the sequential checker.
///
/// When `action_analysis` is provided, uses skip-optimized evaluation for
/// ACTION_CONSTRAINTs whose referenced variables haven't changed between
/// the current and successor states.
pub(super) fn check_successor_constraints_array(
    ctx: &mut EvalCtx,
    config: &Config,
    current_array: &ArrayState,
    succ_array: &ArrayState,
    action_analysis: Option<&crate::checker_ops::ActionConstraintAnalysis>,
) -> Result<bool, CheckError> {
    if !crate::checker_ops::check_state_constraints_array(ctx, &config.constraints, succ_array)? {
        return Ok(false);
    }
    if let Some(analysis) = action_analysis {
        return crate::checker_ops::check_action_constraints_with_analysis(
            ctx,
            &config.action_constraints,
            current_array,
            succ_array,
            analysis,
        );
    }
    crate::checker_ops::check_action_constraints_array(
        ctx,
        &config.action_constraints,
        current_array,
        succ_array,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker_setup::{setup_checker_modules, SetupOptions};
    use crate::config::Config;
    use crate::test_support::parse_module;
    use crate::Value;
    use std::cell::RefCell;
    use std::sync::{Arc, OnceLock};
    use tla_core::ast::{Expr, OperatorDef, Unit};
    use tla_core::span::Spanned;

    fn build_jit_cache(
        module: &tla_core::ast::Module,
        registry: &crate::var_index::VarRegistry,
        invariants: &[String],
    ) -> crate::parallel::SharedJitInvariantCache {
        let mut compiled_module = module.clone();
        for unit in &mut compiled_module.units {
            if let Unit::Operator(def) = &mut unit.node {
                tla_eval::state_var::resolve_state_vars_in_op_def(def, registry);
            }
        }

        let bytecode =
            tla_eval::bytecode_vm::compile_operators_to_bytecode(&compiled_module, &[], invariants);
        assert!(
            bytecode.op_indices.contains_key(&invariants[0]),
            "test invariant should compile to bytecode and JIT"
        );
        Arc::new(
            JitInvariantCacheImpl::build(&bytecode.chunk, &bytecode.op_indices)
                .expect("JIT cache should build for test invariant"),
        )
    }

    fn make_false_op(name: &str) -> OperatorDef {
        OperatorDef {
            name: Spanned::dummy(name.to_string()),
            params: vec![],
            body: Spanned::dummy(Expr::Bool(false)),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }
    }

    fn make_invariant_ctx<'a>(
        config: &'a Config,
        registry: &'a crate::var_index::VarRegistry,
        bytecode: &'a Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
        jit_cache: &'a Option<crate::parallel::SharedJitInvariantCache>,
        jit_state_scratch: &'a RefCell<Vec<i64>>,
        first_violation: &'a OnceLock<(String, Fingerprint)>,
        first_action_property_violation: &'a OnceLock<(String, Fingerprint)>,
        parent_log: &'a crate::parallel::ParentLog,
        seen: &'a crate::parallel::FxDashMap<Fingerprint, ArrayState>,
        depths: &'a crate::parallel::FxDashMap<Fingerprint, usize>,
    ) -> InvariantCheckCtx<'a> {
        InvariantCheckCtx {
            config,
            eval_implied_actions: &[],
            eval_state_invariants: &[],
            uses_trace: false,
            store_full_states: false,
            continue_on_error: false,
            first_violation,
            first_action_property_violation,
            parent_log,
            worker_id: 0,
            seen,
            var_registry: registry,
            depths,
            track_depths: false,
            bytecode,
            jit_cache,
            jit_state_scratch,
            jit_hits: std::cell::Cell::new(0),
            jit_misses: std::cell::Cell::new(0),
            jit_fallback: std::cell::Cell::new(0),
            jit_not_compiled: std::cell::Cell::new(0),
            jit_verify_checked: std::cell::Cell::new(0),
            jit_verify_mismatches: std::cell::Cell::new(0),
            action_constraint_analysis: None,
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parallel_successor_invariants_use_jit_before_eval_fallback() {
        let module = parse_module(
            r#"
---- MODULE ParallelJitSuccessor ----
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x > 0
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let crate::checker_setup::CheckerSetup {
            mut ctx,
            main_module,
            ..
        } = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        let registry = ctx.var_registry().clone();
        ctx.define_op("Inv".to_string(), make_false_op("Inv"));

        let bytecode = None;
        let jit_cache = Some(build_jit_cache(&main_module, &registry, &config.invariants));
        let jit_state_scratch = RefCell::new(Vec::new());
        let first_violation = OnceLock::new();
        let first_action_property_violation = OnceLock::new();
        let parent_log = crate::parallel::ParentLog::new(1);
        let seen = crate::parallel::FxDashMap::default();
        let depths = crate::parallel::FxDashMap::default();
        let inv_ctx = make_invariant_ctx(
            &config,
            &registry,
            &bytecode,
            &jit_cache,
            &jit_state_scratch,
            &first_violation,
            &first_action_property_violation,
            &parent_log,
            &seen,
            &depths,
        );
        let succ =
            ArrayState::from_state(&crate::State::from_pairs([("x", Value::int(1))]), &registry);

        let outcome = check_successor_invariants(&mut ctx, &inv_ctx, &succ, Fingerprint(1), 1);

        assert!(matches!(outcome, InvariantOutcome::Ok));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parallel_successor_invariants_jit_succeeds_with_unreferenced_compound_var() {
        // Part of #3908: With selective flattening, the JIT succeeds when the
        // invariant only references scalar vars, even if other vars are compound.
        // Here, Inv only reads `x` (scalar), so `y` (record) is not serialized.
        // The JIT evaluates `x > 0` with x=1 → TRUE (no violation).
        let module = parse_module(
            r#"
---- MODULE ParallelJitFallback ----
VARIABLE x, y
Init == /\ x = 1
        /\ y = [tag |-> 0]
Next == /\ x' = x
        /\ y' = y
Inv == x > 0
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let crate::checker_setup::CheckerSetup {
            mut ctx,
            main_module,
            ..
        } = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        let registry = ctx.var_registry().clone();
        ctx.define_op("Inv".to_string(), make_false_op("Inv"));

        let bytecode = None;
        let jit_cache = Some(build_jit_cache(&main_module, &registry, &config.invariants));
        let jit_state_scratch = RefCell::new(Vec::new());
        let first_violation = OnceLock::new();
        let first_action_property_violation = OnceLock::new();
        let parent_log = crate::parallel::ParentLog::new(1);
        let seen = crate::parallel::FxDashMap::default();
        let depths = crate::parallel::FxDashMap::default();
        let inv_ctx = make_invariant_ctx(
            &config,
            &registry,
            &bytecode,
            &jit_cache,
            &jit_state_scratch,
            &first_violation,
            &first_action_property_violation,
            &parent_log,
            &seen,
            &depths,
        );
        let succ = ArrayState::from_state(
            &crate::State::from_pairs([
                ("x", Value::int(1)),
                ("y", Value::record([("tag", Value::int(0))])),
            ]),
            &registry,
        );

        let outcome = check_successor_invariants(&mut ctx, &inv_ctx, &succ, Fingerprint(1), 1);

        // JIT evaluates `x > 0` (x=1) → TRUE, no violation.
        assert!(
            matches!(outcome, InvariantOutcome::Ok),
            "JIT should succeed with selective flattening when invariant doesn't reference compound vars"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parallel_successor_invariants_skip_jit_checked_prefix_on_tree_walk_fallback() {
        let module = parse_module(
            r#"
---- MODULE ParallelJitMixedFallback ----
VARIABLE x
Init == x = 1
Next == x' = x
Helper(v) == v > 0
InvJit == x > 0
InvCall == Helper(x)
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InvJit".to_string(), "InvCall".to_string()],
            ..Default::default()
        };
        let crate::checker_setup::CheckerSetup {
            mut ctx,
            main_module,
            ..
        } = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        let registry = ctx.var_registry().clone();
        ctx.define_op("InvJit".to_string(), make_false_op("InvJit"));

        let bytecode = None;
        // Build JIT cache with ONLY InvJit — InvCall is deliberately excluded so
        // it returns NotCompiled and forces tree-walk fallback for that invariant.
        // (Previously, InvCall used Helper(x) which the JIT couldn't inline, but
        // JIT improvements now handle simple function calls natively.)
        let jit_only = vec!["InvJit".to_string()];
        let jit_cache = Some(build_jit_cache(&main_module, &registry, &jit_only));
        assert_eq!(
            jit_cache.as_ref().unwrap().check_invariant("InvCall", &[1]),
            None
        );
        let jit_state_scratch = RefCell::new(Vec::new());
        let first_violation = OnceLock::new();
        let first_action_property_violation = OnceLock::new();
        let parent_log = crate::parallel::ParentLog::new(1);
        let seen = crate::parallel::FxDashMap::default();
        let depths = crate::parallel::FxDashMap::default();
        let inv_ctx = make_invariant_ctx(
            &config,
            &registry,
            &bytecode,
            &jit_cache,
            &jit_state_scratch,
            &first_violation,
            &first_action_property_violation,
            &parent_log,
            &seen,
            &depths,
        );
        let succ =
            ArrayState::from_state(&crate::State::from_pairs([("x", Value::int(1))]), &registry);

        let outcome = check_successor_invariants(&mut ctx, &inv_ctx, &succ, Fingerprint(1), 1);

        assert!(
            matches!(outcome, InvariantOutcome::Ok),
            "parallel fallback should resume at the first JIT-unchecked invariant, not re-run the JIT-checked prefix"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parallel_jit_verify_uses_interpreter_result_on_pass_mismatch() {
        let module = parse_module(
            r#"
---- MODULE ParallelJitVerifyPassMismatch ----
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x > 0
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            jit_verify: true,
            ..Default::default()
        };
        let crate::checker_setup::CheckerSetup {
            mut ctx,
            main_module,
            ..
        } = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        let registry = ctx.var_registry().clone();
        ctx.define_op("Inv".to_string(), make_false_op("Inv"));

        let bytecode = None;
        let jit_cache = Some(build_jit_cache(&main_module, &registry, &config.invariants));
        let jit_state_scratch = RefCell::new(Vec::new());
        let first_violation = OnceLock::new();
        let first_action_property_violation = OnceLock::new();
        let parent_log = crate::parallel::ParentLog::new(1);
        let seen = crate::parallel::FxDashMap::default();
        let depths = crate::parallel::FxDashMap::default();
        let inv_ctx = make_invariant_ctx(
            &config,
            &registry,
            &bytecode,
            &jit_cache,
            &jit_state_scratch,
            &first_violation,
            &first_action_property_violation,
            &parent_log,
            &seen,
            &depths,
        );
        let succ =
            ArrayState::from_state(&crate::State::from_pairs([("x", Value::int(1))]), &registry);

        let outcome = check_successor_invariants(&mut ctx, &inv_ctx, &succ, Fingerprint(1), 1);

        assert!(matches!(
            outcome,
            InvariantOutcome::Violation { ref invariant, .. } if invariant == "Inv"
        ));
        assert_eq!(inv_ctx.jit_verify_checked.get(), 1);
        assert_eq!(inv_ctx.jit_verify_mismatches.get(), 1);
    }
}
