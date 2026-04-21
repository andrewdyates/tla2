// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bytecode compilation from TIR operators.
//!
//! Provides a high-level API for compiling named operators from AST modules
//! into a `BytecodeChunk` suitable for execution by `BytecodeVm`.

use std::sync::Arc;

use rustc_hash::FxHashMap;
use tla_core::ast::Module;
use tla_core::{name_intern::intern_name, NameId};
use tla_tir::bytecode::{BytecodeChunk, BytecodeCompiler, CompileError};
use tla_tir::{lower_operator_with_env, lower_operator_with_env_permissive, TirLoweringEnv};
use tla_value::{boolean_set, Value};

/// Result of compiling a set of named operators to bytecode.
///
/// Contains the compiled bytecode chunk and a mapping from operator names
/// to their function indices within the chunk. Operators that failed to
/// compile (unsupported TIR constructs, etc.) are silently skipped — the
/// caller should fall back to tree-walking evaluation for those.
#[derive(Debug)]
pub struct CompiledBytecode {
    /// The compiled bytecode chunk (shared constant pool + function table).
    pub chunk: BytecodeChunk,
    /// Mapping from operator name to function index in the chunk.
    pub op_indices: FxHashMap<String, u16>,
    /// Names of operators that failed to compile (for diagnostics).
    pub failed: Vec<(String, CompileError)>,
}

/// Clone resolved constants and inject the stdlib constant names that bytecode
/// compilation cannot recover through builtin dispatch alone.
#[must_use]
pub(crate) fn resolved_constants_with_bytecode_stdlib(
    resolved_constants: &crate::HashMap<NameId, Value>,
    op_replacements: Option<&crate::HashMap<String, String>>,
) -> std::collections::HashMap<NameId, Value> {
    let mut bytecode_constants: std::collections::HashMap<NameId, Value> = resolved_constants
        .iter()
        .map(|(name_id, value)| (*name_id, value.clone()))
        .collect();

    // Insert stdlib defaults only when the model config hasn't overridden
    // them via either resolved_constants or op_replacements.
    //
    // When a .cfg file has `Nat <- NatOverride`, `op_replacements` maps
    // `"Nat" → "NatOverride"`. The bytecode compiler should resolve `Nat`
    // via the replacement chain (Call to NatOverride), NOT via a
    // `ModelValue("Nat")` constant. Adding ModelValue("Nat") short-circuits
    // the replacement path in `compile_name_expr` and prevents the JIT from
    // pre-materializing quantifier domains over Nat.
    for (name, value) in [
        (
            "Nat",
            Value::try_model_value("Nat").expect("Nat stdlib value"),
        ),
        (
            "Int",
            Value::try_model_value("Int").expect("Int stdlib value"),
        ),
        (
            "Real",
            Value::try_model_value("Real").expect("Real stdlib value"),
        ),
        (
            "Infinity",
            Value::try_model_value("Infinity").expect("Infinity stdlib value"),
        ),
        ("BOOLEAN", boolean_set()),
        ("STRING", Value::StringSet),
    ] {
        // Skip stdlib default if this name has an operator replacement
        // (e.g., Nat <- NatOverride). The replacement chain will resolve
        // to the actual set value via a Call opcode.
        if let Some(replacements) = op_replacements {
            if replacements.contains_key(name) {
                continue;
            }
        }
        bytecode_constants
            .entry(intern_name(name))
            .or_insert(value);
    }

    bytecode_constants
}

/// Compile a set of named operators from a module into bytecode.
///
/// For each operator name in `op_names`, attempts to:
/// 1. Look up the operator definition in the root module
/// 2. Lower it to TIR via `lower_operator_with_env_permissive`
/// 3. Compile the TIR to bytecode via `BytecodeCompiler`
///
/// Operators that fail at any step are recorded in `failed` and skipped.
/// The caller uses `op_indices` to check which operators are available
/// for bytecode execution and falls back to tree-walking for the rest.
pub fn compile_operators_to_bytecode(
    root: &Module,
    deps: &[&Module],
    op_names: &[String],
) -> CompiledBytecode {
    let resolved_constants = crate::HashMap::default();
    compile_operators_to_bytecode_with_constants(root, deps, op_names, &resolved_constants)
}

/// Export TIR-lowered operator bodies visible from the root bytecode namespace.
///
/// This includes bare `INSTANCE` imports with their resolved substitution
/// scope preserved, so downstream bytecode compilation can treat the exported
/// bodies as the authoritative namespace instead of re-lowering raw dep-module
/// operators without INSTANCE context.
#[must_use]
pub fn collect_bytecode_namespace_callees(
    root: &Module,
    deps: &[&Module],
) -> std::collections::HashMap<String, tla_tir::bytecode::CalleeInfo> {
    let tir_prog = crate::tir::TirProgram::from_modules(root, deps);
    tir_prog.seed_bytecode_namespace_cache();
    tir_prog.export_callee_bodies().into_iter().collect()
}

/// Compile a set of named operators from a module into bytecode using a
/// snapshot of already-resolved constant values.
///
/// Uses the full bytecode compiler path with TIR-exported callee bodies so
/// bare `INSTANCE` imports compile with their resolved substitution scope.
pub fn compile_operators_to_bytecode_with_constants(
    root: &Module,
    deps: &[&Module],
    op_names: &[String],
    resolved_constants: &crate::HashMap<NameId, Value>,
) -> CompiledBytecode {
    let tir_callees = collect_bytecode_namespace_callees(root, deps);
    compile_operators_to_bytecode_full(
        root,
        deps,
        op_names,
        resolved_constants,
        None,
        Some(&tir_callees),
    )
}

/// Compile operators with both resolved constants and operator replacements.
///
/// `tir_callee_bodies`: optional pre-resolved operator bodies from TIR namespace
/// seeding (includes INSTANCE-imported operators). When present, these bodies
/// are treated as the authoritative root namespace so cross-module operators
/// keep their resolved INSTANCE substitution context during compilation.
/// Part of #3585, #3693.
pub fn compile_operators_to_bytecode_full(
    root: &Module,
    deps: &[&Module],
    op_names: &[String],
    resolved_constants: &crate::HashMap<NameId, Value>,
    op_replacements: Option<&crate::HashMap<String, String>>,
    tir_callee_bodies: Option<&std::collections::HashMap<String, tla_tir::bytecode::CalleeInfo>>,
) -> CompiledBytecode {
    use tla_core::ast::Unit;

    let mut env = TirLoweringEnv::new(root);
    for dep in deps {
        env.add_module(dep);
    }

    let mut compiler = BytecodeCompiler::with_resolved_constants(
        resolved_constants_with_bytecode_stdlib(resolved_constants, op_replacements),
    );
    if let Some(op_repl) = op_replacements {
        if !op_repl.is_empty() {
            let replacements: std::collections::HashMap<String, String> = op_repl
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            compiler.set_op_replacements(replacements);
        }
    }
    let mut failed = Vec::new();

    // Phase 1: Pre-compile all zero-arg operators from root + deps so they
    // are available as Call targets when invariant bodies reference them.
    // Multi-pass convergence loop: operators that fail because they reference
    // not-yet-compiled operators are retried on subsequent passes once their
    // dependencies become available. This mirrors the fixed-point approach
    // already used by `compile_expression_with_callees`.
    let all_modules: Vec<&Module> = std::iter::once(root).chain(deps.iter().copied()).collect();
    let stats_phase1 = {
            static BVM_STATS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *BVM_STATS.get_or_init(|| {
                matches!(std::env::var("TLA2_BYTECODE_VM_STATS").as_deref(), Ok("1"))
            })
        };
    let mut _phase1_passes = 0u32;
    loop {
        let mut progress = false;
        _phase1_passes += 1;
        for module in &all_modules {
            for unit in &module.units {
                if let Unit::Operator(def) = &unit.node {
                    let name = &def.name.node;
                    if compiler.has_operator(name) {
                        continue;
                    }
                    if tir_callee_bodies.is_some_and(|callees| callees.contains_key(name)) {
                        continue;
                    }
                    if !def.params.is_empty() {
                        continue;
                    }
                    // Best-effort: skip if lowering or compilation fails.
                    // Pass the owning module so sibling operator names resolve.
                    // Use NON-permissive lowering here: Phase 1 pre-compiles ALL
                    // zero-arg ops from root + deps (including proof modules like
                    // TLAPS). Permissive lowering causes massive compilation of
                    // proof module operators, hanging specs like MCQuicksort.
                    // Only Phase 2 (target operators) needs permissive lowering.
                    if let Ok(tir_op) = lower_operator_with_env(&env, module, def) {
                        if compiler.compile_operator(&tir_op).is_ok() {
                            progress = true;
                        }
                    }
                }
            }
        }
        if !progress {
            break;
        }
    }
    if stats_phase1 {
        eprintln!(
            "[bytecode] Phase 1: {_phase1_passes} passes, {} zero-arg ops compiled",
            compiler.op_count()
        );
    }

    // Phase 1.5: Collect all operators (including parameterized) as callee
    // bodies so that Phase 2 can resolve cross-operator calls via
    // compile_expression_with_callees. This allows invariant bodies that
    // reference parameterized helpers (e.g., IInv calling Before(i,j))
    // to compile successfully.
    let mut callee_bodies: std::collections::HashMap<String, tla_tir::bytecode::CalleeInfo> =
        std::collections::HashMap::new();
    let stats_enabled = {
            static BVM_STATS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *BVM_STATS.get_or_init(|| {
                matches!(std::env::var("TLA2_BYTECODE_VM_STATS").as_deref(), Ok("1"))
            })
        };
    // Track Phase 1.5 failures for targeted permissive retry in Phase 1.75.
    let mut phase15_failures: Vec<(String, usize)> = Vec::new(); // (op_name, module_idx)
    for (mod_idx, module) in all_modules.iter().enumerate() {
        for unit in &module.units {
            if let Unit::Operator(def) = &unit.node {
                let op_name = &def.name.node;
                if callee_bodies.contains_key(op_name) {
                    continue;
                }
                if tir_callee_bodies.is_some_and(|callees| callees.contains_key(op_name)) {
                    continue;
                }
                // Use NON-permissive lowering for callee collection: this
                // iterates ALL operators from ALL modules. Permissive lowering
                // on proof modules (TLAPS, SequenceTheorems) causes compilation
                // explosion. Callees that fail here are simply unavailable —
                // Phase 2 target operators handle builtins via permissive lowering.
                match lower_operator_with_env(&env, module, def) {
                    Ok(tir_op) => {
                        callee_bodies.insert(
                            op_name.clone(),
                            tla_tir::bytecode::CalleeInfo {
                                params: tir_op.params,
                                body: Arc::new(tir_op.body),
                                ast_body: Some(tla_tir::nodes::PreservedAstBody(
                                    Arc::new(def.body.clone()),
                                )),
                            },
                        );
                    }
                    Err(e) => {
                        phase15_failures.push((op_name.clone(), mod_idx));
                        if stats_enabled {
                            eprintln!("[bytecode] callee lower failed: {op_name}: {e}");
                        }
                    }
                }
            }
        }
    }
    // Part of #3693: treat TIR-resolved callee bodies as the authoritative
    // root namespace. These bodies come from `TirProgram` seeding and preserve
    // INSTANCE substitution context; raw dep-module lowerings do not.
    if let Some(tir_callees) = tir_callee_bodies {
        let before = callee_bodies.len();
        for (name, info) in tir_callees {
            callee_bodies.insert(name.clone(), info.clone());
        }
        if stats_enabled && callee_bodies.len() > before {
            eprintln!(
                "[bytecode] TIR callee bridge: +{} cross-module operators",
                callee_bodies.len() - before
            );
        }
    }
    // Phase 1.75: Targeted permissive retry for Phase 1.5 failures.
    //
    // Phase 1.5 uses non-permissive TIR lowering to avoid compilation
    // explosion on proof modules. But this means callee operators that use
    // builtins (Append, Head, Tail, etc.) fail to lower, making them
    // unavailable to Phase 2 target operators. Example: Broadcast uses
    // Append, so Request/Exit (which call Broadcast) fail with "unresolved
    // identifier 'Broadcast'".
    //
    // Fix: retry only failed callees that are NOT already resolved (by TIR
    // bridge or Phase 1 pre-compilation), using permissive lowering. This
    // is bounded to the number of Phase 1.5 failures (typically <10), not
    // all operators, so proof module explosion is avoided.
    //
    // Part of #3967: get all split actions to compile for JIT dispatch.
    if !phase15_failures.is_empty() {
        // Phase 1.75: retry failed callees with permissive TIR lowering.
        // The proof-module guard that was here (#3981) was removed because:
        // (1) Only Unit::Operator defs reach this point (Unit::Theorem is
        //     excluded by module_graph.rs), so no proof AST explosion occurs.
        // (2) The guard blocked ALL user-defined operators (Init, Next, TypeOK)
        //     from modules that EXTEND TLAPS, causing 0% JIT hit rate on specs
        //     like MCQuicksort. Individual lowering failures are already handled
        //     gracefully by the Err branch below.
        let mut permissive_recovered = 0usize;
        for (op_name, mod_idx) in &phase15_failures {
            if callee_bodies.contains_key(op_name) {
                continue; // Already resolved by TIR callee bridge
            }
            let module = all_modules[*mod_idx];
            let def = match module.units.iter().find_map(|unit| match &unit.node {
                Unit::Operator(def) if def.name.node == *op_name => Some(def),
                _ => None,
            }) {
                Some(d) => d,
                None => continue,
            };
            match lower_operator_with_env_permissive(&env, module, def) {
                Ok(tir_op) => {
                    callee_bodies.insert(
                        op_name.clone(),
                        tla_tir::bytecode::CalleeInfo {
                            params: tir_op.params,
                            body: Arc::new(tir_op.body),
                            ast_body: Some(tla_tir::nodes::PreservedAstBody(
                                Arc::new(def.body.clone()),
                            )),
                        },
                    );
                    permissive_recovered += 1;
                    if stats_enabled {
                        eprintln!("[bytecode] Phase 1.75: recovered callee '{op_name}' via permissive lowering");
                    }
                }
                Err(e) => {
                    if stats_enabled {
                        eprintln!("[bytecode] Phase 1.75: permissive retry failed for '{op_name}': {e}");
                    }
                }
            }
        }
        if stats_enabled && permissive_recovered > 0 {
            eprintln!(
                "[bytecode] Phase 1.75: recovered {permissive_recovered}/{} failed callees",
                phase15_failures.len()
            );
        }
    }

    if stats_enabled {
        eprintln!(
            "[bytecode] callee bodies collected: {} ({} parameterized)",
            callee_bodies.len(),
            callee_bodies
                .values()
                .filter(|c| !c.params.is_empty())
                .count()
        );
        for name in op_names {
            let in_callees = callee_bodies.contains_key(name);
            let compiled = compiler.has_operator(name);
            if !compiled {
                eprintln!("[bytecode] invariant '{name}' not yet compiled, in callee_bodies: {in_callees}");
            }
        }
    }

    // Phase 2: Compile the requested operators (invariants) with callee
    // resolution. Uses compile_expression_with_callees so that
    // parameterized operator calls (e.g., Before(i,j)) resolve via Call.
    let (chunk, compiler_indices) = {
        for name in op_names {
            if compiler.has_operator(name) {
                continue;
            }
            let (params, body) = if let Some(info) = tir_callee_bodies.and_then(|c| c.get(name)) {
                (info.params.clone(), info.body.clone())
            } else {
                // Fall back to direct module lookup when no namespace-resolved
                // TIR body was exported (e.g. callers using the public helper
                // without a `TirProgram` bridge).
                let (def, owner_module) =
                    match find_operator(root, name).map(|d| (d, root)).or_else(|| {
                        deps.iter()
                            .find_map(|dep| find_operator(dep, name).map(|d| (d, *dep)))
                    }) {
                        Some(pair) => pair,
                        None => {
                            failed.push((
                                name.clone(),
                                CompileError::Unsupported(format!(
                                    "operator '{name}' not found in module"
                                )),
                            ));
                            continue;
                        }
                    };

                // Part of #3967: use permissive lowering for bytecode path.
                let tir_op = match lower_operator_with_env_permissive(&env, owner_module, def) {
                    Ok(op) => op,
                    Err(e) => {
                        failed.push((
                            name.clone(),
                            CompileError::Unsupported(format!("TIR lowering failed: {e}")),
                        ));
                        continue;
                    }
                };
                (tir_op.params, Arc::new(tir_op.body))
            };

            match compiler.compile_expression_with_callees(name, &params, &*body, &callee_bodies) {
                Ok(_) => {}
                Err(e) => {
                    failed.push((name.clone(), e));
                }
            }
        }
        compiler.finish_with_indices()
    };

    // Build op_indices containing only the requested operator names.
    let mut op_indices = FxHashMap::default();
    for name in op_names {
        if let Some(&idx) = compiler_indices.get(name) {
            op_indices.insert(name.clone(), idx);
        }
    }

    CompiledBytecode {
        chunk,
        op_indices,
        failed,
    }
}

/// Find an operator definition by name in a module.
fn find_operator<'a>(module: &'a Module, name: &str) -> Option<&'a tla_core::ast::OperatorDef> {
    use tla_core::ast::Unit;
    module.units.iter().find_map(|unit| match &unit.node {
        Unit::Operator(def) if def.name.node == name => Some(def),
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        collect_bytecode_namespace_callees, compile_operators_to_bytecode_full,
        compile_operators_to_bytecode_with_constants,
    };
    use crate::bytecode_vm::BytecodeVm;
    use tla_core::{lower, parse_to_syntax_tree, FileId};
    use tla_value::Value;

    fn parse_module(src: &str) -> tla_core::ast::Module {
        let tree = parse_to_syntax_tree(src);
        let result = lower(FileId(0), &tree);
        result.module.expect("module should lower")
    }

    #[test]
    fn test_compile_operators_to_bytecode_injects_stdlib_constants() {
        let module = parse_module(
            "\
---- MODULE BytecodeStdlibCompile3585 ----
Check == 1 \\in Nat /\\ 1 \\in Int /\\ TRUE \\in BOOLEAN /\\ \"hello\" \\in STRING
====",
        );

        let compiled = compile_operators_to_bytecode_with_constants(
            &module,
            &[],
            &["Check".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "stdlib-backed operator should compile without unresolved identifiers: {:?}",
            compiled.failed
        );
        assert!(
            compiled.op_indices.contains_key("Check"),
            "Check should compile to bytecode"
        );
    }

    #[test]
    fn test_compile_full_uses_instance_resolved_entry_and_callees() {
        let inner = parse_module(
            "\
---- MODULE BytecodeInstanceInner3693 ----
CONSTANT K
Helper == K
MyVal == Helper + 1
====",
        );
        let wrapper = parse_module(
            "\
---- MODULE BytecodeInstanceWrapper3693 ----
Nodes == 41
INSTANCE BytecodeInstanceInner3693 WITH K <- Nodes
====",
        );
        let dep_refs = [&inner];
        let tir_callees = collect_bytecode_namespace_callees(&wrapper, &dep_refs);

        let compiled = compile_operators_to_bytecode_full(
            &wrapper,
            &dep_refs,
            &["MyVal".to_string()],
            &crate::HashMap::default(),
            None,
            Some(&tir_callees),
        );

        assert!(
            compiled.failed.is_empty(),
            "INSTANCE-imported operator should compile through the public bytecode API: {:?}",
            compiled.failed
        );
        let func_idx = *compiled
            .op_indices
            .get("MyVal")
            .expect("INSTANCE-imported MyVal should be compiled");
        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let value = vm
            .execute_function(func_idx)
            .expect("compiled INSTANCE-imported operator should execute");
        assert_eq!(
            value,
            Value::int(42),
            "entry operator and imported helper must both keep INSTANCE substitution context",
        );
    }

    #[test]
    fn test_compile_with_constants_uses_instance_resolved_namespace() {
        let inner = parse_module(
            "\
---- MODULE BytecodeInstanceInner3693Simple ----
CONSTANT K
Helper == K
MyVal == Helper + 1
====",
        );
        let wrapper = parse_module(
            "\
---- MODULE BytecodeInstanceWrapper3693Simple ----
Nodes == 41
INSTANCE BytecodeInstanceInner3693Simple WITH K <- Nodes
====",
        );
        let dep_refs = [&inner];

        let compiled = compile_operators_to_bytecode_with_constants(
            &wrapper,
            &dep_refs,
            &["MyVal".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "simple public bytecode helper should compile INSTANCE-imported operators: {:?}",
            compiled.failed
        );
        let func_idx = *compiled
            .op_indices
            .get("MyVal")
            .expect("INSTANCE-imported MyVal should be compiled");
        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let value = vm
            .execute_function(func_idx)
            .expect("compiled INSTANCE-imported operator should execute");
        assert_eq!(
            value,
            Value::int(42),
            "public helper must preserve INSTANCE substitution context",
        );
    }

    /// Part of #3789: transitive INSTANCE chain with 3-deep dependency.
    ///
    /// Inner: CONSTANT K, Base == K, Mid == Base + 10, Top == Mid * 2
    /// Wrapper: N == 5, INSTANCE Inner WITH K <- N
    ///
    /// Expected: Base=5, Mid=15, Top=30
    #[test]
    fn test_cross_module_transitive_chain_executes_correctly() {
        let inner = parse_module(
            "\
---- MODULE BytecodeCrossModuleTransitive3789 ----
CONSTANT K
Base == K
Mid == Base + 10
Top == Mid * 2
====",
        );
        let wrapper = parse_module(
            "\
---- MODULE BytecodeCrossModuleWrapper3789 ----
N == 5
INSTANCE BytecodeCrossModuleTransitive3789 WITH K <- N
====",
        );
        let dep_refs = [&inner];
        let compiled = compile_operators_to_bytecode_with_constants(
            &wrapper,
            &dep_refs,
            &["Top".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "3-deep transitive INSTANCE chain should compile: {:?}",
            compiled.failed
        );
        let func_idx = *compiled
            .op_indices
            .get("Top")
            .expect("Top should be compiled");
        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let value = vm
            .execute_function(func_idx)
            .expect("transitive chain should execute without CallExternal");
        assert_eq!(value, Value::int(30), "K=5, Base=5, Mid=15, Top=30");
    }

    /// Part of #3693: named INSTANCE with `I == INSTANCE M WITH ...`.
    ///
    /// When an operator body is `INSTANCE M WITH ...`, the wrapper exposes the
    /// imported operators' sibling references. This test verifies that the
    /// bytecode compiler resolves these through the TIR callee bridge rather
    /// than falling back to CallExternal.
    #[test]
    fn test_named_instance_operator_compiles_to_call() {
        let inner = parse_module(
            "\
---- MODULE BytecodeNamedInstanceInner3693 ----
CONSTANT K
Base == K
Derived == Base + 100
====",
        );
        let wrapper = parse_module(
            "\
---- MODULE BytecodeNamedInstanceWrapper3693 ----
I == INSTANCE BytecodeNamedInstanceInner3693 WITH K <- 7
Result == I!Derived
====",
        );
        let dep_refs = [&inner];
        let compiled = compile_operators_to_bytecode_with_constants(
            &wrapper,
            &dep_refs,
            &["Result".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "named INSTANCE operator (I!Derived) should compile: {:?}",
            compiled.failed
        );
        let func_idx = *compiled
            .op_indices
            .get("Result")
            .expect("Result should be compiled");
        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let value = vm
            .execute_function(func_idx)
            .expect("named INSTANCE operator should execute in bytecode VM");
        assert_eq!(
            value,
            Value::int(107),
            "I!Derived with K=7: Base=7, Derived=107"
        );
    }

    /// Part of #3693: named INSTANCE with parameterized operator.
    ///
    /// Tests `I == INSTANCE M WITH ...` where the imported operator is
    /// parameterized: `I!Scale(arg)` compiles to a Call, not CallExternal.
    #[test]
    fn test_named_instance_parameterized_operator_compiles() {
        let inner = parse_module(
            "\
---- MODULE BytecodeNamedInstanceParam3693 ----
CONSTANT K
Scale(x) == x * K
====",
        );
        let wrapper = parse_module(
            "\
---- MODULE BytecodeNamedInstanceParamWrapper3693 ----
I == INSTANCE BytecodeNamedInstanceParam3693 WITH K <- 5
Result == I!Scale(8)
====",
        );
        let dep_refs = [&inner];
        let compiled = compile_operators_to_bytecode_with_constants(
            &wrapper,
            &dep_refs,
            &["Result".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "named INSTANCE parameterized operator should compile: {:?}",
            compiled.failed
        );
        let func_idx = *compiled
            .op_indices
            .get("Result")
            .expect("Result should be compiled");
        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let value = vm
            .execute_function(func_idx)
            .expect("named INSTANCE parameterized operator should execute");
        assert_eq!(value, Value::int(40), "I!Scale(8) with K=5 should be 40");
    }

    /// Part of #3693: multiple INSTANCE imports, both named and unnamed.
    ///
    /// Verifies that the bytecode compiler handles both import patterns
    /// simultaneously without namespace collisions.
    #[test]
    fn test_mixed_named_unnamed_instance_compiles() {
        let inner_a = parse_module(
            "\
---- MODULE BytecodeMixedInnerA3693 ----
CONSTANT K
ValA == K + 1
====",
        );
        let inner_b = parse_module(
            "\
---- MODULE BytecodeMixedInnerB3693 ----
CONSTANT K
ValB == K + 2
====",
        );
        let wrapper = parse_module(
            "\
---- MODULE BytecodeMixedWrapper3693 ----
INSTANCE BytecodeMixedInnerA3693 WITH K <- 10
B == INSTANCE BytecodeMixedInnerB3693 WITH K <- 20
Result == ValA + B!ValB
====",
        );
        let dep_refs = [&inner_a, &inner_b];
        let compiled = compile_operators_to_bytecode_with_constants(
            &wrapper,
            &dep_refs,
            &["Result".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "mixed named/unnamed INSTANCE should compile: {:?}",
            compiled.failed
        );
        let func_idx = *compiled
            .op_indices
            .get("Result")
            .expect("Result should be compiled");
        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let value = vm
            .execute_function(func_idx)
            .expect("mixed INSTANCE should execute");
        assert_eq!(
            value,
            Value::int(33),
            "ValA (K=10 -> 11) + B!ValB (K=20 -> 22) = 33"
        );
    }

    /// Part of #3789: parameterized operator from INSTANCE module.
    ///
    /// Inner: CONSTANT K, Scale(x) == x * K
    /// Wrapper: Factor == 3, INSTANCE Inner WITH K <- Factor
    /// Entry: Scale(7) should equal 21
    #[test]
    fn test_cross_module_parameterized_operator_compiles() {
        let inner = parse_module(
            "\
---- MODULE BytecodeCrossModuleParam3789 ----
CONSTANT K
Scale(x) == x * K
====",
        );
        let wrapper = parse_module(
            "\
---- MODULE BytecodeCrossModuleParamWrapper3789 ----
Factor == 3
INSTANCE BytecodeCrossModuleParam3789 WITH K <- Factor
Result == Scale(7)
====",
        );
        let dep_refs = [&inner];
        let compiled = compile_operators_to_bytecode_with_constants(
            &wrapper,
            &dep_refs,
            &["Result".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "parameterized INSTANCE operator should compile: {:?}",
            compiled.failed
        );
        let func_idx = *compiled
            .op_indices
            .get("Result")
            .expect("Result should be compiled");
        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let value = vm
            .execute_function(func_idx)
            .expect("parameterized cross-module call should execute");
        assert_eq!(
            value,
            Value::int(21),
            "Scale(7) with K=Factor=3 should be 21"
        );
    }

    /// Part of #3789: stdlib operators that pass through TIR lowering compile
    /// to dedicated bytecode opcodes (Concat for \o, CallBuiltin for
    /// IsFiniteSet).
    ///
    /// Note: Since #3967, Len/Head/Tail/Append/Cardinality/SubSeq also
    /// compile via permissive TIR lowering to CallBuiltin opcodes. See
    /// `test_parameterized_builtins_compile_via_permissive_lowering`.
    #[test]
    fn test_stdlib_operators_compile_to_dedicated_opcodes() {
        let module = parse_module(
            "\
---- MODULE BytecodeStdlibOps3789 ----
EXTENDS FiniteSets
IsFinResult == IsFiniteSet({1, 2})
ConcatResult == <<1, 2>> \\o <<3, 4>>
====",
        );

        let op_names: Vec<String> = ["IsFinResult", "ConcatResult"]
            .iter()
            .map(|s| s.to_string())
            .collect();

        let compiled = compile_operators_to_bytecode_with_constants(
            &module,
            &[],
            &op_names,
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "stdlib operators should compile: {:?}",
            compiled.failed
        );

        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);

        // IsFiniteSet({1, 2}) == TRUE
        let idx = *compiled
            .op_indices
            .get("IsFinResult")
            .expect("IsFinResult compiled");
        assert_eq!(
            vm.execute_function(idx).expect("IsFiniteSet"),
            Value::Bool(true)
        );

        // <<1, 2>> \o <<3, 4>> == <<1, 2, 3, 4>>
        let idx = *compiled
            .op_indices
            .get("ConcatResult")
            .expect("ConcatResult compiled");
        assert_eq!(
            vm.execute_function(idx).expect("Concat"),
            Value::seq(vec![
                Value::int(1),
                Value::int(2),
                Value::int(3),
                Value::int(4)
            ])
        );
    }

    /// Part of #3967: parameterized builtins (Len, Head, Tail, Append,
    /// Cardinality, SubSeq, Seq) now compile to CallBuiltin opcodes via
    /// permissive TIR lowering. Previously these were rejected by
    /// `is_unsupported_parameterized_builtin_name` in the TIR lowerer, blocking
    /// bytecode compilation (and thus JIT) for any spec using them.
    #[test]
    fn test_parameterized_builtins_compile_via_permissive_lowering() {
        let module = parse_module(
            "\
---- MODULE BytecodeBuiltins3967 ----
EXTENDS Sequences, FiniteSets
LenResult == Len(<<10, 20, 30>>)
HeadResult == Head(<<10, 20, 30>>)
TailResult == Tail(<<10, 20, 30>>)
AppendResult == Append(<<1, 2>>, 3)
CardResult == Cardinality({\"a\", \"b\", \"c\"})
SubSeqResult == SubSeq(<<10, 20, 30, 40>>, 2, 3)
====",
        );

        let op_names: Vec<String> = [
            "LenResult",
            "HeadResult",
            "TailResult",
            "AppendResult",
            "CardResult",
            "SubSeqResult",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();

        let compiled = compile_operators_to_bytecode_with_constants(
            &module,
            &[],
            &op_names,
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "all parameterized builtins should compile via permissive lowering: {:?}",
            compiled.failed
        );

        // Verify all operators compiled.
        for name in &op_names {
            assert!(
                compiled.op_indices.contains_key(name),
                "{name} should be in compiled op_indices"
            );
        }

        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);

        // Len(<<10, 20, 30>>) == 3
        let idx = *compiled.op_indices.get("LenResult").expect("LenResult");
        assert_eq!(vm.execute_function(idx).expect("Len"), Value::int(3));

        // Head(<<10, 20, 30>>) == 10
        let idx = *compiled.op_indices.get("HeadResult").expect("HeadResult");
        assert_eq!(vm.execute_function(idx).expect("Head"), Value::int(10));

        // Tail(<<10, 20, 30>>) == <<20, 30>>
        let idx = *compiled.op_indices.get("TailResult").expect("TailResult");
        assert_eq!(
            vm.execute_function(idx).expect("Tail"),
            Value::seq(vec![Value::int(20), Value::int(30)])
        );

        // Append(<<1, 2>>, 3) == <<1, 2, 3>>
        let idx = *compiled
            .op_indices
            .get("AppendResult")
            .expect("AppendResult");
        assert_eq!(
            vm.execute_function(idx).expect("Append"),
            Value::seq(vec![Value::int(1), Value::int(2), Value::int(3)])
        );

        // Cardinality({"a", "b", "c"}) == 3
        let idx = *compiled.op_indices.get("CardResult").expect("CardResult");
        assert_eq!(
            vm.execute_function(idx).expect("Cardinality"),
            Value::int(3)
        );

        // SubSeq(<<10, 20, 30, 40>>, 2, 3) == <<20, 30>>
        let idx = *compiled
            .op_indices
            .get("SubSeqResult")
            .expect("SubSeqResult");
        assert_eq!(
            vm.execute_function(idx).expect("SubSeq"),
            Value::seq(vec![Value::int(20), Value::int(30)])
        );
    }

    /// Part of #3972: A parameterized callee using a builtin (Append) should
    /// compile when called from a target operator. This tests the Phase 1.75
    /// permissive retry path: Phase 1.5 fails on Helper because of Append,
    /// Phase 1.75 retries it with permissive lowering and recovers it.
    #[test]
    fn test_parameterized_callee_using_builtin_compiles_via_phase175() {
        let module = parse_module(
            "\
---- MODULE BytecodeBroadcastCallee3972 ----
EXTENDS Sequences
Helper(s, e) == Append(s, e)
Entry == Helper(<<1, 2>>, 3)
====",
        );

        let compiled = compile_operators_to_bytecode_with_constants(
            &module,
            &[],
            &["Entry".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "parameterized callee using Append should compile via Phase 1.75: {:?}",
            compiled.failed
        );
        assert!(
            compiled.op_indices.contains_key("Entry"),
            "Entry should be in compiled op_indices"
        );

        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let idx = *compiled
            .op_indices
            .get("Entry")
            .expect("Entry compiled");
        let result = vm
            .execute_function(idx)
            .expect("Entry should execute");
        assert_eq!(
            result,
            Value::seq(vec![Value::int(1), Value::int(2), Value::int(3)]),
            "Helper(<<1, 2>>, 3) should produce <<1, 2, 3>>"
        );
    }

    /// Part of #3967: Seq(S) builtin compiles to CallBuiltin and returns
    /// a SeqSet value representing the set of all finite sequences over S.
    #[test]
    fn test_seq_builtin_compiles_to_call_builtin() {
        let module = parse_module(
            "\
---- MODULE BytecodeSeqBuiltin3967 ----
EXTENDS Sequences
SeqResult == <<1, 2>> \\in Seq({1, 2, 3})
====",
        );

        let compiled = compile_operators_to_bytecode_with_constants(
            &module,
            &[],
            &["SeqResult".to_string()],
            &crate::HashMap::default(),
        );

        assert!(
            compiled.failed.is_empty(),
            "Seq builtin should compile via permissive lowering: {:?}",
            compiled.failed
        );
        assert!(
            compiled.op_indices.contains_key("SeqResult"),
            "SeqResult should be in compiled op_indices"
        );

        let mut vm = BytecodeVm::new(&compiled.chunk, &[], None);
        let idx = *compiled
            .op_indices
            .get("SeqResult")
            .expect("SeqResult");
        // <<1, 2>> \in Seq({1, 2, 3}) should be TRUE
        let result = vm.execute_function(idx).expect("Seq membership check");
        assert_eq!(
            result,
            Value::Bool(true),
            "<<1, 2>> should be in Seq({{1, 2, 3}})"
        );
    }
}
