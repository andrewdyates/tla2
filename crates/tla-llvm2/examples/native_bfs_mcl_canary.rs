// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded native fused BFS canary for the MCL-sized parent-loop shape.
//!
//! Part of #4372.

#[cfg(not(feature = "native"))]
fn main() {
    eprintln!("native_bfs_mcl_canary requires `--features native`");
}

#[cfg(feature = "native")]
fn main() {
    native::run();
}

#[cfg(feature = "native")]
mod native {
    use std::ffi::OsString;

    use tla_llvm2::{
        compile_bfs_level_native_actions_only, compile_module_native, ActionDescriptor,
        Llvm2BfsLevelNativeAction, Llvm2SuccessorArena, OptLevel,
    };
    use tmir::constant::Constant;
    use tmir::inst::{BinOp, Inst};
    use tmir::ty::{FuncTy, Ty};
    use tmir::value::{BlockId, FuncId, StructId, ValueId};
    use tmir::{Block, FieldDef, Function, InstrNode, Module, StructDef};

    const STATE_LEN: usize = 89;
    const ACTION_COUNT: usize = 27;
    const PARENT_COUNT: usize = 4;
    const ACTION_VALUE_BASE: i64 = 10_000;
    const LOCAL_DEDUP_DISABLE_ENV: &str = "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP";

    struct EnvGuard {
        key: &'static str,
        old: Option<OsString>,
    }

    impl EnvGuard {
        fn set(key: &'static str, value: &str) -> Self {
            let old = std::env::var_os(key);
            std::env::set_var(key, value);
            Self { key, old }
        }
    }

    impl Drop for EnvGuard {
        fn drop(&mut self) {
            match &self.old {
                Some(value) => std::env::set_var(self.key, value),
                None => std::env::remove_var(self.key),
            }
        }
    }

    fn jit_callout_struct(id: StructId) -> StructDef {
        StructDef {
            id,
            name: "JitCallOut".to_string(),
            fields: vec![
                FieldDef {
                    name: "status".to_string(),
                    ty: Ty::U8,
                    offset: None,
                },
                FieldDef {
                    name: "value".to_string(),
                    ty: Ty::I64,
                    offset: None,
                },
                FieldDef {
                    name: "err_kind".to_string(),
                    ty: Ty::U8,
                    offset: None,
                },
                FieldDef {
                    name: "err_span_start".to_string(),
                    ty: Ty::U32,
                    offset: None,
                },
                FieldDef {
                    name: "err_span_end".to_string(),
                    ty: Ty::U32,
                    offset: None,
                },
                FieldDef {
                    name: "err_file_id".to_string(),
                    ty: Ty::U32,
                    offset: None,
                },
                FieldDef {
                    name: "conjuncts_passed".to_string(),
                    ty: Ty::U32,
                    offset: None,
                },
            ],
            size: None,
            align: None,
        }
    }

    fn push_const(block: &mut Block, next: &mut u32, ty: Ty, value: i128) -> ValueId {
        let result = ValueId::new(*next);
        *next += 1;
        block.body.push(
            InstrNode::new(Inst::Const {
                ty,
                value: Constant::Int(value),
            })
            .with_result(result),
        );
        result
    }

    fn push_i64_gep(block: &mut Block, next: &mut u32, base: ValueId, index: usize) -> ValueId {
        let index = push_const(block, next, Ty::I64, index as i128);
        let result = ValueId::new(*next);
        *next += 1;
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![index],
            })
            .with_result(result),
        );
        result
    }

    fn push_i64_load(block: &mut Block, next: &mut u32, ptr: ValueId) -> ValueId {
        let result = ValueId::new(*next);
        *next += 1;
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr,
                volatile: false,
                align: None,
            })
            .with_result(result),
        );
        result
    }

    fn push_i64_add(block: &mut Block, next: &mut u32, lhs: ValueId, rhs: ValueId) -> ValueId {
        let result = ValueId::new(*next);
        *next += 1;
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs,
                rhs,
            })
            .with_result(result),
        );
        result
    }

    fn push_i64_store(block: &mut Block, ptr: ValueId, value: ValueId) {
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr,
            value,
            volatile: false,
            align: None,
        }));
    }

    fn make_mcl_sized_action_module() -> Module {
        let mut module = Module::new("native_bfs_mcl_many_actions_canary");
        let callout = StructId::new(0);
        module.add_struct(jit_callout_struct(callout));
        let action_ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32],
            returns: vec![],
            is_vararg: false,
        });

        for action_idx in 0..ACTION_COUNT {
            let symbol = action_symbol(action_idx);
            let entry = BlockId::new(action_idx as u32);
            let mut func = Function::new(FuncId::new(action_idx as u32), symbol, action_ft, entry);
            let mut block = Block::new(entry)
                .with_param(ValueId::new(0), Ty::Ptr)
                .with_param(ValueId::new(1), Ty::Ptr)
                .with_param(ValueId::new(2), Ty::Ptr)
                .with_param(ValueId::new(3), Ty::U32);
            let mut next = 4;

            let ok = push_const(&mut block, &mut next, Ty::U8, 0);
            let status_write = ValueId::new(next);
            next += 1;
            block.body.push(
                InstrNode::new(Inst::InsertField {
                    ty: Ty::Struct(callout),
                    aggregate: ValueId::new(0),
                    field: 0,
                    value: ok,
                })
                .with_result(status_write),
            );

            let enabled = push_const(&mut block, &mut next, Ty::I64, 1);
            let value_write = ValueId::new(next);
            next += 1;
            block.body.push(
                InstrNode::new(Inst::InsertField {
                    ty: Ty::Struct(callout),
                    aggregate: ValueId::new(0),
                    field: 1,
                    value: enabled,
                })
                .with_result(value_write),
            );

            let parent_slot0_ptr = push_i64_gep(&mut block, &mut next, ValueId::new(1), 0);
            let parent_slot0 = push_i64_load(&mut block, &mut next, parent_slot0_ptr);
            let action_delta = push_const(
                &mut block,
                &mut next,
                Ty::I64,
                i128::from(ACTION_VALUE_BASE + action_idx as i64),
            );
            let action_value = push_i64_add(&mut block, &mut next, parent_slot0, action_delta);
            let target_ptr = push_i64_gep(
                &mut block,
                &mut next,
                ValueId::new(2),
                action_slot(action_idx),
            );
            push_i64_store(&mut block, target_ptr, action_value);

            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module.add_function(func);
        }

        module
    }

    fn action_symbol(action_idx: usize) -> String {
        format!("mcl_many_action_{action_idx}")
    }

    fn action_slot(action_idx: usize) -> usize {
        2 + action_idx * 3
    }

    fn make_parents() -> Vec<i64> {
        let mut parents = Vec::with_capacity(PARENT_COUNT * STATE_LEN);
        for parent_idx in 0..PARENT_COUNT {
            for slot in 0..STATE_LEN {
                parents.push(1_000 + parent_idx as i64 * 100 + slot as i64);
            }
        }
        parents
    }

    pub fn run() {
        eprintln!("[native_bfs_mcl_canary] compiling action module opt=O1 actions={ACTION_COUNT}");
        let action_lib = compile_module_native(&make_mcl_sized_action_module(), OptLevel::O1)
            .expect("compile MCL-sized action canary");
        eprintln!("[native_bfs_mcl_canary] action module compiled");
        let actions: Vec<_> = (0..ACTION_COUNT)
            .map(|action_idx| {
                Llvm2BfsLevelNativeAction::new(
                    ActionDescriptor {
                        name: action_symbol(action_idx),
                        action_idx: action_idx as u32,
                        binding_values: vec![action_idx as i64],
                        formal_values: vec![action_idx as i64],
                        read_vars: (0..STATE_LEN as u16).collect(),
                        write_vars: vec![action_slot(action_idx) as u16],
                    },
                    action_lib.clone(),
                    action_symbol(action_idx),
                )
            })
            .collect();

        let _dedup_guard = EnvGuard::set(LOCAL_DEDUP_DISABLE_ENV, "1");
        eprintln!(
            "[native_bfs_mcl_canary] compiling native fused parent loop opt=O1 state_len={STATE_LEN} actions={ACTION_COUNT}"
        );
        let mut level = compile_bfs_level_native_actions_only(STATE_LEN, &actions, OptLevel::O1)
            .expect("compile native fused parent loop");
        eprintln!(
            "[native_bfs_mcl_canary] parent loop compiled local_dedup={}",
            level.metadata().local_dedup
        );
        assert!(level.capabilities().native_fused_loop);
        assert!(!level.metadata().local_dedup);
        assert!(!level.capabilities().local_dedup);
        assert_eq!(level.state_len(), STATE_LEN);
        assert_eq!(level.action_count(), ACTION_COUNT);

        let parents = make_parents();
        let mut out = Llvm2SuccessorArena::new(STATE_LEN);
        eprintln!(
            "[native_bfs_mcl_canary] running native fused parent loop parents={PARENT_COUNT}"
        );
        let outcome = level
            .run_level_arena(&parents, PARENT_COUNT, &mut out)
            .expect("run native fused parent loop");
        eprintln!(
            "[native_bfs_mcl_canary] native fused parent loop returned generated={} new={}",
            outcome.total_generated, outcome.total_new
        );

        let expected_successors = PARENT_COUNT * ACTION_COUNT;
        assert_eq!(outcome.parents_processed, PARENT_COUNT);
        assert_eq!(outcome.total_generated, expected_successors as u64);
        assert_eq!(outcome.total_new, expected_successors as u64);
        assert_eq!(out.successor_count(), expected_successors);

        let mut seen = vec![vec![false; ACTION_COUNT]; PARENT_COUNT];
        for successor in out.states_flat().chunks_exact(STATE_LEN) {
            let parent_idx = ((successor[0] - 1_000) / 100) as usize;
            assert!(
                parent_idx < PARENT_COUNT,
                "successor has invalid parent marker in slot 0: {successor:?}"
            );
            let parent = &parents[parent_idx * STATE_LEN..(parent_idx + 1) * STATE_LEN];
            let diffs: Vec<_> = successor
                .iter()
                .zip(parent.iter())
                .enumerate()
                .filter_map(|(slot, (actual, expected))| (actual != expected).then_some(slot))
                .collect();
            assert_eq!(
                diffs.len(),
                1,
                "candidate should be copied from its parent with exactly one action mutation"
            );

            let changed_slot = diffs[0];
            assert!(
                changed_slot >= 2 && (changed_slot - 2) % 3 == 0,
                "unexpected action mutation slot {changed_slot}"
            );
            let action_idx = (changed_slot - 2) / 3;
            assert!(
                action_idx < ACTION_COUNT,
                "unexpected action index inferred from slot {changed_slot}"
            );
            assert_eq!(
                successor[changed_slot],
                parent[0] + ACTION_VALUE_BASE + action_idx as i64
            );
            assert!(
                !seen[parent_idx][action_idx],
                "duplicate successor for parent {parent_idx}, action {action_idx}"
            );
            seen[parent_idx][action_idx] = true;
        }

        assert!(
            seen.iter().flatten().all(|present| *present),
            "native fused parent loop did not emit every parent/action successor"
        );
        println!(
        "native BFS MCL canary passed: state_len={STATE_LEN}, actions={ACTION_COUNT}, parents={PARENT_COUNT}"
    );
    }
}
