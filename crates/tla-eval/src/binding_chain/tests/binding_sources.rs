// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Binding source tests: cons_with_deps (Instance), cons_local (Local),
//! update_head_value, and instance/local interaction patterns.

use super::super::*;
use tla_core::name_intern::intern_name;
use tla_value::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cons_with_deps() {
    use super::super::super::{OpEvalDeps, VarDepMap};
    use tla_core::VarIndex;

    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_deps_x");
    let y_id = intern_name("test_bc_deps_y");

    // Create deps simulating an INSTANCE substitution that reads a state var
    let deps = OpEvalDeps {
        local: smallvec::smallvec![],
        state: VarDepMap::from_entries(&[(VarIndex::new(0), Value::int(10))]),
        next: VarDepMap::default(),
        inconsistent: false,
        ..Default::default()
    };

    // cons_with_deps attaches INSTANCE dependency info
    let chain = chain.cons_with_deps(x_id, BindingValue::eager(Value::int(7)), deps);
    // cons without deps for comparison
    let chain = chain.cons(y_id, BindingValue::eager(Value::int(8)));

    // y has BindingSource::None (plain cons)
    let (bv_y, source_y) = chain.lookup(y_id).unwrap();
    assert!(matches!(source_y, BindingSourceRef::None));
    match bv_y {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(8)),
        _ => panic!("expected Eager"),
    }

    // x has BindingSource::Instance with state var dep
    let (bv_x, source_x) = chain.lookup(x_id).unwrap();
    match source_x {
        BindingSourceRef::Instance(deps) => {
            assert!(deps.state.contains_key(&VarIndex::new(0)));
            assert!(!deps.inconsistent);
        }
        _ => panic!("expected BindingSource::Instance"),
    }
    match bv_x {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(7)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cons_local() {
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_local_x");

    // cons_local attaches stack index
    let chain = chain.cons_local(x_id, BindingValue::eager(Value::int(5)), 3);

    let (bv, source) = chain.lookup(x_id).unwrap();
    match source {
        BindingSourceRef::Local(idx) => assert_eq!(idx, 3),
        _ => panic!("expected BindingSource::Local"),
    }
    match bv {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(5)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_level_instance_simulation() {
    // Simulate 3-level INSTANCE nesting like EWD998ChanID -> EWD998Chan -> EWD998
    let chain = BindingChain::empty();

    // Level 1: EWD998 substitutions (e.g., Node <- Node, Initiator <- Initiator)
    let node_id = intern_name("test_bc_inst_Node");
    let init_id = intern_name("test_bc_inst_Initiator");
    let chain = chain.cons(node_id, BindingValue::eager(Value::int(3)));
    let chain = chain.cons(init_id, BindingValue::eager(Value::int(0)));

    // Level 2: EWD998Chan adds more substitutions
    let chan_id = intern_name("test_bc_inst_channel");
    let chain = chain.cons(chan_id, BindingValue::eager(Value::Bool(true)));

    // Level 3: EWD998ChanID adds final substitutions
    let id_id = intern_name("test_bc_inst_id_func");
    let chain = chain.cons(id_id, BindingValue::eager(Value::int(42)));

    // Total depth: 4
    assert_eq!(chain.depth(), 4);

    // All bindings accessible
    match chain.lookup(node_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(3)),
        _ => panic!("expected Eager"),
    }
    match chain.lookup(id_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(42)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_update_head_value_replaces_value() {
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_upd_x");
    let y_id = intern_name("test_bc_upd_y");

    // Build chain: y(10) -> x(1)
    let chain = chain.cons(x_id, BindingValue::eager(Value::int(1)));
    let mut chain = chain.cons(y_id, BindingValue::eager(Value::int(10)));
    assert_eq!(chain.depth(), 2);

    // Update head (y) from 10 to 99
    chain.update_head_value(BindingValue::eager(Value::int(99)));

    // Head value is updated
    match chain.lookup(y_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(99)),
        _ => panic!("expected Eager"),
    }
    // Tail is preserved -- x still has its original value
    match chain.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(1)),
        _ => panic!("expected Eager"),
    }
    // Depth unchanged
    assert_eq!(chain.depth(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_update_head_value_empty_chain_is_noop() {
    let mut chain = BindingChain::empty();
    assert!(chain.is_empty());

    // update_head_value on empty chain should be a no-op (not panic)
    chain.update_head_value(BindingValue::eager(Value::int(42)));

    // Chain is still empty -- value was silently dropped
    assert!(chain.is_empty());
    assert_eq!(chain.depth(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_update_head_value_preserves_source_metadata() {
    use super::super::super::OpEvalDeps;
    use crate::cache::VarDepMap;
    use tla_core::VarIndex;

    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_upd_src_x");

    // Create an INSTANCE binding with deps
    let deps = OpEvalDeps {
        local: smallvec::smallvec![],
        state: VarDepMap::from_entries(&[(VarIndex::new(0), Value::int(7))]),
        next: VarDepMap::default(),
        inconsistent: false,
        ..Default::default()
    };
    let mut chain = chain.cons_with_deps(x_id, BindingValue::eager(Value::int(1)), deps);

    // Update head value
    chain.update_head_value(BindingValue::eager(Value::int(999)));

    // Value is updated
    let (bv, source) = chain.lookup(x_id).unwrap();
    match bv {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(999)),
        _ => panic!("expected Eager"),
    }
    // Source metadata (Instance deps) is preserved
    match source {
        BindingSourceRef::Instance(deps) => {
            assert!(deps.state.contains_key(&VarIndex::new(0)));
        }
        _ => panic!("expected BindingSource::Instance -- source must be preserved after update"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_rebind_recursive_param_reuses_param_head() {
    let param_id = intern_name("test_bc_recursive_param");
    let self_name = "test_bc_recursive_self";
    let self_id = intern_name(self_name);
    let captured_id = intern_name("test_bc_recursive_captured");

    let chain = BindingChain::empty().cons(captured_id, BindingValue::eager(Value::int(5)));
    let chain = chain.cons_local(self_id, BindingValue::eager(Value::int(99)), 0);
    let mut chain = chain.cons_local(param_id, BindingValue::eager(Value::int(1)), 1);

    assert!(chain.try_rebind_recursive_param(param_id, self_id, Value::int(2)));
    assert_eq!(chain.depth(), 3);

    match chain.lookup(param_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(2)),
        _ => panic!("expected Eager"),
    }
    match chain.lookup(self_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(99)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_rebind_recursive_param_rejects_intervening_scope() {
    let param_id = intern_name("test_bc_recursive_guard_param");
    let self_name = "test_bc_recursive_guard_self";
    let self_id = intern_name(self_name);

    let chain = BindingChain::empty().cons_local(self_id, BindingValue::eager(Value::int(99)), 0);
    let chain = chain.cons_local(param_id, BindingValue::eager(Value::int(1)), 1);
    let mut chain = chain.cons_local(param_id, BindingValue::eager(Value::int(100)), 2);

    assert!(!chain.try_rebind_recursive_param(param_id, self_id, Value::int(2)));
    assert_eq!(chain.depth(), 3);

    match chain.lookup(param_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(100)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_instance_then_local_lookup_finds_local_first() {
    use super::super::super::OpEvalDeps;

    // Simulate production pattern: INSTANCE subs first, then local bindings stacked on top
    let chain = BindingChain::empty();
    let n_id = intern_name("test_bc_mixed_N");
    let i_id = intern_name("test_bc_mixed_i");

    // First: INSTANCE substitution for N (deeper in chain)
    let deps = OpEvalDeps::default();
    let chain = chain.cons_with_deps(n_id, BindingValue::eager(Value::int(3)), deps);

    // Then: local quantifier binding for i (head of chain)
    let chain = chain.cons_local(i_id, BindingValue::eager(Value::int(0)), 5);

    // Lookup local binding (head) -- should find immediately
    let (bv_i, source_i) = chain.lookup(i_id).unwrap();
    match source_i {
        BindingSourceRef::Local(idx) => assert_eq!(idx, 5),
        _ => panic!("expected Local source for quantifier var"),
    }
    match bv_i {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(0)),
        _ => panic!("expected Eager"),
    }

    // Lookup INSTANCE binding (deeper) -- should walk past local node
    let (bv_n, source_n) = chain.lookup(n_id).unwrap();
    match source_n {
        BindingSourceRef::Instance(_) => {} // correct
        _ => panic!("expected Instance source for INSTANCE substitution"),
    }
    match bv_n {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(3)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_local_shadows_instance_same_name() {
    use super::super::super::OpEvalDeps;

    // If a local binding uses the same name as an INSTANCE binding,
    // the local (newer) should shadow the INSTANCE (older)
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_shadow_inst_x");

    // INSTANCE binding: x = 100
    let deps = OpEvalDeps::default();
    let chain = chain.cons_with_deps(x_id, BindingValue::eager(Value::int(100)), deps);

    // Local binding: x = 0 (shadows INSTANCE)
    let chain = chain.cons_local(x_id, BindingValue::eager(Value::int(0)), 1);

    // Lookup should find the local (shadowing) binding
    let (bv, source) = chain.lookup(x_id).unwrap();
    match source {
        BindingSourceRef::Local(idx) => assert_eq!(idx, 1),
        _ => panic!("expected Local source -- local should shadow INSTANCE"),
    }
    match bv {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(0)),
        _ => panic!("expected Eager with value 0, not 100"),
    }
}
