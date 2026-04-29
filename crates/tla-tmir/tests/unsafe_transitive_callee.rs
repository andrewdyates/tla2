// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_tir::bytecode::action_transform::{transform_action_to_next_state, ActionTransformOutcome};
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};
use tla_tmir::lower::lower_entry_next_state_with_chunk;

fn rewritten_entry_calling(op_idx: u16) -> BytecodeFunction {
    let mut entry = BytecodeFunction::new("entry".to_string(), 0);
    entry.emit(Opcode::Call {
        rd: 0,
        op_idx,
        args_start: 0,
        argc: 0,
    });
    entry.emit(Opcode::LoadPrime { rd: 1, var_idx: 0 });
    entry.emit(Opcode::Eq {
        rd: 2,
        r1: 1,
        r2: 0,
    });
    entry.emit(Opcode::Ret { rs: 2 });

    let ActionTransformOutcome::Transformed(instructions) =
        transform_action_to_next_state(&entry.instructions)
    else {
        panic!("entry should survive the action transform");
    };
    entry.instructions = instructions;
    entry
}

#[test]
fn hidden_loadprime_callee_reaches_next_state_lowering() {
    let mut chunk = BytecodeChunk::new();

    // Spec shape: Helper == y' ; Next == x' = Helper
    //
    // The entry action itself rewrites to next-state form cleanly, but the
    // transitive callee still carries primed semantics.
    let mut helper = BytecodeFunction::new("hidden_prime".to_string(), 0);
    helper.emit(Opcode::LoadPrime { rd: 0, var_idx: 1 });
    helper.emit(Opcode::Ret { rs: 0 });
    chunk.add_function(helper);

    let entry = rewritten_entry_calling(0);

    let module = lower_entry_next_state_with_chunk(&entry, &chunk, "transitive_hidden_prime")
        .expect("chunk-aware next-state lowering should still pull in the hidden LoadPrime callee");

    let names: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
    assert!(
        names.contains(&"transitive_hidden_prime"),
        "missing rewritten entry: {names:?}"
    );
    assert!(
        names.iter().any(|name| name.starts_with("__tmir_callee_")
            && name.ends_with("_n12x68696464656e5f7072696d65")),
        "missing transitive helper with LoadPrime: {names:?}"
    );
}

#[test]
fn hidden_set_prime_mode_callee_survives_transform_then_fails_next_state_lowering() {
    let mut chunk = BytecodeChunk::new();

    // Spec shape: Helper == LET H == x IN H' ; Next == x' = Helper
    //
    // The action transform does not look through the Call, so the entry is
    // retained even though the helper still depends on runtime SetPrimeMode.
    let mut helper = BytecodeFunction::new("hidden_set_prime_mode".to_string(), 0);
    helper.emit(Opcode::SetPrimeMode { enable: true });
    helper.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    helper.emit(Opcode::SetPrimeMode { enable: false });
    helper.emit(Opcode::Ret { rs: 0 });
    chunk.add_function(helper);

    let entry = rewritten_entry_calling(0);

    let err = lower_entry_next_state_with_chunk(&entry, &chunk, "transitive_set_prime_mode")
        .expect_err("next-state lowering should reject a transitive SetPrimeMode callee");

    let msg = err.to_string();
    assert!(
        msg.contains("unsupported opcode"),
        "unexpected lowering error: {msg}"
    );
}
