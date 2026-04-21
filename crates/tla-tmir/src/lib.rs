// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode-to-tMIR lowering backend.
//!
//! This crate translates TLA+ bytecode functions ([`BytecodeFunction`]) into
//! [`tmir::Module`] — a proof-carrying SSA IR that can be compiled through
//! LLVM2's verified backend. It is an alternative to the `tla-llvm` crate
//! which emits LLVM IR text and shells out to llc/clang.
//!
//! # Architecture
//!
//! The TLA+ bytecode is register-based (256 virtual registers), while tMIR is
//! SSA-based. The lowering allocates a tMIR alloca per bytecode register and
//! uses load/store to bridge the models. This is the same strategy as
//! `tla-llvm/lower.rs` — simple, correct, and the tMIR optimizer can promote
//! the allocas to SSA values later.
//!
//! # Supported opcodes
//!
//! Phase 1 covers the scalar integer core:
//! - Arithmetic: `AddInt`, `SubInt`, `MulInt`, `IntDiv`, `ModInt`, `NegInt`, `DivInt`
//! - Comparison: `Eq`, `Neq`, `LtInt`, `LeInt`, `GtInt`, `GeInt`
//! - Boolean: `And`, `Or`, `Not`, `Implies`, `Equiv`
//! - Control: `Jump`, `JumpTrue`, `JumpFalse`, `Ret`, `CondMove`, `Halt`, `Nop`
//! - State: `LoadImm`, `LoadBool`, `LoadVar`, `LoadPrime`, `StoreVar`, `Move`
//!
//! Phase 2 adds compound types:
//! - Sets: `SetEnum`, `SetIn`, `SetUnion`, `SetIntersect`, `SetDiff`, `Subseteq`, `Range`
//! - Sequences: `SeqNew`, `CallBuiltin(Len)`, `CallBuiltin(Head)`, `CallBuiltin(Tail)`,
//!   `CallBuiltin(Append)`
//! - Tuples: `TupleNew`, `TupleGet`
//! - Records: `RecordNew`, `RecordGet`
//! - Builtins: `CallBuiltin(Cardinality)`
//!
//! Phase 3 adds quantifiers:
//! - ForAll: `ForallBegin`, `ForallNext` — loop with short-circuit AND
//! - Exists: `ExistsBegin`, `ExistsNext` — loop with short-circuit OR
//! - Choose: `ChooseBegin`, `ChooseNext` — first-match iteration
//!
//! Phase 4 adds functions:
//! - FuncApply: `f[x]` — linear scan for key match in function aggregate
//! - Domain: `DOMAIN f` — extract keys into a new set
//! - FuncExcept: `[f EXCEPT ![x] = y]` — copy with conditional value replacement
//! - FuncDef: `FuncDefBegin`/`LoopNext` — iterate domain, build function aggregate
//!
//! Function aggregate layout: `[pair_count, key1, val1, key2, val2, ...]`.
//!
//! Phase 5 adds constants and frame conditions:
//! - LoadConst: `LoadConst { rd, idx }` — load integer/boolean from constant pool
//! - Unchanged: `Unchanged { rd, start, count }` — frame condition (next' = current)
//!
//! Unsupported opcodes (closures, set comprehensions, FuncSet, etc.) return
//! [`TmirError::UnsupportedOpcode`].

pub mod annotations;
pub mod layout;
pub mod lower;

mod error;
pub use error::TmirError;
