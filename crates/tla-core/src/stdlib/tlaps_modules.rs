// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLAPS proof system module operator tables.
//!
//! Operator definitions for the TLA+ Proof System modules: TLAPS, Toolbox,
//! PTL, Zenon, SMT, Isa, Blast, Auto, ProofRules, TLAPMTLA, and
//! WellFoundedInduction.

use super::OpDef;

/// TLAPS (TLA+ Proof System) module operators
/// All TLAPS operators return TRUE during model checking - they are proof backend pragmas
pub(super) const TLAPS_OPS: &[OpDef] = &[
    // SMT solver operators (zero-arity)
    ("SMT", 0),
    ("CVC3", 0),
    ("Yices", 0),
    ("veriT", 0),
    ("Z3", 0),
    ("Spass", 0),
    ("SimpleArithmetic", 0),
    // Zenon prover operators (zero-arity)
    ("Zenon", 0),
    ("SlowZenon", 0),
    ("SlowerZenon", 0),
    ("VerySlowZenon", 0),
    ("SlowestZenon", 0),
    // Isabelle prover operators (zero-arity)
    ("Isa", 0),
    ("Auto", 0),
    ("Force", 0),
    ("Blast", 0),
    ("SimplifyAndSolve", 0),
    ("Simplification", 0),
    ("AutoBlast", 0),
    // Temporal logic operators (zero-arity)
    ("LS4", 0),
    ("PTL", 0),
    ("PropositionalTemporalLogic", 0),
    // Multi-backend operators (zero-arity)
    ("AllProvers", 0),
    ("AllSMT", 0),
    ("AllIsa", 0),
    // Theorems (zero-arity)
    ("SetExtensionality", 0),
    ("NoSetContainsEverything", 0),
    ("IsaWithSetExtensionality", 0),
    // Parameterized SMT operators (1 arg)
    ("SMTT", 1),
    ("CVC3T", 1),
    ("YicesT", 1),
    ("veriTT", 1),
    ("Z3T", 1),
    ("SpassT", 1),
    // Parameterized Zenon operator (1 arg)
    ("ZenonT", 1),
    // Parameterized Isabelle operators (1-2 args)
    ("IsaT", 1),
    ("IsaM", 1),
    ("IsaMT", 2),
    // Parameterized multi-backend operators (1 arg)
    ("AllProversT", 1),
    ("AllSMTT", 1),
    ("AllIsaT", 1),
];

/// Toolbox module operators
pub(super) const TOOLBOX_OPS: &[OpDef] = &[
    // Toolbox-specific annotations
];

/// PTL (Propositional Temporal Logic) module operators
pub(super) const PTL_OPS: &[OpDef] = &[
    // Temporal operators for propositional proofs
    // PTL is used as a proof backend selector, no explicit operators
];

/// Zenon prover module operators
pub(super) const ZENON_OPS: &[OpDef] = &[
    // Zenon is used as a proof backend selector, no explicit operators
];

/// SMT solver module operators
pub(super) const SMT_OPS: &[OpDef] = &[
    // SMT is used as a proof backend selector, no explicit operators
];

/// Isabelle prover module operators
pub(super) const ISA_OPS: &[OpDef] = &[
    // Isa is used as a proof backend selector, no explicit operators
];

/// Blast prover module operators
pub(super) const BLAST_OPS: &[OpDef] = &[
    // Blast is used as a proof backend selector, no explicit operators
];

/// Auto prover module operators
pub(super) const AUTO_OPS: &[OpDef] = &[
    // Auto is used as a proof backend selector, no explicit operators
];

/// ProofRules module operators
pub(super) const PROOFRULES_OPS: &[OpDef] = &[];

/// TLAPMTLA module operators
pub(super) const TLAPMTLA_OPS: &[OpDef] = &[];

/// WellFoundedInduction module operators
pub(super) const WELLFOUNDEDINDUCTION_OPS: &[OpDef] = &[
    ("OpToRel", 2),         // Convert operator to relation
    ("IsWellFoundedOn", 2), // Check if relation is well-founded
    ("SetLessThan", 2),     // Set comparison for well-foundedness
];
