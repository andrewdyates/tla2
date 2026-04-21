// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA+ Standard Library Definitions
//!
//! This module provides definitions for the TLA+ standard library modules
//! (Naturals, Integers, Sequences, FiniteSets, TLC, etc.) to enable proper
//! name resolution without needing to parse the actual standard library files.
//!
//! The definitions here are stubs - they provide symbol information (name, arity)
//! but not implementation semantics. The actual semantics are provided by
//! tla-check (model checking) and tla-prove (theorem proving).

mod community_modules;
mod core_modules;
mod tlaps_modules;

#[cfg(test)]
mod tests;

use crate::resolve::{ResolveCtx, SymbolKind};
use crate::span::Span;

use community_modules::*;
use core_modules::*;
use tlaps_modules::*;

/// Operator definition: (name, arity)
/// Arity -1 means variadic (accepts any number of arguments)
type OpDef = (&'static str, i32);

/// Standard library module names
pub const STDLIB_MODULES: &[&str] = &[
    "Naturals",
    "Integers",
    "Reals",
    "Sequences",
    "FiniteSets",
    "Bags",
    "BagsExt",
    "TLC",
    "TLAPS",
    "Toolbox",
    // TLAPS proof modules
    "PTL",        // Propositional Temporal Logic
    "Zenon",      // Zenon prover
    "SMT",        // SMT solvers
    "Isa",        // Isabelle prover
    "Blast",      // Blast prover
    "Auto",       // Auto prover
    "ProofRules", // Proof rules
    "TLAPMTLA",   // TLA+ Proof Manager TLA module
    "WellFoundedInduction",
    // Community modules (commonly used)
    "Folds",
    "Functions",
    "FiniteSetTheorems",
    "NaturalsInduction",
    "SequencesExt",
    "FiniteSetsExt",
    "TLCExt",
    "Strings",
    "IOUtils",
    "CSV",
    "Json",
    "Relation",
    // Dyadic rationals (CommunityModules)
    "DyadicRationals",
    // Graph theory
    "Graphs",
    "UndirectedGraphs",
    "DirectedGraphs",
    // Bitwise operations (CommunityModules)
    "Bitwise",
    // Randomization (TLC standard module)
    "Randomization",
    // SVG module for animation specs (CommunityModules)
    "SVG",
    // VectorClocks for trace export (CommunityModules)
    "VectorClocks",
    // Statistics module for statistical tests (CommunityModules)
    "Statistics",
    // Apalache modules
    "Apalache",
    "Variants",
    "Option",
];

/// Get operators provided by a standard library module
pub fn get_module_operators(module_name: &str) -> &'static [OpDef] {
    match module_name {
        "Naturals" => NATURALS_OPS,
        "Integers" => INTEGERS_OPS,
        "Reals" => REALS_OPS,
        "Sequences" => SEQUENCES_OPS,
        "FiniteSets" => FINITESETS_OPS,
        "Bags" => BAGS_OPS,
        "BagsExt" => BAGSEXT_OPS,
        "TLC" => TLC_OPS,
        "TLAPS" => TLAPS_OPS,
        "Toolbox" => TOOLBOX_OPS,
        // TLAPS proof modules
        "PTL" => PTL_OPS,
        "Zenon" => ZENON_OPS,
        "SMT" => SMT_OPS,
        "Isa" => ISA_OPS,
        "Blast" => BLAST_OPS,
        "Auto" => AUTO_OPS,
        "ProofRules" => PROOFRULES_OPS,
        "TLAPMTLA" => TLAPMTLA_OPS,
        "WellFoundedInduction" => WELLFOUNDEDINDUCTION_OPS,
        // Community modules
        "Folds" => FOLDS_OPS,
        "Functions" => FUNCTIONS_OPS,
        "FiniteSetTheorems" => FINITESETTHEOREMS_OPS,
        "NaturalsInduction" => NATURALSINDUCTION_OPS,
        "SequencesExt" => SEQUENCESEXT_OPS,
        "FiniteSetsExt" => FINITESETSEXT_OPS,
        "TLCExt" => TLCEXT_OPS,
        "Strings" => STRINGS_OPS,
        "IOUtils" => IOUTILS_OPS,
        "CSV" => CSV_OPS,
        "Json" => JSON_OPS,
        "Relation" => RELATION_OPS,
        // Dyadic rationals
        "DyadicRationals" => DYADICRATIONALS_OPS,
        // Graph modules
        "Graphs" => GRAPHS_OPS,
        "UndirectedGraphs" => UNDIRECTEDGRAPHS_OPS,
        "DirectedGraphs" => DIRECTEDGRAPHS_OPS,
        "Bitwise" => BITWISE_OPS,
        "Randomization" => RANDOMIZATION_OPS,
        "SVG" => SVG_OPS,
        "VectorClocks" => VECTORCLOCKS_OPS,
        "Statistics" => STATISTICS_OPS,
        // Apalache modules
        "Apalache" => APALACHE_OPS,
        "Variants" => VARIANTS_OPS,
        "Option" => OPTION_OPS,
        _ => &[],
    }
}

/// Check if a module name is a standard library module
pub fn is_stdlib_module(name: &str) -> bool {
    STDLIB_MODULES.contains(&name)
}

/// Inject standard library symbols into a resolution context based on EXTENDS list
pub(crate) fn inject_stdlib(ctx: &mut ResolveCtx, extends: &[&str]) {
    // Create a synthetic span for stdlib definitions (dummy span = file 0, offset 0)
    let stdlib_span = Span::dummy();

    inject_prelude_builtins(ctx, stdlib_span);

    // Track which modules have been processed to handle transitive extends
    let mut processed = std::collections::HashSet::new();

    // Process each extended module
    for module_name in extends {
        inject_module_symbols(ctx, module_name, &mut processed, stdlib_span);
    }
}

fn inject_prelude_builtins(ctx: &mut ResolveCtx, span: Span) {
    // Built-ins that exist without requiring EXTENDS.
    //
    // Note: BOOLEAN is lexed as a keyword and lowered to `Ident("BOOLEAN")`.
    // It must always be resolvable, or specs using record/function set syntax like
    // `[field: BOOLEAN]` and `[S -> BOOLEAN]` will fail semantic analysis.
    ctx.define("BOOLEAN", SymbolKind::Constant, span, 0, false);

    // Built-in operators that appear as identifiers in the lowered AST.
    //
    // Some built-in infix syntax is lowered to `Apply(Ident(op), [lhs, rhs])` rather than to a
    // dedicated AST node. That makes these names participate in semantic resolution even though
    // they don't require EXTENDS and are not user-defined.
    //
    // If we don't inject them here, semantic analysis reports "undefined identifier" for specs
    // using these operators (tlaplus-examples commonly use `\o` and `:>`).
    ctx.define("\\o", SymbolKind::Operator, span, 2, false);
    ctx.define("\\circ", SymbolKind::Operator, span, 2, false);
    ctx.define("\\cdot", SymbolKind::Operator, span, 2, false);
    ctx.define(":>", SymbolKind::Operator, span, 2, false);
    ctx.define("@@", SymbolKind::Operator, span, 2, false);
}

fn inject_module_symbols(
    ctx: &mut ResolveCtx,
    module_name: &str,
    processed: &mut std::collections::HashSet<String>,
    span: Span,
) {
    if processed.contains(module_name) {
        return;
    }
    processed.insert(module_name.to_string());

    // Handle transitive extends (public EXTENDS chains only, not LOCAL INSTANCE).
    // Verified against TLC community module source (CommunityModules.jar).
    // Note: UndirectedGraphs does NOT extend Graphs - they are separate modules
    // with different edge representations (sets vs tuples)
    match module_name {
        // Core math modules
        "Integers" => {
            inject_module_symbols(ctx, "Naturals", processed, span);
        }
        "Reals" => {
            inject_module_symbols(ctx, "Integers", processed, span);
        }
        // Standard modules
        "Bags" => {
            // Bags.tla: EXTENDS TLC
            inject_module_symbols(ctx, "TLC", processed, span);
        }
        // Community modules
        "FiniteSetsExt" => {
            // FiniteSetsExt.tla: EXTENDS Folds, Functions
            inject_module_symbols(ctx, "Folds", processed, span);
            inject_module_symbols(ctx, "Functions", processed, span);
        }
        "VectorClocks" => {
            // VectorClocks.tla: EXTENDS Naturals, Sequences, Functions
            inject_module_symbols(ctx, "Naturals", processed, span);
            inject_module_symbols(ctx, "Sequences", processed, span);
            inject_module_symbols(ctx, "Functions", processed, span);
        }
        "Statistics" => {
            // Statistics.tla: EXTENDS Naturals
            inject_module_symbols(ctx, "Naturals", processed, span);
        }
        "Apalache" => {
            // Apalache.tla: EXTENDS Integers, Sequences
            inject_module_symbols(ctx, "Integers", processed, span);
            inject_module_symbols(ctx, "Sequences", processed, span);
        }
        "Variants" => {
            // Variants.tla: standalone (no transitive extends needed for stubs)
        }
        "Option" => {
            // Option.tla: EXTENDS Apalache, Variants
            inject_module_symbols(ctx, "Apalache", processed, span);
            inject_module_symbols(ctx, "Variants", processed, span);
        }
        _ => {}
    }

    // Get operators for this module
    let ops = get_module_operators(module_name);

    for (name, arity) in ops {
        let arity = if *arity < 0 { 0 } else { *arity as usize };
        // Use define_imported_operator to allow same-arity operators from different
        // stdlib modules (e.g., Functions.Range and SequencesExt.Range both have arity 1).
        // TLC treats this as a warning, not an error.
        ctx.define_imported_operator(name, span, arity);
    }

    // Also define the module as a constant (e.g., Nat, Int, Real, Seq)
    match module_name {
        "Naturals" => {
            ctx.define("Nat", SymbolKind::Constant, span, 0, false);
        }
        "Integers" => {
            ctx.define("Int", SymbolKind::Constant, span, 0, false);
        }
        "Reals" => {
            ctx.define("Real", SymbolKind::Constant, span, 0, false);
            ctx.define("Infinity", SymbolKind::Constant, span, 0, false);
        }
        _ => {}
    }
}
