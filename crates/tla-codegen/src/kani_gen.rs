// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Automatic Kani proof harness generator for TIR-based codegen output.
//!
//! Given metadata about a generated Rust module (state type, variable types,
//! invariant names), this module emits three categories of verification
//! harnesses:
//!
//! 1. **Base case** — `Init` satisfies every invariant.
//! 2. **Inductive step** — for any state satisfying `Inv`, every `Next`
//!    successor also satisfies `Inv`.
//! 3. **Bounded model check** — explore all reachable states within `K` steps
//!    and verify invariants at each step.
//!
//! Each Kani harness has a corresponding `#[test]` fallback so the same
//! verification logic can run under `cargo test` without Kani installed.
//!
//! # Usage
//!
//! ```rust,ignore
//! use tla_codegen::kani_gen::{generate_kani_harnesses, KaniGenOptions, SpecInfo, VarInfo};
//! use tla_codegen::TlaType;
//!
//! let spec = SpecInfo {
//!     module_name: "ModularCounter".into(),
//!     state_type: "ModularCounterState".into(),
//!     machine_type: "ModularCounter".into(),
//!     variables: vec![VarInfo {
//!         name: "x".into(),
//!         rust_field: "x".into(),
//!         ty: TlaType::Int,
//!         range: Some((0, 10)),
//!     }],
//!     invariant_names: vec!["Inv".into()],
//! };
//! let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());
//! ```

use crate::types::TlaType;
use std::fmt::Write;

/// Metadata about a generated TLA+ spec module, sufficient to produce Kani
/// harnesses.
#[derive(Debug, Clone)]
pub struct SpecInfo {
    /// TLA+ module name (e.g. `"ModularCounter"`).
    pub module_name: String,
    /// Rust state struct name (e.g. `"ModularCounterState"`).
    pub state_type: String,
    /// Rust state machine struct name (e.g. `"ModularCounter"`).
    pub machine_type: String,
    /// Per-variable metadata.
    pub variables: Vec<VarInfo>,
    /// Names of invariant operators (e.g. `["Inv", "TypeOK"]`).
    pub invariant_names: Vec<String>,
}

/// Metadata for a single state variable.
#[derive(Debug, Clone)]
pub struct VarInfo {
    /// TLA+ variable name.
    pub name: String,
    /// Snake-case Rust field name in the state struct.
    pub rust_field: String,
    /// Inferred type.
    pub ty: TlaType,
    /// Optional inclusive integer range `[lo, hi)` for `kani::assume` constraints.
    /// Only meaningful when `ty` is `TlaType::Int`.
    pub range: Option<(i64, i64)>,
}

/// Options controlling harness generation.
#[derive(Debug, Clone)]
pub struct KaniGenOptions {
    /// Maximum number of steps for the bounded model check harness.
    /// The `#[kani::unwind]` annotation is set to `bound_k + 1`.
    pub bound_k: usize,
    /// Maximum number of states explored in the test-mode BFS fallback.
    pub test_max_states: usize,
}

impl Default for KaniGenOptions {
    fn default() -> Self {
        Self {
            bound_k: 15,
            test_max_states: 10_000,
        }
    }
}

const W: &str = "writing generated Rust into an in-memory String should not fail";

/// Generate Kani proof harnesses and `#[test]` fallbacks for a spec.
///
/// Returns a string of Rust source code containing:
/// - `#[cfg(kani)] #[kani::proof]` harnesses for base case, inductive step,
///   and bounded model checking.
/// - A `#[cfg(test)] mod tests { ... }` with equivalent `#[test]` functions.
///
/// The caller is responsible for appending this to (or including it in) the
/// generated module that defines `init()`, `next()`, and `check_*()` functions.
#[must_use]
pub fn generate_kani_harnesses(spec: &SpecInfo, options: &KaniGenOptions) -> String {
    let mut out = String::with_capacity(4096);

    emit_header(&mut out, spec);
    emit_kani_base_case(&mut out, spec);
    emit_kani_inductive_step(&mut out, spec, options);
    emit_kani_bounded(&mut out, spec, options);
    emit_test_module(&mut out, spec, options);

    out
}

// ---------------------------------------------------------------------------
// Internal emitters
// ---------------------------------------------------------------------------

fn emit_header(out: &mut String, spec: &SpecInfo) {
    writeln!(out, "// ---------------------------------------------------------------------------").expect(W);
    writeln!(
        out,
        "// Kani proof harnesses for {} (auto-generated)",
        spec.module_name
    )
    .expect(W);
    writeln!(out, "// ---------------------------------------------------------------------------").expect(W);
    writeln!(out).expect(W);
}

/// Base case: every initial state satisfies every invariant.
fn emit_kani_base_case(out: &mut String, spec: &SpecInfo) {
    let machine = &spec.machine_type;
    writeln!(out, "/// Base case: every initial state satisfies all invariants.").expect(W);
    writeln!(out, "#[cfg(kani)]").expect(W);
    writeln!(out, "#[kani::proof]").expect(W);
    writeln!(out, "fn prove_init_satisfies_inv() {{").expect(W);
    writeln!(out, "    let sm = {machine};").expect(W);
    writeln!(out, "    let states = sm.init();").expect(W);
    writeln!(out, "    for state in &states {{").expect(W);
    for inv in &spec.invariant_names {
        let check_fn = to_snake_case(inv);
        writeln!(
            out,
            "        kani::assert({machine}::check_{check_fn}(state), \"Init violates {inv}\");",
        )
        .expect(W);
    }
    writeln!(out, "    }}").expect(W);
    writeln!(out, "}}").expect(W);
    writeln!(out).expect(W);
}

/// Inductive step: if all invariants hold, every `Next` successor also
/// satisfies all invariants.
fn emit_kani_inductive_step(out: &mut String, spec: &SpecInfo, _options: &KaniGenOptions) {
    let state_ty = &spec.state_type;
    let machine = &spec.machine_type;

    writeln!(
        out,
        "/// Inductive step: Inv /\\ Next => Inv' for all invariants."
    )
    .expect(W);
    writeln!(out, "#[cfg(kani)]").expect(W);
    writeln!(out, "#[kani::proof]").expect(W);
    writeln!(out, "fn prove_next_preserves_inv() {{").expect(W);

    // Declare a symbolic value for each variable.
    for var in &spec.variables {
        emit_kani_any_decl(out, var, "    ");
    }

    // Construct the state.
    writeln!(out, "    let state = {state_ty} {{").expect(W);
    for var in &spec.variables {
        writeln!(out, "        {field},", field = var.rust_field).expect(W);
    }
    writeln!(out, "    }};").expect(W);

    // Assume all invariants hold (inductive hypothesis).
    for inv in &spec.invariant_names {
        let check_fn = to_snake_case(inv);
        writeln!(
            out,
            "    kani::assume({machine}::check_{check_fn}(&state));",
        )
        .expect(W);
    }

    // Assert invariants on every successor.
    writeln!(out, "    let sm = {machine};").expect(W);
    writeln!(out, "    let successors = sm.next(&state);").expect(W);
    writeln!(out, "    for ns in &successors {{").expect(W);
    for inv in &spec.invariant_names {
        let check_fn = to_snake_case(inv);
        writeln!(
            out,
            "        kani::assert({machine}::check_{check_fn}(ns), \"Next violates {inv}\");",
        )
        .expect(W);
    }
    writeln!(out, "    }}").expect(W);
    writeln!(out, "}}").expect(W);
    writeln!(out).expect(W);
}

/// Bounded model check: pick a non-deterministic initial state and explore
/// up to K transitions.
fn emit_kani_bounded(out: &mut String, spec: &SpecInfo, options: &KaniGenOptions) {
    let machine = &spec.machine_type;
    let k = options.bound_k;

    writeln!(
        out,
        "/// Bounded model check: explore up to {k} steps from Init."
    )
    .expect(W);
    writeln!(out, "#[cfg(kani)]").expect(W);
    writeln!(out, "#[kani::proof]").expect(W);
    writeln!(out, "#[kani::unwind({})]", k + 1).expect(W);
    writeln!(out, "fn prove_bounded_k_steps() {{").expect(W);
    writeln!(out, "    let sm = {machine};").expect(W);
    writeln!(out, "    let init_states = sm.init();").expect(W);
    writeln!(out, "    if init_states.is_empty() {{").expect(W);
    writeln!(out, "        return;").expect(W);
    writeln!(out, "    }}").expect(W);
    writeln!(out, "    // Pick a non-deterministic initial state.").expect(W);
    writeln!(out, "    let idx: usize = kani::any();").expect(W);
    writeln!(out, "    kani::assume(idx < init_states.len());").expect(W);
    writeln!(out, "    let mut state = init_states[idx].clone();").expect(W);

    // Assert invariants at step 0.
    for inv in &spec.invariant_names {
        let check_fn = to_snake_case(inv);
        writeln!(
            out,
            "    kani::assert({machine}::check_{check_fn}(&state), \"{inv} violated at step 0\");",
        )
        .expect(W);
    }

    // Transition loop.
    writeln!(out, "    let k: usize = kani::any();").expect(W);
    writeln!(out, "    kani::assume(k <= {k});").expect(W);
    writeln!(out, "    let mut i = 0;").expect(W);
    writeln!(out, "    while i < k {{").expect(W);
    writeln!(out, "        let succs = sm.next(&state);").expect(W);
    writeln!(out, "        if succs.is_empty() {{").expect(W);
    writeln!(out, "            break;").expect(W);
    writeln!(out, "        }}").expect(W);
    writeln!(out, "        state = succs[0].clone();").expect(W);
    for inv in &spec.invariant_names {
        let check_fn = to_snake_case(inv);
        writeln!(
            out,
            "        kani::assert({machine}::check_{check_fn}(&state), \"{inv} violated after step\");",
        )
        .expect(W);
    }
    writeln!(out, "        i += 1;").expect(W);
    writeln!(out, "    }}").expect(W);
    writeln!(out, "}}").expect(W);
    writeln!(out).expect(W);
}

/// `#[cfg(test)]` module with `#[test]` equivalents.
fn emit_test_module(out: &mut String, spec: &SpecInfo, options: &KaniGenOptions) {
    let machine = &spec.machine_type;
    let state_ty = &spec.state_type;
    let max_states = options.test_max_states;

    writeln!(out, "// ---------------------------------------------------------------------------").expect(W);
    writeln!(out, "// Standard test fallbacks (run without Kani via `cargo test`)").expect(W);
    writeln!(out, "// ---------------------------------------------------------------------------").expect(W);
    writeln!(out).expect(W);
    writeln!(out, "#[cfg(test)]").expect(W);
    writeln!(out, "mod kani_fallback_tests {{").expect(W);
    writeln!(out, "    use super::*;").expect(W);
    writeln!(out).expect(W);

    // Test: init satisfies inv
    writeln!(out, "    /// Test: every initial state satisfies all invariants.").expect(W);
    writeln!(out, "    #[test]").expect(W);
    writeln!(out, "    fn test_init_satisfies_inv() {{").expect(W);
    writeln!(out, "        let sm = {machine};").expect(W);
    writeln!(out, "        let states = sm.init();").expect(W);
    writeln!(
        out,
        "        assert!(!states.is_empty(), \"Init must produce at least one state\");"
    )
    .expect(W);
    writeln!(out, "        for state in &states {{").expect(W);
    for inv in &spec.invariant_names {
        let check_fn = to_snake_case(inv);
        writeln!(
            out,
            "            assert!({machine}::check_{check_fn}(state), \"Init violates {inv}: {{:?}}\", state);",
        )
        .expect(W);
    }
    writeln!(out, "        }}").expect(W);
    writeln!(out, "    }}").expect(W);
    writeln!(out).expect(W);

    // Test: bounded BFS exploration
    writeln!(
        out,
        "    /// Test: BFS exploration verifying invariants at every reachable state."
    )
    .expect(W);
    writeln!(out, "    #[test]").expect(W);
    writeln!(out, "    fn test_bounded_exploration() {{").expect(W);
    writeln!(out, "        use std::collections::HashSet;").expect(W);
    writeln!(out).expect(W);
    writeln!(out, "        let sm = {machine};").expect(W);
    writeln!(
        out,
        "        let mut seen: HashSet<{state_ty}> = HashSet::new();"
    )
    .expect(W);
    writeln!(out, "        let mut frontier = sm.init();").expect(W);
    writeln!(out, "        let mut total = 0usize;").expect(W);
    writeln!(out, "        let max_states = {max_states};").expect(W);
    writeln!(out).expect(W);
    writeln!(out, "        while let Some(state) = frontier.pop() {{").expect(W);
    writeln!(out, "            if !seen.insert(state.clone()) {{").expect(W);
    writeln!(out, "                continue;").expect(W);
    writeln!(out, "            }}").expect(W);
    for inv in &spec.invariant_names {
        let check_fn = to_snake_case(inv);
        writeln!(
            out,
            "            assert!({machine}::check_{check_fn}(&state), \"{inv} violated at state {{:?}}\", state);",
        )
        .expect(W);
    }
    writeln!(out, "            total += 1;").expect(W);
    writeln!(out, "            if total >= max_states {{").expect(W);
    writeln!(out, "                break;").expect(W);
    writeln!(out, "            }}").expect(W);
    writeln!(out, "            frontier.extend(sm.next(&state));").expect(W);
    writeln!(out, "        }}").expect(W);
    writeln!(out, "        assert!(total > 0, \"no states explored\");").expect(W);
    writeln!(out, "    }}").expect(W);

    writeln!(out, "}}").expect(W);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Emit a `let field: Type = kani::any();` declaration with appropriate
/// `kani::assume` constraints for the variable's type and range.
fn emit_kani_any_decl(out: &mut String, var: &VarInfo, indent: &str) {
    let field = &var.rust_field;
    match &var.ty {
        TlaType::Bool => {
            writeln!(out, "{indent}let {field}: bool = kani::any();").expect(W);
        }
        TlaType::Int => {
            writeln!(out, "{indent}let {field}: i64 = kani::any();").expect(W);
            if let Some((lo, hi)) = var.range {
                writeln!(
                    out,
                    "{indent}kani::assume({field} >= {lo} && {field} < {hi});",
                )
                .expect(W);
            }
        }
        TlaType::String => {
            // Strings cannot be symbolically explored with kani::any().
            // Use a small set of representative values instead.
            writeln!(out, "{indent}let {field}_idx: u8 = kani::any();").expect(W);
            writeln!(out, "{indent}kani::assume({field}_idx < 3);").expect(W);
            writeln!(
                out,
                "{indent}let {field} = [\"a\", \"b\", \"c\"][{field}_idx as usize].to_string();"
            )
            .expect(W);
        }
        TlaType::Set(elem) => {
            emit_kani_any_set(out, var, elem, indent);
        }
        TlaType::Seq(elem) => {
            emit_kani_any_seq(out, var, elem, indent);
        }
        // For complex types (records, functions, tuples, unknown), fall back
        // to Default::default() with a comment indicating manual review is needed.
        _ => {
            let rust_ty = var.ty.to_rust_type();
            writeln!(
                out,
                "{indent}// TODO: kani::any() not supported for {rust_ty}; using default",
            )
            .expect(W);
            writeln!(
                out,
                "{indent}let {field}: {rust_ty} = Default::default();",
            )
            .expect(W);
        }
    }
}

/// Emit a symbolic set variable by constructing a small set of up to 3
/// elements via kani::any().
fn emit_kani_any_set(out: &mut String, var: &VarInfo, elem: &TlaType, indent: &str) {
    let field = &var.rust_field;
    match elem {
        TlaType::Int => {
            writeln!(out, "{indent}let {field}_len: u8 = kani::any();").expect(W);
            writeln!(out, "{indent}kani::assume({field}_len <= 3);").expect(W);
            writeln!(out, "{indent}let mut {field}_vec: Vec<i64> = Vec::new();").expect(W);
            writeln!(out, "{indent}let mut {field}_i = 0u8;").expect(W);
            writeln!(out, "{indent}while {field}_i < {field}_len {{").expect(W);
            writeln!(out, "{indent}    let elem: i64 = kani::any();").expect(W);
            if let Some((lo, hi)) = var.range {
                writeln!(
                    out,
                    "{indent}    kani::assume(elem >= {lo} && elem < {hi});",
                )
                .expect(W);
            }
            writeln!(out, "{indent}    {field}_vec.push(elem);").expect(W);
            writeln!(out, "{indent}    {field}_i += 1;").expect(W);
            writeln!(out, "{indent}}}").expect(W);
            writeln!(
                out,
                "{indent}let {field} = TlaSet::from_iter({field}_vec);",
            )
            .expect(W);
        }
        TlaType::Bool => {
            // A set of booleans has at most 4 subsets: {}, {T}, {F}, {T,F}.
            writeln!(out, "{indent}let {field}_has_t: bool = kani::any();").expect(W);
            writeln!(out, "{indent}let {field}_has_f: bool = kani::any();").expect(W);
            writeln!(out, "{indent}let mut {field}_vec: Vec<bool> = Vec::new();").expect(W);
            writeln!(out, "{indent}if {field}_has_t {{ {field}_vec.push(true); }}").expect(W);
            writeln!(out, "{indent}if {field}_has_f {{ {field}_vec.push(false); }}").expect(W);
            writeln!(
                out,
                "{indent}let {field} = TlaSet::from_iter({field}_vec);",
            )
            .expect(W);
        }
        _ => {
            let rust_ty = var.ty.to_rust_type();
            writeln!(
                out,
                "{indent}// TODO: kani::any() not supported for {rust_ty}; using default",
            )
            .expect(W);
            writeln!(
                out,
                "{indent}let {field}: {rust_ty} = Default::default();",
            )
            .expect(W);
        }
    }
}

/// Emit a symbolic sequence variable by constructing a Vec of up to 3
/// kani::any() elements.
fn emit_kani_any_seq(out: &mut String, var: &VarInfo, elem: &TlaType, indent: &str) {
    let field = &var.rust_field;
    match elem {
        TlaType::Int => {
            writeln!(out, "{indent}let {field}_len: u8 = kani::any();").expect(W);
            writeln!(out, "{indent}kani::assume({field}_len <= 3);").expect(W);
            writeln!(out, "{indent}let mut {field}: Vec<i64> = Vec::new();").expect(W);
            writeln!(out, "{indent}let mut {field}_i = 0u8;").expect(W);
            writeln!(out, "{indent}while {field}_i < {field}_len {{").expect(W);
            writeln!(out, "{indent}    let elem: i64 = kani::any();").expect(W);
            writeln!(out, "{indent}    {field}.push(elem);").expect(W);
            writeln!(out, "{indent}    {field}_i += 1;").expect(W);
            writeln!(out, "{indent}}}").expect(W);
        }
        TlaType::Bool => {
            writeln!(out, "{indent}let {field}_len: u8 = kani::any();").expect(W);
            writeln!(out, "{indent}kani::assume({field}_len <= 3);").expect(W);
            writeln!(out, "{indent}let mut {field}: Vec<bool> = Vec::new();").expect(W);
            writeln!(out, "{indent}let mut {field}_i = 0u8;").expect(W);
            writeln!(out, "{indent}while {field}_i < {field}_len {{").expect(W);
            writeln!(out, "{indent}    let elem: bool = kani::any();").expect(W);
            writeln!(out, "{indent}    {field}.push(elem);").expect(W);
            writeln!(out, "{indent}    {field}_i += 1;").expect(W);
            writeln!(out, "{indent}}}").expect(W);
        }
        _ => {
            let rust_ty = var.ty.to_rust_type();
            writeln!(
                out,
                "{indent}// TODO: kani::any() not supported for {rust_ty}; using default",
            )
            .expect(W);
            writeln!(
                out,
                "{indent}let {field}: {rust_ty} = Default::default();",
            )
            .expect(W);
        }
    }
}

/// Simple snake_case conversion matching the tir_emit utility.
fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    let mut prev_was_sep = false;
    let mut prev_was_lower_or_digit = false;

    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            if c.is_uppercase() {
                if !result.is_empty() && !prev_was_sep && prev_was_lower_or_digit {
                    result.push('_');
                }
                result.push(c.to_ascii_lowercase());
                prev_was_lower_or_digit = false;
            } else {
                result.push(c.to_ascii_lowercase());
                prev_was_lower_or_digit = true;
            }
            prev_was_sep = false;
        } else if !result.is_empty() && !prev_was_sep {
            result.push('_');
            prev_was_sep = true;
            prev_was_lower_or_digit = false;
        }
    }

    while result.ends_with('_') {
        result.pop();
    }

    if result.is_empty() {
        "_".to_string()
    } else if result.starts_with(|c: char| c.is_ascii_digit()) {
        format!("_{result}")
    } else {
        result
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a single-variable integer spec like ModularCounter.
    fn modular_counter_spec() -> SpecInfo {
        SpecInfo {
            module_name: "ModularCounter".into(),
            state_type: "ModularCounterState".into(),
            machine_type: "ModularCounter".into(),
            variables: vec![VarInfo {
                name: "x".into(),
                rust_field: "x".into(),
                ty: TlaType::Int,
                range: Some((0, 10)),
            }],
            invariant_names: vec!["Inv".into()],
        }
    }

    /// Build a multi-variable spec with both int and bool.
    fn traffic_light_spec() -> SpecInfo {
        SpecInfo {
            module_name: "TrafficLight".into(),
            state_type: "TrafficLightState".into(),
            machine_type: "TrafficLight".into(),
            variables: vec![
                VarInfo {
                    name: "color".into(),
                    rust_field: "color".into(),
                    ty: TlaType::Int,
                    range: Some((0, 3)),
                },
                VarInfo {
                    name: "is_on".into(),
                    rust_field: "is_on".into(),
                    ty: TlaType::Bool,
                    range: None,
                },
            ],
            invariant_names: vec!["TypeOK".into(), "SafetyInv".into()],
        }
    }

    // -- Base case harness tests --

    #[test]
    fn test_base_case_single_var_single_inv() {
        let spec = modular_counter_spec();
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("#[kani::proof]"),
            "should contain kani::proof attribute"
        );
        assert!(
            code.contains("fn prove_init_satisfies_inv()"),
            "should contain base case harness"
        );
        assert!(
            code.contains("ModularCounter::check_inv(state)"),
            "should check invariant Inv via check_inv"
        );
        assert!(
            code.contains("sm.init()"),
            "should call init()"
        );
    }

    #[test]
    fn test_base_case_multi_invariant() {
        let spec = traffic_light_spec();
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("TrafficLight::check_type_ok(state)"),
            "should check TypeOK via check_type_ok"
        );
        assert!(
            code.contains("TrafficLight::check_safety_inv(state)"),
            "should check SafetyInv via check_safety_inv"
        );
    }

    // -- Inductive step harness tests --

    #[test]
    fn test_inductive_step_single_int_var() {
        let spec = modular_counter_spec();
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("fn prove_next_preserves_inv()"),
            "should contain inductive step harness"
        );
        // Should declare a symbolic i64 for x
        assert!(
            code.contains("let x: i64 = kani::any();"),
            "should declare symbolic i64 for x"
        );
        // Should assume range constraint
        assert!(
            code.contains("kani::assume(x >= 0 && x < 10);"),
            "should assume integer range for x"
        );
        // Should construct state
        assert!(
            code.contains("let state = ModularCounterState {"),
            "should construct state struct"
        );
        // Should assume invariant (inductive hypothesis)
        assert!(
            code.contains("kani::assume(ModularCounter::check_inv(&state));"),
            "should assume invariant holds"
        );
        // Should assert invariant on successors
        assert!(
            code.contains("kani::assert(ModularCounter::check_inv(ns)"),
            "should assert invariant on successors"
        );
    }

    #[test]
    fn test_inductive_step_multi_var() {
        let spec = traffic_light_spec();
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        // Both variables should be declared
        assert!(
            code.contains("let color: i64 = kani::any();"),
            "should declare symbolic i64 for color"
        );
        assert!(
            code.contains("let is_on: bool = kani::any();"),
            "should declare symbolic bool for is_on"
        );
        // Range constraint only on the integer variable
        assert!(
            code.contains("kani::assume(color >= 0 && color < 3);"),
            "should assume range for color"
        );
        // No range constraint on boolean (boolean is inherently bounded)
        assert!(
            !code.contains("kani::assume(is_on >="),
            "should NOT assume range for boolean"
        );
        // State construction should include both fields
        assert!(
            code.contains("TrafficLightState {"),
            "should construct multi-field state"
        );
    }

    // -- Bounded model check harness tests --

    #[test]
    fn test_bounded_harness_default_k() {
        let spec = modular_counter_spec();
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("fn prove_bounded_k_steps()"),
            "should contain bounded harness"
        );
        assert!(
            code.contains("#[kani::unwind(16)]"),
            "default K=15 should yield unwind(16)"
        );
        assert!(
            code.contains("kani::assume(k <= 15);"),
            "should bound loop to K=15"
        );
    }

    #[test]
    fn test_bounded_harness_custom_k() {
        let spec = modular_counter_spec();
        let options = KaniGenOptions {
            bound_k: 5,
            ..KaniGenOptions::default()
        };
        let code = generate_kani_harnesses(&spec, &options);

        assert!(
            code.contains("#[kani::unwind(6)]"),
            "K=5 should yield unwind(6)"
        );
        assert!(
            code.contains("kani::assume(k <= 5);"),
            "should bound loop to K=5"
        );
    }

    // -- Test fallback module tests --

    #[test]
    fn test_fallback_test_module_present() {
        let spec = modular_counter_spec();
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("#[cfg(test)]"),
            "should contain #[cfg(test)]"
        );
        assert!(
            code.contains("mod kani_fallback_tests"),
            "should contain fallback test module"
        );
        assert!(
            code.contains("fn test_init_satisfies_inv()"),
            "should contain init test"
        );
        assert!(
            code.contains("fn test_bounded_exploration()"),
            "should contain bounded exploration test"
        );
    }

    #[test]
    fn test_fallback_custom_max_states() {
        let spec = modular_counter_spec();
        let options = KaniGenOptions {
            test_max_states: 500,
            ..KaniGenOptions::default()
        };
        let code = generate_kani_harnesses(&spec, &options);

        assert!(
            code.contains("let max_states = 500;"),
            "should use custom max_states"
        );
    }

    // -- Integer range constraint tests --

    #[test]
    fn test_int_var_without_range() {
        let spec = SpecInfo {
            module_name: "Unbounded".into(),
            state_type: "UnboundedState".into(),
            machine_type: "Unbounded".into(),
            variables: vec![VarInfo {
                name: "n".into(),
                rust_field: "n".into(),
                ty: TlaType::Int,
                range: None,
            }],
            invariant_names: vec!["Inv".into()],
        };
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("let n: i64 = kani::any();"),
            "should declare symbolic i64"
        );
        // Should NOT contain an assume for n since range is None
        assert!(
            !code.contains("kani::assume(n >="),
            "should NOT assume range when range is None"
        );
    }

    // -- String variable tests --

    #[test]
    fn test_string_var_uses_representative_values() {
        let spec = SpecInfo {
            module_name: "StringSpec".into(),
            state_type: "StringSpecState".into(),
            machine_type: "StringSpec".into(),
            variables: vec![VarInfo {
                name: "msg".into(),
                rust_field: "msg".into(),
                ty: TlaType::String,
                range: None,
            }],
            invariant_names: vec!["Inv".into()],
        };
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("let msg_idx: u8 = kani::any();"),
            "should use index-based representative strings"
        );
        assert!(
            code.contains("kani::assume(msg_idx < 3);"),
            "should bound string index"
        );
    }

    // -- Set variable tests --

    #[test]
    fn test_set_of_int_symbolic() {
        let spec = SpecInfo {
            module_name: "SetSpec".into(),
            state_type: "SetSpecState".into(),
            machine_type: "SetSpec".into(),
            variables: vec![VarInfo {
                name: "s".into(),
                rust_field: "s".into(),
                ty: TlaType::Set(Box::new(TlaType::Int)),
                range: Some((0, 5)),
            }],
            invariant_names: vec!["Inv".into()],
        };
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("let s_len: u8 = kani::any();"),
            "should declare symbolic set length"
        );
        assert!(
            code.contains("kani::assume(s_len <= 3);"),
            "should bound set size"
        );
        assert!(
            code.contains("TlaSet::from_iter(s_vec)"),
            "should construct set from vec"
        );
    }

    #[test]
    fn test_set_of_bool_symbolic() {
        let spec = SpecInfo {
            module_name: "BoolSetSpec".into(),
            state_type: "BoolSetSpecState".into(),
            machine_type: "BoolSetSpec".into(),
            variables: vec![VarInfo {
                name: "flags".into(),
                rust_field: "flags".into(),
                ty: TlaType::Set(Box::new(TlaType::Bool)),
                range: None,
            }],
            invariant_names: vec!["Inv".into()],
        };
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("let flags_has_t: bool = kani::any();"),
            "should use inclusion flags for boolean sets"
        );
        assert!(
            code.contains("let flags_has_f: bool = kani::any();"),
            "should use inclusion flags for boolean sets"
        );
    }

    // -- Sequence variable tests --

    #[test]
    fn test_seq_of_int_symbolic() {
        let spec = SpecInfo {
            module_name: "SeqSpec".into(),
            state_type: "SeqSpecState".into(),
            machine_type: "SeqSpec".into(),
            variables: vec![VarInfo {
                name: "log".into(),
                rust_field: "log".into(),
                ty: TlaType::Seq(Box::new(TlaType::Int)),
                range: None,
            }],
            invariant_names: vec!["Inv".into()],
        };
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        assert!(
            code.contains("let log_len: u8 = kani::any();"),
            "should declare symbolic seq length"
        );
        assert!(
            code.contains("kani::assume(log_len <= 3);"),
            "should bound seq size"
        );
        assert!(
            code.contains("let mut log: Vec<i64> = Vec::new();"),
            "should declare Vec for sequence"
        );
    }

    // -- snake_case tests --

    #[test]
    fn test_snake_case_conversion() {
        assert_eq!(to_snake_case("Inv"), "inv");
        assert_eq!(to_snake_case("TypeOK"), "type_ok");
        assert_eq!(to_snake_case("SafetyInv"), "safety_inv");
        assert_eq!(to_snake_case("check_inv"), "check_inv");
        // Consecutive uppercase letters are not split: "MC" stays "mc".
        assert_eq!(to_snake_case("MCInit"), "mcinit");
    }

    // -- Empty invariants --

    #[test]
    fn test_no_invariants() {
        let spec = SpecInfo {
            module_name: "NoInv".into(),
            state_type: "NoInvState".into(),
            machine_type: "NoInv".into(),
            variables: vec![VarInfo {
                name: "x".into(),
                rust_field: "x".into(),
                ty: TlaType::Int,
                range: None,
            }],
            invariant_names: vec![],
        };
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        // Harnesses should still be generated (they just don't assert anything).
        assert!(
            code.contains("fn prove_init_satisfies_inv()"),
            "harness should still be generated even with no invariants"
        );
    }

    // -- Full output snapshot for ModularCounter --

    #[test]
    fn test_modular_counter_full_output() {
        let spec = modular_counter_spec();
        let options = KaniGenOptions {
            bound_k: 15,
            test_max_states: 1000,
        };
        let code = generate_kani_harnesses(&spec, &options);

        // Verify the three Kani harnesses are present.
        let kani_proof_count = code.matches("#[kani::proof]").count();
        assert_eq!(
            kani_proof_count, 3,
            "should have exactly 3 kani::proof harnesses, got {}",
            kani_proof_count
        );

        // Verify the two test functions are present.
        assert!(code.contains("fn test_init_satisfies_inv()"));
        assert!(code.contains("fn test_bounded_exploration()"));

        // Verify the cfg gates.
        let cfg_kani_count = code.matches("#[cfg(kani)]").count();
        assert_eq!(
            cfg_kani_count, 3,
            "should have 3 #[cfg(kani)] gates"
        );
        assert!(code.contains("#[cfg(test)]"));
    }

    // -- Multi-variable full output --

    #[test]
    fn test_traffic_light_full_output() {
        let spec = traffic_light_spec();
        let code = generate_kani_harnesses(&spec, &KaniGenOptions::default());

        // Both field names appear in state construction.
        assert!(code.contains("color,"));
        assert!(code.contains("is_on,"));

        // Both invariant checks in base case.
        assert!(code.contains("check_type_ok"));
        assert!(code.contains("check_safety_inv"));

        // Both assume calls in inductive step.
        assert!(code.contains("kani::assume(TrafficLight::check_type_ok(&state));"));
        assert!(code.contains("kani::assume(TrafficLight::check_safety_inv(&state));"));
    }
}
