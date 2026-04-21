// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FRTS (Functional Reduction / Transitive Simplification) preprocessing.
//!
//! Eliminates functionally equivalent signals using simulation-guided,
//! budget-limited SAT verification. Unlike SCORR (which handles sequential
//! latch equivalences), FRTS targets combinational equivalences across all
//! signal types (latches, gates, inputs).
//!
//! Improvements over the initial implementation:
//! - Init-seeded simulation for better candidate quality near initial states
//! - FRTS-local higher-round simulation to reduce false-positive candidates
//! - Proven equivalences fed back to the solver as clauses (rIC3's `add_eq`)
//! - Skips primary-input/primary-input pairs, which have no structural path
//! - Time-limited to avoid spending too long on large circuits (rIC3's `frts_tl`)
//! - Intermediate COI cleanup when many signals eliminated (rIC3's pattern of
//!   `coi_refine + bve_simplify` every 5000 replacements)
//! - COI reduction after each iteration to shrink the circuit for subsequent rounds
//!
//! Reference: rIC3's `FrTs::new()` + `fr()` in `transys/frts.rs`.

use std::time::{Duration, Instant};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Lit, SatResult, SatSolver, SolverBackend, Var};
use crate::transys::Transys;

use super::bve::bounded_variable_elimination;
use super::simulation::{random_pattern, SimSig};
use super::substitution::{apply_substitution, sorted_and_defs, subst_lit};

/// Maximum FRTS iterations (simulate -> verify -> substitute -> repeat).
const MAX_FRTS_ITERATIONS: usize = 5;

/// Maximum conflict budget per SAT query. If the solver exceeds this many
/// conflicts without determining SAT/UNSAT, we skip the pair. Low budgets
/// (1-10) are critical for FRTS performance: most equivalent pairs are
/// trivially provable, and hard pairs should be skipped rather than blocking.
/// rIC3 uses a restart limit of 1, which corresponds to roughly 10 conflicts.
const CONFLICT_BUDGET: u64 = 10;

/// Minimum wall-clock cap for the whole FRTS pass.
const FRTS_MIN_TIME_LIMIT_MS: u64 = 2000;

/// Maximum wall-clock cap for the whole FRTS pass.
const FRTS_MAX_TIME_LIMIT_MS: u64 = 8000;

/// Number of proven equivalences before triggering intermediate cleanup.
/// rIC3 triggers `coi_refine + bve_simplify` every 5000 replacements.
/// We use a lower threshold since our circuits tend to be smaller.
const INTERMEDIATE_CLEANUP_THRESHOLD: usize = 2000;

/// FRTS-specific simulation round count. This is intentionally higher than the
/// shared preprocessing simulation count so FRTS spends fewer SAT queries on
/// false-positive candidates.
const FRTS_SIM_ROUNDS: usize = 256;

/// Number of sequential forward-simulation transitions from one init state.
const FRTS_FORWARD_SIM_STEPS: usize = 8;

/// Number of SAT-enumerated init states used to seed FRTS signatures.
const FRTS_SAT_INIT_STATES: usize = 2;

/// Number of forward-simulation transitions from each SAT-enumerated init state.
const FRTS_SAT_FORWARD_STEPS: usize = 4;

/// Combined simulation output used by FRTS.
struct FrtsSimulation {
    signatures: FxHashMap<Var, SimSig>,
    stuck_candidates: Vec<(Var, Lit)>,
}

/// rIC3-style representative map: for each variable, the simulation-derived
/// representative literal it should be mapped to.
///
/// Unlike the pair-based `build_candidates` approach which generates O(n^2)
/// pairs, this maps each variable to a single representative in O(n) time.
/// The representative is the lowest-indexed variable in the same simulation
/// equivalence class (positive for same-signature, negated for complementary).
///
/// This mirrors rIC3's `FrTs::map` field, which is built during `FrTs::new()`.
struct RepresentativeMap {
    /// Maps a variable to its representative literal. If the representative
    /// is the variable itself, no entry is stored.
    map: FxHashMap<Var, Lit>,
}

impl RepresentativeMap {
    /// Build a representative map from simulation signatures.
    ///
    /// For each signature class, the lowest-indexed variable becomes the
    /// representative. All other variables in the class map to that representative
    /// (positive for same-signature, negated for complementary signature).
    fn build(sigs: &FxHashMap<Var, SimSig>, input_set: &FxHashSet<Var>) -> Self {
        // Group variables by signature (and complementary signature).
        // For each group, the representative is the lowest-indexed variable.
        let mut sig_to_representative: FxHashMap<SimSig, Var> = FxHashMap::default();
        let mut map = FxHashMap::default();

        // Sort variables by index so we process in increasing order.
        // This ensures the first variable seen for each signature becomes the
        // representative (lowest index).
        let mut sorted_vars: Vec<(Var, SimSig)> = sigs.iter().map(|(&v, &s)| (v, s)).collect();
        sorted_vars.sort_unstable_by_key(|(v, _)| v.0);

        for (var, sig) in sorted_vars {
            // Check if we already have a representative for this signature
            // or its complement.
            if let Some(&rep) = sig_to_representative.get(&sig) {
                if rep != var {
                    // Skip input-input pairs (no structural path)
                    if !(input_set.contains(&var) && input_set.contains(&rep)) {
                        map.insert(var, Lit::pos(rep));
                    }
                }
            } else if let Some(&rep) = sig_to_representative.get(&!sig) {
                // Complementary signature: map to negated representative
                if !(input_set.contains(&var) && input_set.contains(&rep)) {
                    map.insert(var, Lit::neg(rep));
                }
            } else {
                // First variable with this signature: becomes the representative
                sig_to_representative.insert(sig, var);
            }
        }

        RepresentativeMap { map }
    }
}

/// Running simulation summary across all FRTS simulation modes.
struct SimulationSummary {
    sigs: Vec<SimSig>,
    always_zero: Vec<bool>,
    always_one: Vec<bool>,
}

#[inline]
fn eval_pattern_lit(lit: Lit, values: &[u64]) -> u64 {
    let value = values.get(lit.var().index()).copied().unwrap_or(0);
    if lit.is_negated() {
        !value
    } else {
        value
    }
}

/// Evaluate a boolean literal against a concrete value vector.
#[inline]
fn eval_bool_lit(lit: Lit, values: &[bool]) -> bool {
    let value = values.get(lit.var().index()).copied().unwrap_or(false);
    if lit.is_negated() {
        !value
    } else {
        value
    }
}

/// Create an empty simulation summary for `n` variables.
fn new_simulation_summary(n: usize) -> SimulationSummary {
    SimulationSummary {
        sigs: vec![0u64; n],
        always_zero: vec![true; n],
        always_one: vec![true; n],
    }
}

/// Fold one packed simulation observation into the summary.
fn record_pattern_values(summary: &mut SimulationSummary, values: &[u64], mix: u64) {
    let len = summary.sigs.len().min(values.len());
    for i in 0..len {
        let value = values[i];
        summary.sigs[i] = summary.sigs[i]
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(value ^ mix);
        if value != 0 {
            summary.always_zero[i] = false;
        }
        if value != u64::MAX {
            summary.always_one[i] = false;
        }
    }
}

/// Fold one concrete boolean observation into the summary.
fn record_bool_values(summary: &mut SimulationSummary, values: &[bool], mix: u64) {
    let len = summary.sigs.len().min(values.len());
    for i in 0..len {
        let value = if values[i] { u64::MAX } else { 0 };
        summary.sigs[i] = summary.sigs[i]
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(value ^ mix);
        if value != 0 {
            summary.always_zero[i] = false;
        }
        if value != u64::MAX {
            summary.always_one[i] = false;
        }
    }
}

/// Extract known latch initial values from unit init clauses.
fn extract_init_values(ts: &Transys) -> FxHashMap<Var, bool> {
    let latch_set: FxHashSet<Var> = ts.latch_vars.iter().copied().collect();
    let mut init_values = FxHashMap::default();

    for clause in &ts.init_clauses {
        if clause.lits.len() != 1 {
            continue;
        }
        let lit = clause.lits[0];
        let var = lit.var();
        if latch_set.contains(&var) {
            init_values.insert(var, lit.is_positive());
        }
    }

    init_values
}

/// Run the high-round random/init-seeded simulation portion of FRTS.
fn accumulate_random_simulation(
    ts: &Transys,
    and_defs: &[(Var, Lit, Lit)],
    init_values: &FxHashMap<Var, bool>,
    summary: &mut SimulationSummary,
) {
    let n = ts.max_var as usize + 1;

    for round in 0..FRTS_SIM_ROUNDS {
        let mut values = vec![0u64; n];
        let seed_base = (u64::from(ts.max_var) << 32)
            ^ ((ts.num_latches as u64) << 16)
            ^ (ts.num_inputs as u64)
            ^ (round as u64).wrapping_mul(0x517C_C1B7_2722_0A95)
            ^ 0xA163_0000_0000_0042;

        for &var in &ts.latch_vars {
            if round == 0 {
                if let Some(&init_val) = init_values.get(&var) {
                    values[var.index()] = if init_val { u64::MAX } else { 0 };
                    continue;
                }
            }
            values[var.index()] = random_pattern(seed_base ^ ((var.0 as u64) << 1) ^ 0x1111);
        }

        for &var in &ts.input_vars {
            values[var.index()] = random_pattern(seed_base ^ ((var.0 as u64) << 1) ^ 0x2222);
        }

        for &(out, rhs0, rhs1) in and_defs {
            values[out.index()] = eval_pattern_lit(rhs0, &values) & eval_pattern_lit(rhs1, &values);
        }

        let mix = random_pattern(round as u64 ^ 0xDEAD_BEEF_CAFE_BABE);
        record_pattern_values(summary, &values, mix);
    }
}

/// Multi-round simulation with an FRTS-specific higher round count.
///
/// Like the shared init-seeded simulation, the first round uses known initial
/// state values for latches (from init_clauses unit clauses). Unlike the shared
/// helper, this runs more rounds so FRTS gets sharper signatures and wastes
/// fewer SAT-budgeted checks on accidental collisions.
#[allow(dead_code)]
fn simulate_frts_init_seeded(ts: &Transys) -> Vec<SimSig> {
    let and_defs = sorted_and_defs(ts);
    let init_values = extract_init_values(ts);
    let mut summary = new_simulation_summary(ts.max_var as usize + 1);
    accumulate_random_simulation(ts, &and_defs, &init_values, &mut summary);
    summary.sigs
}

/// Build a SAT solver over init constraints for init-state enumeration.
fn build_init_solver(ts: &Transys) -> Box<dyn SatSolver> {
    let mut solver = SolverBackend::Z4Sat.make_solver(ts.max_var + 1);
    solver.ensure_vars(ts.max_var);
    for clause in &ts.init_clauses {
        solver.add_clause(&clause.lits);
    }
    for &constraint in &ts.constraint_lits {
        solver.add_clause(&[constraint]);
    }
    solver
}

/// Enumerate up to `max_states` valid init states via SAT.
fn enumerate_init_states(ts: &Transys, max_states: usize) -> Vec<FxHashMap<Var, bool>> {
    if ts.latch_vars.is_empty() || max_states == 0 {
        return Vec::new();
    }

    let mut solver = build_init_solver(ts);
    let mut states = Vec::new();

    for _ in 0..max_states {
        match solver.solve(&[]) {
            SatResult::Sat => {
                let mut state = FxHashMap::default();
                let mut blocking_clause = Vec::with_capacity(ts.latch_vars.len());

                for &latch in &ts.latch_vars {
                    let value = solver.value(Lit::pos(latch)).unwrap_or(false);
                    state.insert(latch, value);
                    blocking_clause.push(if value { Lit::neg(latch) } else { Lit::pos(latch) });
                }

                states.push(state);
                if blocking_clause.is_empty() {
                    break;
                }
                solver.add_clause(&blocking_clause);
            }
            SatResult::Unsat | SatResult::Unknown => break,
        }
    }

    states
}

/// Select one concrete init state for the longer sequential forward simulation.
fn select_forward_init_state(
    ts: &Transys,
    init_values: &FxHashMap<Var, bool>,
    init_states: &[FxHashMap<Var, bool>],
) -> Vec<bool> {
    let mut state = vec![false; ts.max_var as usize + 1];

    if let Some(first_state) = init_states.first() {
        for &latch in &ts.latch_vars {
            state[latch.index()] = first_state.get(&latch).copied().unwrap_or(false);
        }
        return state;
    }

    for &latch in &ts.latch_vars {
        if let Some(&value) = init_values.get(&latch) {
            state[latch.index()] = value;
        }
    }

    state
}

/// Evaluate one concrete sequential step and compute the next latch state.
fn forward_simulate_step(
    ts: &Transys,
    and_defs: &[(Var, Lit, Lit)],
    latch_state: &[bool],
    step: usize,
    sim_seed: u64,
) -> (Vec<bool>, Vec<bool>) {
    let n = ts.max_var as usize + 1;
    let mut values = vec![false; n];

    for &latch in &ts.latch_vars {
        values[latch.index()] = latch_state.get(latch.index()).copied().unwrap_or(false);
    }

    let seed_base = sim_seed
        ^ (u64::from(ts.max_var) << 32)
        ^ ((ts.num_latches as u64) << 16)
        ^ (ts.num_inputs as u64)
        ^ (step as u64).wrapping_mul(0x517C_C1B7_2722_0A95)
        ^ 0xC1A0_0000_0000_00F4;

    for &var in &ts.input_vars {
        values[var.index()] = random_pattern(seed_base ^ ((var.0 as u64) << 1) ^ 0x3333) & 1 != 0;
    }

    for &(out, rhs0, rhs1) in and_defs {
        values[out.index()] = eval_bool_lit(rhs0, &values) && eval_bool_lit(rhs1, &values);
    }

    let mut next_latch_state = vec![false; n];
    for &latch in &ts.latch_vars {
        next_latch_state[latch.index()] = if let Some(&next_lit) = ts.next_state.get(&latch) {
            eval_bool_lit(next_lit, &values)
        } else {
            latch_state.get(latch.index()).copied().unwrap_or(false)
        };
    }

    (values, next_latch_state)
}

/// Forward-simulate a concrete init state and merge all observations into the summary.
fn accumulate_forward_simulation(
    ts: &Transys,
    and_defs: &[(Var, Lit, Lit)],
    init_state: &[bool],
    transitions: usize,
    sim_seed: u64,
    summary: &mut SimulationSummary,
) {
    let mut current_state = init_state.to_vec();

    for step in 0..=transitions {
        let (values, next_state) = forward_simulate_step(ts, and_defs, &current_state, step, sim_seed);
        let mix = random_pattern(
            sim_seed
                ^ (step as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
                ^ 0xABCD_EF01_2345_6789,
        );
        record_bool_values(summary, &values, mix);
        if step == transitions {
            break;
        }
        current_state = next_state;
    }
}

fn live_signal_vars(ts: &Transys) -> FxHashSet<Var> {
    let mut live = FxHashSet::default();
    live.extend(ts.latch_vars.iter().copied());
    live.extend(ts.input_vars.iter().copied());
    live.extend(ts.and_defs.keys().copied());
    live
}

/// Extract signal signatures for all live FRTS-visible variables.
fn build_signal_signature_map(ts: &Transys, sigs: &[SimSig]) -> FxHashMap<Var, SimSig> {
    let mut result = FxHashMap::default();

    for &latch in &ts.latch_vars {
        let sig = sigs.get(latch.index()).copied().unwrap_or(0);
        result.insert(latch, sig);
    }

    for &gate in ts.and_defs.keys() {
        let sig = sigs.get(gate.index()).copied().unwrap_or(0);
        result.insert(gate, sig);
    }

    for &input in &ts.input_vars {
        let sig = sigs.get(input.index()).copied().unwrap_or(0);
        result.insert(input, sig);
    }

    result
}

/// Collect variables that looked stuck-at-0 or stuck-at-1 across all observations.
fn collect_stuck_candidates(ts: &Transys, summary: &SimulationSummary) -> Vec<(Var, Lit)> {
    let mut stuck = Vec::new();

    for var in live_signal_vars(ts) {
        if var == Var::CONST {
            continue;
        }

        let idx = var.index();
        let always_zero = summary.always_zero.get(idx).copied().unwrap_or(false);
        let always_one = summary.always_one.get(idx).copied().unwrap_or(false);

        if always_zero && !always_one {
            stuck.push((var, Lit::FALSE));
        } else if always_one && !always_zero {
            stuck.push((var, Lit::TRUE));
        }
    }

    stuck.sort_unstable_by(|(var_a, const_a), (var_b, const_b)| {
        var_b
            .0
            .cmp(&var_a.0)
            .then_with(|| const_a.code().cmp(&const_b.code()))
    });
    stuck
}

/// Run all FRTS simulation modes and return signatures plus stuck-at candidates.
fn run_frts_simulation(ts: &Transys) -> FrtsSimulation {
    let n = ts.max_var as usize + 1;
    let and_defs = sorted_and_defs(ts);
    let init_values = extract_init_values(ts);
    let init_states = enumerate_init_states(ts, FRTS_SAT_INIT_STATES);
    let mut summary = new_simulation_summary(n);

    accumulate_random_simulation(ts, &and_defs, &init_values, &mut summary);

    let forward_init_state = select_forward_init_state(ts, &init_values, &init_states);
    accumulate_forward_simulation(
        ts,
        &and_defs,
        &forward_init_state,
        FRTS_FORWARD_SIM_STEPS,
        0xF175_F0A1_D000_0001,
        &mut summary,
    );

    for (state_idx, init_state) in init_states.iter().enumerate() {
        let mut latch_state = vec![false; n];
        for &latch in &ts.latch_vars {
            latch_state[latch.index()] = init_state.get(&latch).copied().unwrap_or(false);
        }
        accumulate_forward_simulation(
            ts,
            &and_defs,
            &latch_state,
            FRTS_SAT_FORWARD_STEPS,
            0x5A7F_0000_0000_0000 ^ (state_idx as u64).wrapping_mul(0x517C_C1B7_2722_0A95),
            &mut summary,
        );
    }

    FrtsSimulation {
        signatures: build_signal_signature_map(ts, &summary.sigs),
        stuck_candidates: collect_stuck_candidates(ts, &summary),
    }
}

/// Collect signatures for all variables in the transition system
/// (latches + AND gate outputs + inputs). This gives FRTS broader
/// coverage than SCORR's latch-only or forward_reduce's gate-only scope.
///
/// Uses random, init-seeded, sequential-forward, and SAT-seeded simulation for
/// better candidate quality across both combinational and reachable-state views.
#[allow(dead_code)]
fn all_signal_signatures(ts: &Transys) -> FxHashMap<Var, SimSig> {
    run_frts_simulation(ts).signatures
}

/// Build a SAT solver over the transition relation and constraints.
fn build_trans_solver(ts: &Transys) -> Box<dyn SatSolver> {
    let mut solver = SolverBackend::Z4Sat.make_solver(ts.max_var + 1);
    solver.ensure_vars(ts.max_var);
    for clause in &ts.trans_clauses {
        solver.add_clause(&clause.lits);
    }
    for &constraint in &ts.constraint_lits {
        solver.add_clause(&[constraint]);
    }
    solver
}

/// Check if two signals are combinationally equivalent using budget-limited SAT.
///
/// For each mismatch case (a=true,b=false and a=false,b=true for positive
/// equivalence, or the complement for negated), run SAT with the conflict
/// budget. Returns true only if both mismatch cases are UNSAT.
/// Returns false if either is SAT (not equivalent) or Unknown (too hard).
fn budget_equiv_check(solver: &mut dyn SatSolver, a: Lit, b: Lit, negated: bool) -> bool {
    let cases = if negated {
        [(a, b), (!a, !b)]
    } else {
        [(a, !b), (!a, b)]
    };

    for (lhs, rhs) in cases {
        match solver.solve_with_budget(&[lhs, rhs], CONFLICT_BUDGET) {
            SatResult::Unsat => {}
            SatResult::Sat | SatResult::Unknown => return false,
        }
    }
    true
}

/// Add equivalence clauses to the solver after proving two signals equivalent.
///
/// For positive equivalence (a <=> b): add (!a | b) and (a | !b).
/// For negated equivalence (a <=> !b): add (!a | !b) and (a | b).
///
/// This strengthens the solver for subsequent equivalence checks, so proofs
/// that depend on earlier equivalences become trivially UNSAT instead of
/// requiring the solver to rediscover the relationship. rIC3 calls
/// `add_eq(lv, m)` after each proven equivalence in its FRTS loop.
#[inline]
fn add_equiv_to_solver(solver: &mut dyn SatSolver, a: Lit, b: Lit, negated: bool) {
    if negated {
        solver.add_clause(&[!a, !b]);
        solver.add_clause(&[a, b]);
    } else {
        solver.add_clause(&[!a, b]);
        solver.add_clause(&[a, !b]);
    }
}

/// Convert a proven constant value into the corresponding unit literal for `var`.
#[inline]
fn literal_for_constant_value(var: Var, constant: Lit) -> Lit {
    if constant == Lit::TRUE {
        Lit::pos(var)
    } else {
        Lit::neg(var)
    }
}

/// Add a proven constant assignment to the solver.
#[inline]
fn add_constant_to_solver(solver: &mut dyn SatSolver, var: Var, constant: Lit) {
    solver.add_clause(&[literal_for_constant_value(var, constant)]);
}

/// Check whether `var` is forced to a constant using a budget-limited SAT query.
fn budget_constant_check(solver: &mut dyn SatSolver, var: Var, constant: Lit) -> bool {
    let opposite = !literal_for_constant_value(var, constant);
    match solver.solve_with_budget(&[opposite], CONFLICT_BUDGET) {
        SatResult::Unsat => true,
        SatResult::Sat | SatResult::Unknown => false,
    }
}

/// Compute the size-scaled FRTS deadline budget for this transition system.
fn frts_time_limit(ts: &Transys) -> Duration {
    let num_signals = ts.latch_vars.len() + ts.input_vars.len() + ts.and_defs.len();
    let millis = ((num_signals as u64) * 5)
        .max(FRTS_MIN_TIME_LIMIT_MS)
        .min(FRTS_MAX_TIME_LIMIT_MS);
    Duration::from_millis(millis)
}

/// Check whether a variable is a "leaf" in the AIG — an input or a latch
/// with no AND gate definition. Leaf variables have no structural relationship
/// to other variables through the combinational logic, so they can never be
/// proven equivalent to another signal through transition-relation SAT queries.
///
/// rIC3 skips leaf variables in its FRTS loop via `self.ts.rel.is_leaf(v)`.
#[inline]
fn is_leaf_var(var: Var, ts: &Transys) -> bool {
    !ts.and_defs.contains_key(&var)
}

/// Apply intermediate cleanup: substitute, COI reduce, and BVE simplify.
///
/// rIC3 triggers this every 5000 replacements. We trigger at
/// `INTERMEDIATE_CLEANUP_THRESHOLD` (2000) since our circuits tend to be smaller.
/// After cleanup, the solver must be rebuilt because the transition system changed.
fn apply_intermediate_cleanup(
    current: &mut Transys,
    subst: &mut FxHashMap<Var, Lit>,
    live_vars: &mut FxHashSet<Var>,
    solver: &mut Box<dyn SatSolver>,
    total_eliminated: &mut usize,
    batch_eliminated: &mut usize,
) {
    *total_eliminated += subst.len();
    *current = apply_substitution(current, subst);
    *current = current.coi_reduce();
    *current = bounded_variable_elimination(current).0;
    *live_vars = live_signal_vars(current);
    subst.clear();
    *batch_eliminated = 0;
    *solver = build_trans_solver(current);
}

/// Run one FRTS iteration using rIC3-style map-based linear traversal.
///
/// Instead of building O(n^2) candidate pairs, builds a representative map
/// from simulation (each variable maps to its lowest-indexed equivalent),
/// then iterates through variables linearly in increasing order. For each
/// variable with a mapped representative, checks equivalence with a single
/// budget-limited SAT query.
///
/// Key techniques (matching rIC3's `fr()` loop):
/// - Map-based candidate tracking: O(n) variables checked, not O(n^2) pairs
/// - Skips leaf variables (inputs/latches without AND definitions)
/// - Feeds proven equivalences back to the solver (`add_eq`)
/// - Intermediate COI + BVE cleanup every INTERMEDIATE_CLEANUP_THRESHOLD merges
/// - Stuck-at constant candidates verified after equivalence candidates
/// - Time-limited to avoid blocking the preprocessing pipeline
fn frts_one_iteration(ts: &Transys, deadline: Instant) -> (Transys, usize) {
    if Instant::now() >= deadline {
        return (ts.clone(), 0);
    }

    let simulation = run_frts_simulation(ts);
    let input_set: FxHashSet<Var> = ts.input_vars.iter().copied().collect();
    let rep_map = RepresentativeMap::build(&simulation.signatures, &input_set);
    let stuck_candidates = simulation.stuck_candidates;

    if rep_map.map.is_empty() && stuck_candidates.is_empty() {
        return (ts.clone(), 0);
    }

    let mut current = ts.clone();
    let mut live_vars = live_signal_vars(&current);
    let mut solver = build_trans_solver(&current);
    let mut subst: FxHashMap<Var, Lit> = FxHashMap::default();
    let mut batch_eliminated = 0usize;
    let mut total_eliminated = 0usize;

    // rIC3-style linear iteration: iterate through all variables in increasing
    // order, checking each against its simulation-derived representative.
    // This is O(n) SAT calls in the best case vs O(n^2) pair enumeration.
    let max_var_idx = current.max_var;
    for var_idx in 1..=max_var_idx {
        if Instant::now() >= deadline {
            break;
        }

        let var = Var(var_idx);

        // Skip leaf variables — inputs and latches have no AND gate definition,
        // so they cannot be structurally proven equivalent via transition relation.
        // rIC3: `if self.ts.rel.is_leaf(v) { continue; }`
        if is_leaf_var(var, &current) {
            continue;
        }

        // Look up the simulation-derived representative for this variable.
        let Some(&rep_lit) = rep_map.map.get(&var) else {
            continue;
        };

        // Skip if either variable has already been substituted or eliminated.
        if !live_vars.contains(&var) || !live_vars.contains(&rep_lit.var()) {
            continue;
        }
        if subst.contains_key(&var) || subst.contains_key(&rep_lit.var()) {
            continue;
        }

        // Determine equivalence polarity: positive if rep_lit is positive,
        // negated if rep_lit is negative.
        let negated = rep_lit.is_negated();
        let rep_var = rep_lit.var();

        // Budget-limited SAT check: is var equivalent to rep_var (with polarity)?
        // rIC3 uses constraint clauses [m, lv] + [!m, !lv] with restart limit 1.
        // We use two assumption-based calls (equivalent semantics).
        if !budget_equiv_check(&mut *solver, Lit::pos(rep_var), Lit::pos(var), negated) {
            continue;
        }

        // Proven equivalent! Feed back to solver and record substitution.
        // rIC3: `self.solver.add_eq(lv, m)`
        add_equiv_to_solver(&mut *solver, Lit::pos(rep_var), Lit::pos(var), negated);

        // Map the higher-indexed variable to the lower-indexed representative.
        // Chase any existing substitutions on the representative.
        let resolved_rep = subst_lit(Lit::pos(rep_var), &subst);
        let replacement = if negated { !resolved_rep } else { resolved_rep };
        if replacement != Lit::pos(var) {
            subst.insert(var, replacement);
            batch_eliminated += 1;
        }

        // rIC3: intermediate cleanup every 5000 replacements.
        if batch_eliminated >= INTERMEDIATE_CLEANUP_THRESHOLD {
            apply_intermediate_cleanup(
                &mut current,
                &mut subst,
                &mut live_vars,
                &mut solver,
                &mut total_eliminated,
                &mut batch_eliminated,
            );
        }
    }

    // Phase 2: stuck-at constant candidates (simulation-derived).
    for (var, constant) in stuck_candidates {
        if Instant::now() >= deadline {
            break;
        }

        if !live_vars.contains(&var) || subst.contains_key(&var) {
            continue;
        }

        if !budget_constant_check(&mut *solver, var, constant) {
            continue;
        }

        add_constant_to_solver(&mut *solver, var, constant);
        subst.insert(var, constant);
        batch_eliminated += 1;

        if batch_eliminated >= INTERMEDIATE_CLEANUP_THRESHOLD {
            apply_intermediate_cleanup(
                &mut current,
                &mut subst,
                &mut live_vars,
                &mut solver,
                &mut total_eliminated,
                &mut batch_eliminated,
            );
        }
    }

    if subst.is_empty() {
        (current, total_eliminated)
    } else {
        total_eliminated += subst.len();
        (apply_substitution(&current, &subst), total_eliminated)
    }
}

/// FRTS preprocessing pass: iterative functional reduction.
///
/// Runs up to MAX_FRTS_ITERATIONS rounds of simulate-verify-substitute.
/// Each round re-simulates the reduced circuit, which can expose new
/// equivalences after earlier substitutions. The entire pass is time-limited
/// using a size-scaled budget so larger circuits get more preprocessing time.
///
/// Returns the reduced transition system and total number of eliminated signals.
pub(crate) fn frts(ts: &Transys) -> (Transys, usize) {
    if ts.and_defs.len() + ts.latch_vars.len() < 4 {
        return (ts.clone(), 0);
    }

    let deadline = Instant::now() + frts_time_limit(ts);
    let mut current = ts.clone();
    let mut total_eliminated = 0usize;

    for _ in 0..MAX_FRTS_ITERATIONS {
        if Instant::now() >= deadline {
            break;
        }

        let (reduced, eliminated) = frts_one_iteration(&current, deadline);
        total_eliminated += eliminated;
        if eliminated == 0 {
            break;
        }
        current = reduced.coi_reduce();
    }

    (current, total_eliminated)
}
