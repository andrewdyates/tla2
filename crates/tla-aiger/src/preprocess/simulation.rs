// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Multi-round random simulation for equivalence candidate generation.
//!
//! Runs multiple simulation rounds with random input patterns to compute
//! per-variable signatures. Variables with matching (or complementary)
//! signatures are likely equivalent and become candidates for SAT-based
//! verification in SCORR and forward reduction.
//!
//! Supports two simulation modes:
//! - **Random simulation**: All variables get random patterns each round.
//! - **Init-seeded simulation**: Round 0 seeds latches with known init values
//!   from unit clauses.
//!
//! SAT-seeded simulation (z4-sat init enumeration + forward simulation) is in
//! the companion module [`super::simulation_sat`].

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

use super::substitution::sorted_and_defs;

/// Number of 64-bit simulation rounds for equivalence candidate generation.
/// rIC3 generates ~640 bit-patterns via SAT-driven init + reachable-state
/// simulation. We use 256 packed 64-bit rounds (= 16,384 bit-patterns) for
/// strong candidate precision. Higher round counts reduce false-positive
/// equivalence candidates, meaning fewer wasted SAT queries in SCORR and FRTS.
const SIM_ROUNDS: usize = 256;

/// Signature type: concatenated hash of all simulation rounds.
pub(crate) type SimSig = u64;

pub(super) fn random_pattern(seed: u64) -> u64 {
    let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
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

/// Run a single simulation round with the given round index for seed variation.
fn simulate_one_round(ts: &Transys, round: usize) -> Vec<u64> {
    let mut values = vec![0u64; ts.max_var as usize + 1];
    let seed_base = (u64::from(ts.max_var) << 32)
        ^ ((ts.num_latches as u64) << 16)
        ^ (ts.num_inputs as u64)
        ^ (round as u64).wrapping_mul(0x517C_C1B7_2722_0A95)
        ^ 0xA163_0000_0000_0042;

    for &var in &ts.latch_vars {
        values[var.index()] = random_pattern(seed_base ^ ((var.0 as u64) << 1) ^ 0x1111);
    }
    for &var in &ts.input_vars {
        values[var.index()] = random_pattern(seed_base ^ ((var.0 as u64) << 1) ^ 0x2222);
    }

    for (out, rhs0, rhs1) in sorted_and_defs(ts) {
        values[out.index()] = eval_pattern_lit(rhs0, &values) & eval_pattern_lit(rhs1, &values);
    }

    values
}

/// Multi-round simulation: run `SIM_ROUNDS` rounds and combine signatures.
///
/// Each round produces a 64-bit pattern per variable. We hash across rounds to
/// produce a single `SimSig` per variable. More rounds = fewer false-positive
/// equivalence candidates = fewer wasted SAT queries.
///
/// Reference: rIC3 uses SAT-driven simulation generating ~640 bit-patterns.
/// We use SIM_ROUNDS (256) packed 64-bit rounds for 16,384 bit-patterns of
/// discrimination, giving very strong candidate precision.
pub(crate) fn simulate_multi_round(ts: &Transys) -> Vec<SimSig> {
    let n = ts.max_var as usize + 1;
    let mut sigs = vec![0u64; n];

    for round in 0..SIM_ROUNDS {
        let values = simulate_one_round(ts, round);
        let mix = random_pattern(round as u64 ^ 0xDEAD_BEEF_CAFE_BABE);
        for i in 0..n.min(values.len()) {
            // Combine each round's value into the running signature using
            // a hash-mix so that patterns from different rounds contribute
            // independent bits rather than just being XOR'd.
            sigs[i] = sigs[i]
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(values[i] ^ mix);
        }
    }

    sigs
}

/// Extract known initial values from init_clauses.
///
/// Scans for unit clauses (single-literal clauses) which definitively
/// constrain a latch's initial value. Returns a map from latch var to
/// its known initial boolean value.
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

/// Single simulation round seeded with known initial state values.
///
/// For round 0, latches with known init values get all-zero or all-one
/// 64-bit patterns (matching their init value), while unknown latches and
/// inputs get random patterns. This biases the first round toward the
/// actual initial state, helping SCORR discover equivalences that hold
/// from init. Subsequent rounds use pure random patterns.
fn simulate_one_round_init_seeded(
    ts: &Transys,
    round: usize,
    init_values: &FxHashMap<Var, bool>,
) -> Vec<u64> {
    let mut values = vec![0u64; ts.max_var as usize + 1];
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

    for (out, rhs0, rhs1) in sorted_and_defs(ts) {
        values[out.index()] = eval_pattern_lit(rhs0, &values) & eval_pattern_lit(rhs1, &values);
    }

    values
}

/// Multi-round simulation with init-seeded first round.
///
/// Like [`simulate_multi_round`] but the first round uses known initial
/// state values for latches (from init_clauses unit clauses). This improves
/// equivalence candidate quality for SCORR by incorporating knowledge of
/// the actual initial state.
pub(crate) fn simulate_multi_round_init_seeded(ts: &Transys) -> Vec<SimSig> {
    let n = ts.max_var as usize + 1;
    let mut sigs = vec![0u64; n];
    let init_values = extract_init_values(ts);

    for round in 0..SIM_ROUNDS {
        let values = simulate_one_round_init_seeded(ts, round, &init_values);
        let mix = random_pattern(round as u64 ^ 0xDEAD_BEEF_CAFE_BABE);
        for i in 0..n.min(values.len()) {
            sigs[i] = sigs[i]
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(values[i] ^ mix);
        }
    }

    sigs
}

// ---------------------------------------------------------------------------
// Signature extraction and candidate building
// ---------------------------------------------------------------------------

pub(crate) fn latch_signatures(ts: &Transys) -> FxHashMap<Var, SimSig> {
    let sigs = simulate_multi_round(ts);
    let mut result = FxHashMap::default();
    for &latch in &ts.latch_vars {
        if let Some(&next_lit) = ts.next_state.get(&latch) {
            let sig = sigs.get(next_lit.var().index()).copied().unwrap_or(0);
            let sig = if next_lit.is_negated() { !sig } else { sig };
            result.insert(latch, sig);
        }
    }
    result
}

/// Latch signatures using init-seeded simulation.
///
/// Uses [`simulate_multi_round_init_seeded`] so the first round
/// incorporates known initial state values, improving candidate quality.
pub(crate) fn latch_signatures_init_seeded(ts: &Transys) -> FxHashMap<Var, SimSig> {
    let sigs = simulate_multi_round_init_seeded(ts);
    let mut result = FxHashMap::default();
    for &latch in &ts.latch_vars {
        if let Some(&next_lit) = ts.next_state.get(&latch) {
            let sig = sigs.get(next_lit.var().index()).copied().unwrap_or(0);
            let sig = if next_lit.is_negated() { !sig } else { sig };
            result.insert(latch, sig);
        }
    }
    result
}

pub(crate) fn gate_signatures(ts: &Transys) -> FxHashMap<Var, SimSig> {
    let sigs = simulate_multi_round(ts);
    let mut result = FxHashMap::default();
    for &gate in ts.and_defs.keys() {
        let value = sigs.get(gate.index()).copied().unwrap_or(0);
        result.insert(gate, value);
    }
    result
}

pub(crate) fn build_candidates(sigs: &FxHashMap<Var, SimSig>) -> Vec<(Var, Var, bool)> {
    let mut groups: FxHashMap<SimSig, Vec<Var>> = FxHashMap::default();
    for (&var, &sig) in sigs {
        groups.entry(sig).or_default().push(var);
    }
    for vars in groups.values_mut() {
        vars.sort_unstable_by_key(|var| var.0);
    }

    let mut seen = FxHashSet::default();
    let mut candidates = Vec::new();

    for vars in groups.values() {
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let x = vars[i];
                let y = vars[j];
                if seen.insert((x.0, y.0, false)) {
                    candidates.push((x, y, false));
                }
            }
        }
    }

    let mut sig_keys: Vec<SimSig> = groups.keys().copied().collect();
    sig_keys.sort_unstable();
    for sig in sig_keys {
        let comp = !sig;
        if sig >= comp {
            continue;
        }
        if let (Some(left), Some(right)) = (groups.get(&sig), groups.get(&comp)) {
            for &a in left {
                for &b in right {
                    let (x, y) = if a < b { (a, b) } else { (b, a) };
                    if x != y && seen.insert((x.0, y.0, true)) {
                        candidates.push((x, y, true));
                    }
                }
            }
        }
    }

    candidates.sort_unstable_by_key(|(x, y, negated)| (y.0, x.0, *negated as u8));
    candidates
}
