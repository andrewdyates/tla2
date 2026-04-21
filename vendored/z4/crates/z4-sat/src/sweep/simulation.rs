// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random simulation-based equivalence candidate finding.
//!
//! Assigns random boolean values to variables incrementally with unit
//! propagation between decisions. Variables that receive the same simulation
//! value across all rounds are equivalence candidates.
//!
//! This is a cheap pre-filter for kitten probing: it reduces the number of
//! expensive SAT-based equivalence checks by quickly eliminating obviously
//! non-equivalent variable pairs.
//!
//! Algorithm:
//! 1. For each round, start with all variables unassigned (except level-0 fixed)
//! 2. Iterate variables in random order; for each unassigned variable:
//!    a. Assign it a random value
//!    b. Forward-propagate: scan clauses for unit implications, repeat to fixpoint
//! 3. Record each variable's final value as one bit of its 64-bit signature
//! 4. Group variables by signature (with complement folding for ¬-equivalences)
//! 5. Return candidate equivalence classes for kitten verification
//!
//! Reference: circuit equivalence checking / SAT sweeping literature.

use std::collections::HashMap;

use super::Sweeper;
use crate::clause_arena::ClauseArena;
use crate::literal::Literal;

/// Number of random simulation rounds.
/// Each round produces one bit of the per-variable signature.
/// 64 rounds = 64-bit signature, giving 2^-64 false-positive probability
/// for any single pair.
const MAX_SIMULATION_ROUNDS: u32 = 64;

/// Maximum number of forward-propagation passes per decision.
/// Propagation reaches a fixpoint quickly; this limits pathological cases.
const MAX_PROPAGATION_PASSES: u32 = 10;

/// Simple XorShift64 PRNG for fast random simulation.
/// No external dependencies; deterministic given a seed.
struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 { 0x5A5A_5A5A_5A5A_5A5A } else { seed },
        }
    }

    #[inline]
    fn next(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    #[inline]
    fn next_bool(&mut self) -> bool {
        (self.next() & 1) != 0
    }

    /// Fisher-Yates shuffle of a slice.
    fn shuffle(&mut self, slice: &mut [usize]) {
        let n = slice.len();
        for i in (1..n).rev() {
            let j = (self.next() as usize) % (i + 1);
            slice.swap(i, j);
        }
    }
}

/// Assign a literal true in the simulation values buffer.
#[inline]
fn sim_assign(sim_vals: &mut [i8], lit: Literal) {
    let li = lit.index();
    let neg_li = lit.negated().index();
    if li < sim_vals.len() && neg_li < sim_vals.len() {
        sim_vals[li] = 1;
        sim_vals[neg_li] = -1;
    }
}

impl Sweeper {
    /// Find equivalence candidate classes via random simulation.
    ///
    /// Returns equivalence classes as `Vec<Vec<u32>>` where each inner vec
    /// contains signed literal indices that had identical simulation signatures.
    /// The caller should verify these candidates with kitten probing.
    ///
    /// Signed literal convention matches the existing probe code: each class
    /// member is the literal (positive or negative) that was true for that
    /// variable in the final simulation round.
    pub(super) fn find_candidates_by_simulation(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
    ) -> Vec<Vec<u32>> {
        let num_vars = self.num_vars;
        if num_vars == 0 {
            return Vec::new();
        }

        // Collect clause data once.
        // Skip garbage, empty, and large learned clauses (matching COI filter).
        let clause_data: Vec<Vec<Literal>> = clauses
            .indices()
            .filter(|&idx| {
                !clauses.is_garbage(idx)
                    && !clauses.is_empty_clause(idx)
                    && !(clauses.is_learned(idx) && clauses.len_of(idx) > 2)
            })
            .map(|idx| clauses.literals(idx).to_vec())
            .collect();

        if clause_data.is_empty() {
            return Vec::new();
        }

        let num_lits = num_vars * 2;
        let mut signatures = vec![0u64; num_vars];
        let mut sim_vals = vec![0i8; num_lits];
        let mut rng = XorShift64::new(0xDEAD_BEEF_CAFE_1234);

        // Variable ordering buffer (shuffled each round).
        let mut var_order: Vec<usize> = (0..num_vars).collect();

        for round in 0..MAX_SIMULATION_ROUNDS {
            // 1. Reset simulation values. Copy level-0 fixed assignments.
            for v in sim_vals.iter_mut() {
                *v = 0;
            }
            for var in 0..num_vars {
                let pos_idx = var * 2;
                let neg_idx = var * 2 + 1;
                if pos_idx < vals.len() && vals[pos_idx] != 0 {
                    sim_vals[pos_idx] = vals[pos_idx];
                    sim_vals[neg_idx] = vals[neg_idx];
                }
            }

            // 2. Shuffle variable order for this round.
            rng.shuffle(&mut var_order);

            // 3. Assign variables in random order with propagation.
            for &var in &var_order {
                let pos_idx = var * 2;
                if pos_idx >= num_lits {
                    continue;
                }
                // Skip already-assigned variables (fixed or propagated).
                if sim_vals[pos_idx] != 0 {
                    continue;
                }

                // Random decision.
                let pos_lit = Literal(pos_idx as u32);
                let neg_lit = Literal((pos_idx as u32) | 1);
                if rng.next_bool() {
                    sim_assign(&mut sim_vals, pos_lit);
                } else {
                    sim_assign(&mut sim_vals, neg_lit);
                }

                // Forward propagate from this decision.
                Self::simulate_propagate(&clause_data, &mut sim_vals, num_lits);
            }

            // 4. Record signature bit.
            let bit = 1u64 << (round & 63);
            for var in 0..num_vars {
                let pos_idx = var * 2;
                if pos_idx < num_lits && sim_vals[pos_idx] > 0 {
                    signatures[var] |= bit;
                }
            }
        }

        // 5. Group variables by canonical signature.
        // Complement folding: if sig(A) = !sig(B), then A ≡ ¬B.
        // Canonical signature = min(sig, !sig). If we use !sig, negate the literal.
        let mut classes: HashMap<u64, Vec<u32>> = HashMap::new();

        for var in 0..num_vars {
            let pos_idx = var * 2;
            // Skip assigned variables.
            if pos_idx < vals.len() && vals[pos_idx] != 0 {
                continue;
            }
            // Skip frozen variables.
            if var < frozen.len() && frozen[var] > 0 {
                continue;
            }

            let sig = signatures[var];
            let (canon_sig, signed_lit) = if sig <= !sig {
                let lit = if sim_vals[pos_idx] > 0 {
                    pos_idx as u32
                } else {
                    (pos_idx as u32) | 1
                };
                (sig, lit)
            } else {
                // Complement: negate the literal polarity.
                let lit = if sim_vals[pos_idx] > 0 {
                    (pos_idx as u32) | 1
                } else {
                    pos_idx as u32
                };
                (!sig, lit)
            };

            classes.entry(canon_sig).or_default().push(signed_lit);
        }

        // 6. Filter: keep only classes with 2+ members.
        classes
            .into_values()
            .filter(|class| class.len() >= 2)
            .collect()
    }

    /// Forward-propagate unit implications in the simulation assignment.
    /// Scans all clauses, looking for clauses where exactly one literal is
    /// unassigned and all others are falsified -> force the unassigned literal.
    /// Repeats until fixpoint or pass limit.
    fn simulate_propagate(clause_data: &[Vec<Literal>], sim_vals: &mut [i8], num_lits: usize) {
        for _pass in 0..MAX_PROPAGATION_PASSES {
            let mut propagated = false;

            for lits in clause_data {
                let mut falsified = 0u32;
                let mut satisfied = false;
                let mut unassigned_lit = Literal(0);
                let mut unassigned_count = 0u32;

                for &lit in lits.iter() {
                    let li = lit.index();
                    if li >= num_lits {
                        continue;
                    }
                    let v = sim_vals[li];
                    if v > 0 {
                        satisfied = true;
                        break;
                    } else if v < 0 {
                        falsified += 1;
                    } else {
                        unassigned_count += 1;
                        unassigned_lit = lit;
                    }
                }

                if satisfied {
                    continue;
                }

                // Unit clause under current simulation: force the remaining literal.
                if unassigned_count == 1 && falsified as usize == lits.len() - 1 {
                    let li = unassigned_lit.index();
                    if li < num_lits && sim_vals[li] == 0 {
                        sim_assign(sim_vals, unassigned_lit);
                        propagated = true;
                    }
                }
            }

            if !propagated {
                break;
            }
        }
    }
}
