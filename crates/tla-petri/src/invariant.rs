// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Place invariant computation for structural Petri net analysis.
//!
//! Computes semi-positive P-invariants using the Farkas algorithm
//! (Fourier-Motzkin elimination on the incidence matrix). A P-invariant
//! is a non-negative integer vector y ≥ 0 satisfying y^T · C = 0, where
//! C is the incidence matrix. The key property: for any reachable marking
//! m, y^T · m = y^T · m₀ (invariant quantity).
//!
//! Structural bounds derived from P-invariants enable answering MCC
//! examinations without state space exploration:
//! - **OneSafe**: prove all places ≤ 1 token structurally
//! - **UpperBounds**: tight bounds on place-set token sums

use crate::petri_net::PetriNet;

/// A semi-positive P-invariant: y ≥ 0 with y^T · C = 0.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PInvariant {
    /// Weight for each place (indexed by place index). All values ≥ 0.
    pub weights: Vec<u64>,
    /// Conserved quantity: y^T · m₀. Equal to y^T · m for all reachable m.
    pub token_count: u64,
}

/// Maximum augmented row count before aborting the Farkas algorithm.
/// Prevents combinatorial explosion on pathological nets.
const MAX_ROWS: usize = 10_000;

/// Compute semi-positive P-invariants via the Farkas algorithm.
///
/// Returns all minimal semi-positive P-invariants discovered. For nets
/// with no transitions, returns a unit invariant per place (every place
/// is trivially invariant). Aborts gracefully if intermediate row count
/// exceeds [`MAX_ROWS`], returning whatever invariants were found.
pub(crate) fn compute_p_invariants(net: &PetriNet) -> Vec<PInvariant> {
    let np = net.num_places();
    let nt = net.num_transitions();

    if np == 0 {
        return vec![];
    }

    // No transitions: every place has constant token count.
    if nt == 0 {
        return (0..np)
            .map(|p| {
                let mut weights = vec![0u64; np];
                weights[p] = 1;
                PInvariant {
                    token_count: net.initial_marking[p],
                    weights,
                }
            })
            .collect();
    }

    let c = incidence_matrix(net);
    farkas_elimination(&c, np, nt, &net.initial_marking)
}

/// Build the incidence matrix C[p][t] = output_weight(p,t) - input_weight(p,t).
fn incidence_matrix(net: &PetriNet) -> Vec<Vec<i64>> {
    let np = net.num_places();
    let nt = net.num_transitions();
    let mut c = vec![vec![0i64; nt]; np];

    for (tidx, trans) in net.transitions.iter().enumerate() {
        for arc in &trans.inputs {
            c[arc.place.0 as usize][tidx] -= arc.weight as i64;
        }
        for arc in &trans.outputs {
            c[arc.place.0 as usize][tidx] += arc.weight as i64;
        }
    }
    c
}

/// Farkas (Fourier-Motzkin) elimination for semi-positive P-invariants.
///
/// Starts with augmented matrix [C | I_P] and eliminates each transition
/// column by combining positive/negative row pairs. After all columns
/// are processed, rows with all-zero left part yield P-invariants in the
/// right part.
fn farkas_elimination(
    c: &[Vec<i64>],
    np: usize,
    nt: usize,
    initial_marking: &[u64],
) -> Vec<PInvariant> {
    farkas_elimination_with_completeness(c, np, nt, initial_marking).0
}

/// Like [`farkas_elimination`] but also returns whether the computation
/// completed without hitting [`MAX_ROWS`]. An incomplete result is still
/// a valid subset of invariants, but callers that require ALL invariants
/// (e.g., T-semiflow non-coverage) must check the flag.
fn farkas_elimination_with_completeness(
    c: &[Vec<i64>],
    np: usize,
    nt: usize,
    initial_marking: &[u64],
) -> (Vec<PInvariant>, bool) {
    // Augmented matrix: left = C part, right = identity part.
    let mut left: Vec<Vec<i64>> = c.to_vec();
    let mut right: Vec<Vec<u64>> = (0..np)
        .map(|p| {
            let mut row = vec![0u64; np];
            row[p] = 1;
            row
        })
        .collect();

    let mut truncated = false;

    for j in 0..nt {
        let mut kept_left = Vec::new();
        let mut kept_right = Vec::new();

        let mut pos = Vec::new();
        let mut neg = Vec::new();

        for i in 0..left.len() {
            match left[i][j].cmp(&0) {
                std::cmp::Ordering::Greater => pos.push(i),
                std::cmp::Ordering::Less => neg.push(i),
                std::cmp::Ordering::Equal => {
                    kept_left.push(left[i].clone());
                    kept_right.push(right[i].clone());
                }
            }
        }

        // Combine each positive×negative pair to zero column j.
        let mut aborted = false;
        for &pi in &pos {
            for &ni in &neg {
                if kept_left.len() >= MAX_ROWS {
                    aborted = true;
                    break;
                }
                let a = left[pi][j] as u64; // positive
                let b = (-left[ni][j]) as u64; // positive (negated negative)

                // new_row = b * row[pi] + a * row[ni] → zeroes column j.
                let mut nl: Vec<i64> = left[pi]
                    .iter()
                    .zip(&left[ni])
                    .map(|(&lp, &ln)| (b as i64) * lp + (a as i64) * ln)
                    .collect();
                let mut nr: Vec<u64> = right[pi]
                    .iter()
                    .zip(&right[ni])
                    .map(|(&rp, &rn)| b * rp + a * rn)
                    .collect();

                reduce_row(&mut nl, &mut nr);

                if nr.iter().any(|&v| v > 0) {
                    kept_left.push(nl);
                    kept_right.push(nr);
                }
            }
            if aborted {
                break;
            }
        }

        left = kept_left;
        right = kept_right;

        if left.len() >= MAX_ROWS {
            truncated = true;
            break;
        }
    }

    let complete = !truncated;

    // Extract invariants: rows where the C part is fully zeroed.
    let mut invariants = Vec::new();
    for i in 0..left.len() {
        if left[i].iter().all(|&v| v == 0) && right[i].iter().any(|&v| v > 0) {
            let weights = right[i].clone();
            let token_count: u64 = weights
                .iter()
                .zip(initial_marking)
                .map(|(&w, &m)| w * m)
                .sum();
            invariants.push(PInvariant {
                weights,
                token_count,
            });
        }
    }

    deduplicate_invariants(&mut invariants);
    (invariants, complete)
}

/// GCD of two non-negative integers (Euclidean algorithm).
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Divide all row elements by their GCD to keep numbers small.
fn reduce_row(left: &mut [i64], right: &mut [u64]) {
    let mut g = 0u64;
    for &v in left.iter() {
        g = gcd(g, v.unsigned_abs());
    }
    for &v in right.iter() {
        g = gcd(g, v);
    }
    if g > 1 {
        for v in left.iter_mut() {
            *v /= g as i64;
        }
        for v in right.iter_mut() {
            *v /= g;
        }
    }
}

/// Remove duplicate invariants (identical weight vectors).
fn deduplicate_invariants(invariants: &mut Vec<PInvariant>) {
    invariants.sort_by(|a, b| a.weights.cmp(&b.weights));
    invariants.dedup_by(|a, b| a.weights == b.weights);
}

/// Structural upper bound for a single place from P-invariants.
///
/// Returns `min_{y: y_p > 0} floor(y.token_count / y_p)`.
/// Returns `None` if no invariant covers the place.
pub(crate) fn structural_place_bound(invariants: &[PInvariant], place: usize) -> Option<u64> {
    invariants
        .iter()
        .filter(|inv| inv.weights[place] > 0)
        .map(|inv| inv.token_count / inv.weights[place])
        .min()
}

/// Structural upper bound for the sum of tokens over a place set.
///
/// For a P-invariant y covering all places in S (y_p > 0 for all p ∈ S):
///   min(y_p) · Σ m(p) ≤ Σ y_p · m(p) ≤ y.token_count
///   ⟹ Σ m(p) ≤ token_count / min(y_p for p ∈ S)
///
/// Returns `None` if no invariant covers all places in `places`.
pub(crate) fn structural_set_bound(invariants: &[PInvariant], places: &[usize]) -> Option<u64> {
    if places.is_empty() {
        return Some(0);
    }

    invariants
        .iter()
        .filter(|inv| places.iter().all(|&p| inv.weights[p] > 0))
        .map(|inv| {
            let min_weight = places.iter().map(|&p| inv.weights[p]).min().unwrap();
            inv.token_count / min_weight
        })
        .min()
}

/// Compute structural upper bounds for all places in a net.
///
/// Returns a vector indexed by place, with `Some(bound)` for places covered
/// by at least one P-invariant, `None` for uncovered places.
pub(crate) fn structural_place_bounds(net: &PetriNet) -> Vec<Option<u64>> {
    let invariants = compute_p_invariants(net);
    (0..net.num_places())
        .map(|p| structural_place_bound(&invariants, p))
        .collect()
}

// ── Implied place detection ──────────────────────────────────────────

/// An implied place: its token count is fully determined by a P-invariant
/// and other non-implied (kept) places. Excluding implied places from
/// the packed hash key reduces per-state memory during BFS exploration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ImpliedPlace {
    /// Index of the implied place in the net's place vector.
    pub place: usize,
    /// How to reconstruct this place's token count from kept places.
    pub reconstruction: ImpliedPlaceReconstruction,
}

/// Reconstruction equation for an implied place.
///
/// `m(place) = (constant - sum(weight_i * m(kept_i))) / divisor`
///
/// Division is exact for all reachable markings (guaranteed by the
/// P-invariant property y^T · m = constant).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ImpliedPlaceReconstruction {
    /// Conserved quantity: y^T · m₀.
    pub constant: u64,
    /// Invariant weight of the implied place (always > 0).
    pub divisor: u64,
    /// (place_index, invariant_weight) pairs for kept places in the support.
    pub terms: Vec<(usize, u64)>,
}

/// Find implied places using a greedy selection over P-invariants.
///
/// For each invariant (processed by ascending support size), selects at most
/// one place to exclude. Guarantees no chained reconstruction: every term
/// in a reconstruction references only kept (non-excluded) places.
///
/// Prefers weight-1 places (exact division without remainder).
pub(crate) fn find_implied_places(invariants: &[PInvariant]) -> Vec<ImpliedPlace> {
    if invariants.is_empty() {
        return vec![];
    }

    let num_places = invariants[0].weights.len();

    // Sort invariants by ascending support size (tighter invariants first)
    let mut sorted_indices: Vec<usize> = (0..invariants.len()).collect();
    sorted_indices.sort_by_key(|&i| invariants[i].weights.iter().filter(|&&w| w > 0).count());

    let mut removed = vec![false; num_places];
    let mut must_keep = vec![false; num_places];
    let mut result = Vec::new();

    for &inv_idx in &sorted_indices {
        let inv = &invariants[inv_idx];
        let support: Vec<usize> = inv
            .weights
            .iter()
            .enumerate()
            .filter(|(_, &w)| w > 0)
            .map(|(p, _)| p)
            .collect();

        if support.len() < 2 {
            continue; // Need at least 2 support places for reconstruction
        }

        // Find best candidate to remove:
        // - Not already removed or marked must_keep
        // - All other support places are non-removed (independence guarantee)
        // - Prefer weight 1 (no division)
        let candidate = support
            .iter()
            .copied()
            .filter(|&p| !removed[p] && !must_keep[p])
            .filter(|&p| support.iter().all(|&q| q == p || !removed[q]))
            .min_by_key(|&p| {
                if inv.weights[p] == 1 {
                    0u64
                } else {
                    inv.weights[p]
                }
            });

        let candidate_place = match candidate {
            Some(p) => p,
            None => continue,
        };

        let terms: Vec<(usize, u64)> = support
            .iter()
            .filter(|&&p| p != candidate_place)
            .map(|&p| (p, inv.weights[p]))
            .collect();

        removed[candidate_place] = true;
        for &p in &support {
            if p != candidate_place {
                must_keep[p] = true;
            }
        }

        result.push(ImpliedPlace {
            place: candidate_place,
            reconstruction: ImpliedPlaceReconstruction {
                constant: inv.token_count,
                divisor: inv.weights[candidate_place],
                terms,
            },
        });
    }

    result.sort_by_key(|ip| ip.place);
    result
}

// ── T-semiflow (T-invariant) computation ────────────────────────────

/// A semi-positive T-semiflow: x ≥ 0 with C · x = 0.
///
/// Transitions covered by at least one T-semiflow participate in
/// repeatable firing sequences. Uncovered transitions can fire at most
/// finitely many times in a bounded net — disproving L4-liveness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TSemiflow {
    /// Weight for each transition (indexed by transition index). All ≥ 0.
    pub weights: Vec<u64>,
}

/// Result of T-semiflow computation: semiflows plus a completeness flag.
pub(crate) struct TSemiflowResult {
    /// Discovered T-semiflows (may be a subset if Farkas was truncated).
    pub semiflows: Vec<TSemiflow>,
    /// Whether the Farkas algorithm completed without hitting MAX_ROWS.
    /// If `false`, the semiflow list may be incomplete — callers must NOT
    /// conclude non-coverage from a truncated result (soundness issue).
    pub complete: bool,
}

/// Compute semi-positive T-semiflows via Farkas on C^T.
///
/// T-semiflows satisfy C · x = 0 ⟺ x^T · C^T = 0. This is structurally
/// identical to P-invariant computation on the transposed matrix. We reuse
/// `farkas_elimination` with a dummy marking (the token_count field is
/// meaningless for T-semiflows and is discarded).
///
/// Returns `TSemiflowResult` with a `complete` flag. Callers using the
/// result to prove non-coverage (e.g., structural non-liveness) MUST check
/// `complete == true` before concluding — an incomplete result may miss
/// semiflows that would cover the transition.
pub(crate) fn compute_t_semiflows(net: &PetriNet) -> TSemiflowResult {
    let np = net.num_places();
    let nt = net.num_transitions();

    if nt == 0 {
        return TSemiflowResult {
            semiflows: vec![],
            complete: true,
        };
    }

    // No places: C is empty, every transition vector is a semiflow.
    if np == 0 {
        return TSemiflowResult {
            semiflows: (0..nt)
                .map(|t| {
                    let mut w = vec![0u64; nt];
                    w[t] = 1;
                    TSemiflow { weights: w }
                })
                .collect(),
            complete: true,
        };
    }

    // Build C^T: nt rows × np columns.
    let ct = transposed_incidence_matrix(net);
    // Reuse Farkas with a dummy marking (token_count is discarded).
    let dummy_marking = vec![0u64; nt];
    let (p_invs, complete) = farkas_elimination_with_completeness(&ct, nt, np, &dummy_marking);
    TSemiflowResult {
        semiflows: p_invs
            .into_iter()
            .map(|inv| TSemiflow {
                weights: inv.weights,
            })
            .collect(),
        complete,
    }
}

/// Build the transposed incidence matrix C^T[t][p] = C[p][t].
fn transposed_incidence_matrix(net: &PetriNet) -> Vec<Vec<i64>> {
    let np = net.num_places();
    let nt = net.num_transitions();
    let mut ct = vec![vec![0i64; np]; nt];
    for (tidx, trans) in net.transitions.iter().enumerate() {
        for arc in &trans.inputs {
            ct[tidx][arc.place.0 as usize] -= arc.weight as i64;
        }
        for arc in &trans.outputs {
            ct[tidx][arc.place.0 as usize] += arc.weight as i64;
        }
    }
    ct
}

/// Check if every transition is covered by at least one T-semiflow.
pub(crate) fn all_transitions_covered(semiflows: &[TSemiflow], num_transitions: usize) -> bool {
    (0..num_transitions).all(|t| semiflows.iter().any(|sf| sf.weights[t] > 0))
}

#[cfg(test)]
#[path = "invariant_tests.rs"]
mod tests;
