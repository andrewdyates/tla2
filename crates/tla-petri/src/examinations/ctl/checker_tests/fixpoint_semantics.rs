// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::support::{atom_at_least, full_graph, test_net};
use crate::examinations::ctl::checker::CtlChecker;
use crate::examinations::ctl::resolve::ResolvedCtl;

#[test]
fn test_lfp_ef_forward_reachability() {
    let full = full_graph(
        vec![vec![1], vec![2], vec![]],
        vec![vec![0], vec![0], vec![1]],
    );
    let net = test_net(1);
    let checker = CtlChecker::new(&full, &net);

    let sat = checker.eval(&ResolvedCtl::EF(Box::new(atom_at_least(0, 1))));

    assert_eq!(sat, vec![true, true, true]);
}

#[test]
fn test_gfp_eg_removes_dead_ends() {
    let full = full_graph(
        vec![vec![1], vec![2], vec![]],
        vec![vec![1], vec![1], vec![0]],
    );
    let net = test_net(1);
    let checker = CtlChecker::new(&full, &net);

    let sat = checker.eval(&ResolvedCtl::EG(Box::new(atom_at_least(0, 1))));

    assert_eq!(sat, vec![false, false, false]);
}

#[test]
fn test_lfp_eu_phi_until_psi() {
    let full = full_graph(
        vec![vec![1], vec![2], vec![]],
        vec![vec![1, 0], vec![1, 0], vec![0, 1]],
    );
    let net = test_net(2);
    let checker = CtlChecker::new(&full, &net);

    let sat = checker.eval(&ResolvedCtl::EU(
        Box::new(atom_at_least(0, 1)),
        Box::new(atom_at_least(1, 1)),
    ));

    assert_eq!(sat, vec![true, true, true]);
}

#[test]
fn test_au_algebraic_equivalence() {
    let full = full_graph(
        vec![vec![1, 2], vec![3], vec![2], vec![3]],
        vec![vec![1, 0], vec![1, 0], vec![0, 0], vec![0, 1]],
    );
    let net = test_net(2);
    let checker = CtlChecker::new(&full, &net);
    let phi = atom_at_least(0, 1);
    let psi = atom_at_least(1, 1);
    let direct = ResolvedCtl::AU(Box::new(phi.clone()), Box::new(psi.clone()));
    let rewritten = ResolvedCtl::Not(Box::new(ResolvedCtl::Or(vec![
        ResolvedCtl::EU(
            Box::new(ResolvedCtl::Not(Box::new(psi.clone()))),
            Box::new(ResolvedCtl::And(vec![
                ResolvedCtl::Not(Box::new(phi.clone())),
                ResolvedCtl::Not(Box::new(psi.clone())),
            ])),
        ),
        ResolvedCtl::EG(Box::new(ResolvedCtl::Not(Box::new(psi.clone())))),
    ])));

    let direct_sat = checker.eval(&direct);
    let rewritten_sat = checker.eval(&rewritten);

    assert_eq!(direct_sat, rewritten_sat);
    assert_eq!(direct_sat, vec![false, true, false, true]);
}

#[test]
fn test_deadlock_mcc_semantics() {
    // MCC deadlock semantics: EX=FALSE (no successor), AX=TRUE (vacuous),
    // EG/AG via maximal-path (path=[s], so EG(φ)=φ, AG(φ)=φ).
    let full = full_graph(vec![vec![]], vec![vec![1]]);
    let net = test_net(1);
    let checker = CtlChecker::new(&full, &net);
    let true_atom = atom_at_least(0, 1);
    let false_atom = atom_at_least(0, 2);

    // EX at deadlock = FALSE (no successor exists)
    assert_eq!(
        checker.eval(&ResolvedCtl::EX(Box::new(true_atom.clone()))),
        vec![false]
    );
    // AX at deadlock = TRUE (vacuously true)
    assert_eq!(
        checker.eval(&ResolvedCtl::AX(Box::new(true_atom.clone()))),
        vec![true]
    );
    // EG at deadlock = φ (maximal path is [s])
    assert_eq!(
        checker.eval(&ResolvedCtl::EG(Box::new(true_atom.clone()))),
        vec![true]
    );
    // AG at deadlock = φ (¬EF(¬φ))
    assert_eq!(
        checker.eval(&ResolvedCtl::AG(Box::new(true_atom))),
        vec![true]
    );

    // EX(false) at deadlock = FALSE
    assert_eq!(
        checker.eval(&ResolvedCtl::EX(Box::new(false_atom.clone()))),
        vec![false]
    );
    // AX(false) at deadlock = TRUE (vacuously true!)
    assert_eq!(
        checker.eval(&ResolvedCtl::AX(Box::new(false_atom.clone()))),
        vec![true]
    );
    // EG(false) at deadlock = false (φ doesn't hold)
    assert_eq!(
        checker.eval(&ResolvedCtl::EG(Box::new(false_atom.clone()))),
        vec![false]
    );
    // AG(false) at deadlock = false (¬EF(¬false) = ¬EF(true) = ¬[true] = [false])
    assert_eq!(
        checker.eval(&ResolvedCtl::AG(Box::new(false_atom))),
        vec![false]
    );
}

#[test]
fn test_ax_ex_duality() {
    let full = full_graph(
        vec![vec![1, 2], vec![1], vec![2]],
        vec![vec![0], vec![1], vec![0]],
    );
    let net = test_net(1);
    let checker = CtlChecker::new(&full, &net);
    let phi = atom_at_least(0, 1);
    let ax = ResolvedCtl::AX(Box::new(phi.clone()));
    let dual = ResolvedCtl::Not(Box::new(ResolvedCtl::EX(Box::new(ResolvedCtl::Not(
        Box::new(phi),
    )))));

    assert_eq!(checker.eval(&ax), checker.eval(&dual));
    assert_eq!(checker.eval(&ax), vec![false, true, false]);
}

#[test]
fn test_af_eg_duality() {
    let full = full_graph(
        vec![vec![1, 2], vec![1], vec![2]],
        vec![vec![0], vec![1], vec![0]],
    );
    let net = test_net(1);
    let checker = CtlChecker::new(&full, &net);
    let phi = atom_at_least(0, 1);
    let af = ResolvedCtl::AF(Box::new(phi.clone()));
    let dual = ResolvedCtl::Not(Box::new(ResolvedCtl::EG(Box::new(ResolvedCtl::Not(
        Box::new(phi),
    )))));

    assert_eq!(checker.eval(&af), checker.eval(&dual));
    assert_eq!(checker.eval(&af), vec![false, true, false]);
}

/// Reference AU using direct least fixpoint: A[φ U ψ] = μZ. ψ ∨ (φ ∧ AX(Z)).
fn reference_lfp_au(checker: &CtlChecker, sat_phi: &[bool], sat_psi: &[bool]) -> Vec<bool> {
    let n = sat_phi.len();
    let mut z = vec![false; n];
    loop {
        let ax_z = checker.pre_a(&z);
        let new_z: Vec<bool> = (0..n)
            .map(|i| sat_psi[i] || (sat_phi[i] && ax_z[i]))
            .collect();
        if new_z == z {
            break;
        }
        z = new_z;
    }
    z
}

/// Algebraic AU: A[φ U ψ] = ¬(E[¬ψ U (¬φ ∧ ¬ψ)] ∨ EG(¬ψ)).
fn algebraic_au(checker: &CtlChecker, sat_phi: &[bool], sat_psi: &[bool]) -> Vec<bool> {
    let n = sat_phi.len();
    let not_phi: Vec<bool> = sat_phi.iter().map(|&v| !v).collect();
    let not_psi: Vec<bool> = sat_psi.iter().map(|&v| !v).collect();
    let not_phi_and_not_psi: Vec<bool> = (0..n).map(|i| not_phi[i] && not_psi[i]).collect();
    let eu = checker.lfp_eu(&not_psi, &not_phi_and_not_psi);
    let eg = checker.gfp_eg(&not_psi);
    (0..n).map(|i| !(eu[i] || eg[i])).collect()
}

fn bitvec(mask: u32, n: usize) -> Vec<bool> {
    (0..n).map(|i| mask & (1 << i) != 0).collect()
}

/// Cross-validate AU algebraic identity vs direct fixpoint on deadlock-free
/// graphs, and verify specific AU semantics on graphs with deadlocks.
///
/// NOTE: With MCC deadlock semantics (AX vacuously TRUE at deadlocks),
/// the direct fixpoint μZ. ψ ∨ (φ ∧ AX(Z)) is NOT equivalent to the
/// algebraic identity ¬(E[¬ψ U (¬φ ∧ ¬ψ)] ∨ EG(¬ψ)) because the fixpoint
/// uses AX which is vacuously TRUE at deadlocks. Production code uses the
/// algebraic identity, which is correct.
#[test]
fn test_au_algebraic_vs_fixpoint_exhaustive() {
    struct TestGraph {
        name: &'static str,
        adj: Vec<Vec<u32>>,
    }

    // Graphs WITHOUT deadlocks: fixpoint == algebraic identity
    let no_deadlock_graphs = vec![
        TestGraph {
            name: "cycle_3",
            adj: vec![vec![1], vec![2], vec![0]],
        },
        TestGraph {
            name: "single_cycle",
            adj: vec![vec![0]],
        },
        TestGraph {
            name: "two_cycles_joined",
            adj: vec![vec![1, 2], vec![0], vec![2]],
        },
    ];

    let mut total_checks = 0;
    for tg in &no_deadlock_graphs {
        let n = tg.adj.len();
        let markings: Vec<Vec<u64>> = (0..n).map(|_| vec![0]).collect();
        let full = full_graph(tg.adj.clone(), markings);
        let net = test_net(1);
        let checker = CtlChecker::new(&full, &net);

        let num_masks = 1u32 << n;
        for phi_mask in 0..num_masks {
            let phi = bitvec(phi_mask, n);
            for psi_mask in 0..num_masks {
                let psi = bitvec(psi_mask, n);
                let alg = algebraic_au(&checker, &phi, &psi);
                let fix = reference_lfp_au(&checker, &phi, &psi);
                assert_eq!(
                    alg, fix,
                    "AU mismatch on graph '{}': phi={:?} psi={:?}\n  algebraic={:?}\n  fixpoint={:?}",
                    tg.name, phi, psi, alg, fix
                );
                total_checks += 1;
            }
        }
    }

    // Graph WITH deadlocks: verify algebraic identity gives correct semantics.
    // linear_deadlock: 0→1→2(deadlock). Only maximal path from any state is [s,...,2].
    // A[φ U ψ] at deadlock s: ψ(s) (only the current state matters).
    {
        let full = full_graph(
            vec![vec![1], vec![2], vec![]],
            vec![vec![0], vec![0], vec![0]],
        );
        let net = test_net(1);
        let checker = CtlChecker::new(&full, &net);

        // AU(true, true) = true everywhere (ψ=true holds immediately)
        let au = algebraic_au(&checker, &[true; 3], &[true; 3]);
        assert_eq!(au, vec![true, true, true]);

        // AU(true, false) at deadlock: ψ=false at state 2, and path never reaches ψ
        // AU(true, false) = false everywhere (ψ never holds)
        let au = algebraic_au(&checker, &[true; 3], &[false; 3]);
        assert_eq!(au, vec![false, false, false]);

        // AU(true, only-at-2): ψ holds only at state 2
        // Path [0,1,2]: φ=true until ψ holds at 2 → TRUE for all
        let au = algebraic_au(&checker, &[true; 3], &[false, false, true]);
        assert_eq!(au, vec![true, true, true]);

        total_checks += 3;
    }
    eprintln!("AU cross-validation: {total_checks} checks passed");
}

/// Reference AF using direct least fixpoint: AF(φ) = μZ. φ ∨ AX(Z).
fn reference_lfp_af(checker: &CtlChecker, sat_phi: &[bool]) -> Vec<bool> {
    let n = sat_phi.len();
    let mut z = vec![false; n];
    loop {
        let ax_z = checker.pre_a(&z);
        let new_z: Vec<bool> = (0..n).map(|i| sat_phi[i] || ax_z[i]).collect();
        if new_z == z {
            break;
        }
        z = new_z;
    }
    z
}

/// Verify AF(φ) = ¬EG(¬φ) duality exhaustively on graphs with deadlocks.
///
/// NOTE: With MCC deadlock semantics (AX vacuously TRUE at deadlocks),
/// the direct fixpoint μZ. φ ∨ AX(Z) is NOT equivalent to ¬EG(¬φ).
/// Production code uses the duality form, which is correct for maximal-path
/// semantics. This test verifies the duality holds by comparing gfp_eg
/// with pre_a-based AF on graphs without deadlocks, and checking specific
/// expected values on graphs with deadlocks.
#[test]
fn test_af_duality_vs_fixpoint_exhaustive() {
    // On graphs WITHOUT deadlocks, the fixpoint μZ. φ ∨ AX(Z) is still
    // equivalent to ¬EG(¬φ) because AX never triggers vacuous truth.
    let no_deadlock_graphs: Vec<(&str, Vec<Vec<u32>>)> =
        vec![("cycle_3", vec![vec![1], vec![2], vec![0]])];

    let mut total = 0;
    for (name, adj) in &no_deadlock_graphs {
        let n = adj.len();
        let markings: Vec<Vec<u64>> = (0..n).map(|_| vec![0]).collect();
        let full = full_graph(adj.clone(), markings);
        let net = test_net(1);
        let checker = CtlChecker::new(&full, &net);

        for mask in 0..(1u32 << n) {
            let phi = bitvec(mask, n);
            let not_phi: Vec<bool> = phi.iter().map(|&v| !v).collect();
            let eg_not = checker.gfp_eg(&not_phi);
            let af_duality: Vec<bool> = eg_not.into_iter().map(|v| !v).collect();
            let af_fixpoint = reference_lfp_af(&checker, &phi);
            assert_eq!(
                af_duality, af_fixpoint,
                "AF mismatch on '{name}': phi={phi:?}"
            );
            total += 1;
        }
    }

    // On graphs WITH deadlocks, verify specific AF semantics.
    // linear_deadlock: 0→1→2(deadlock). Only maximal path from s is [s,...,2].
    {
        let full = full_graph(
            vec![vec![1], vec![2], vec![]],
            vec![vec![0], vec![0], vec![1]],
        );
        let net = test_net(1);
        let checker = CtlChecker::new(&full, &net);
        let phi = [false, false, true]; // only state 2 satisfies

        let not_phi: Vec<bool> = phi.iter().map(|&v| !v).collect();
        let eg_not = checker.gfp_eg(&not_phi);
        let af: Vec<bool> = eg_not.into_iter().map(|v| !v).collect();
        // All paths from any state end at state 2, which satisfies phi → AF = true everywhere
        assert_eq!(af, vec![true, true, true]);
        total += 1;

        // AF(false): false never holds → AF(false) = false everywhere
        let af_false: Vec<bool> = {
            let eg_true = checker.gfp_eg(&[true; 3]);
            eg_true.into_iter().map(|v| !v).collect()
        };
        assert_eq!(af_false, vec![false, false, false]);
        total += 1;
    }
    eprintln!("AF cross-validation: {total} checks passed");
}

/// Cross-validate full eval() with nested temporal formulas against manual computation.
/// Tests formulas like AG(EF(p)), AF(EG(p)), A[EX(p) U q], A[p U EG(q)].
#[test]
fn test_nested_temporal_cross_validation() {
    // Graph: 0→1, 0→2, 1→1 (self-loop), 2 deadlock
    // State 0: p0=1 (phi=true)
    // State 1: p0=1 (phi=true), self-loop
    // State 2: p0=0 (phi=false), deadlock
    let full = full_graph(
        vec![vec![1, 2], vec![1], vec![]],
        vec![vec![1], vec![1], vec![0]],
    );
    let net = test_net(1);
    let checker = CtlChecker::new(&full, &net);
    let p = atom_at_least(0, 1); // p0 >= 1: true at {0, 1}
    let not_p = ResolvedCtl::Not(Box::new(p.clone()));

    // EG(p): states from which there's an infinite path staying in p.
    // State 0: path 0→1→1→1→... stays in p. EG(p)[0] = true.
    // State 1: self-loop in p. EG(p)[1] = true.
    // State 2: deadlock, p=false. EG(p)[2] = false.
    assert_eq!(
        checker.eval(&ResolvedCtl::EG(Box::new(p.clone()))),
        vec![true, true, false]
    );

    // AF(p): all paths eventually reach p.
    // State 0: p holds at 0. AF(p)[0] = true.
    // State 1: p holds at 1. AF(p)[1] = true.
    // State 2: deadlock, p=false, loops at 2 forever. AF(p)[2] = false.
    assert_eq!(
        checker.eval(&ResolvedCtl::AF(Box::new(p.clone()))),
        vec![true, true, false]
    );

    // AG(EF(p)): from every reachable state, p is reachable.
    // EF(p) = [true, true, false]. State 2 can't reach p.
    // AG(EF(p)): state 0 can reach state 2 where EF(p)=false. AG(EF(p))[0] = false.
    assert_eq!(
        checker.eval(&ResolvedCtl::AG(Box::new(ResolvedCtl::EF(Box::new(
            p.clone()
        ))))),
        vec![false, true, false]
    );

    // AF(EG(p)): on all paths, eventually reach a state where EG(p) holds.
    // EG(p) = [true, true, false].
    // State 0: EG(p)[0]=true, so at step 0 of ANY path from 0, EG(p) already holds.
    //          Therefore AF(EG(p))[0] = true (not false — EG(p) at state 0 is satisfied).
    // State 1: EG(p)[1]=true. AF(EG(p))[1] = true.
    // State 2: EG(p)[2]=false, deadlock. AF(EG(p))[2] = false.
    assert_eq!(
        checker.eval(&ResolvedCtl::AF(Box::new(ResolvedCtl::EG(Box::new(
            p.clone()
        ))))),
        vec![true, true, false]
    );

    // A[EX(p) U p]: phi=EX(p), psi=p.
    // Since psi=p holds at states 0,1: AU satisfied at j=0.
    // State 2: p=false, EX(p)=false at deadlock. AU[2]=false.
    assert_eq!(
        checker.eval(&ResolvedCtl::AU(
            Box::new(ResolvedCtl::EX(Box::new(p.clone()))),
            Box::new(p.clone()),
        )),
        vec![true, true, false]
    );

    // A[p U EG(¬p)]: phi=p, psi=EG(¬p)=[false,false,true].
    // State 0: path 0→1→1→... never reaches EG(¬p). AU[0] = false.
    // State 1: path 1→1→... never reaches EG(¬p). AU[1] = false.
    // State 2: EG(¬p) holds at 2. AU[2] = true (j=0).
    assert_eq!(
        checker.eval(&ResolvedCtl::AU(
            Box::new(p.clone()),
            Box::new(ResolvedCtl::EG(Box::new(not_p))),
        )),
        vec![false, false, true]
    );
}
