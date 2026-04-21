// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for tableau graph construction.

use super::*;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

fn state_pred(tag: u32) -> LiveExpr {
    LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag,
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_particle_basic() {
    let p = state_pred(1);
    let particle = Particle::new(p);
    assert_eq!(particle.formulas().len(), 1);
    assert!(!particle.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_particle_closure_atom() {
    // Closure of a single atom is just that atom
    let p = state_pred(1);
    let particles = particle_closure(Particle::new(p));
    assert_eq!(particles.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_particle_closure_conjunction() {
    // P /\ Q expands to single particle with P, Q, and (P /\ Q)
    // The original And is kept for membership checks during <>P expansion
    let p = state_pred(1);
    let q = state_pred(2);
    let conj = LiveExpr::and(vec![p, q]);
    let particles = particle_closure(Particle::new(conj));
    assert_eq!(particles.len(), 1);
    // Particle has: the original (P /\ Q), plus the expanded P and Q
    assert_eq!(particles[0].formulas().len(), 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_particle_closure_disjunction() {
    // P \/ Q expands to two particles
    let p = state_pred(1);
    let q = state_pred(2);
    let disj = LiveExpr::or(vec![p, q]);
    let particles = particle_closure(Particle::new(disj));
    assert_eq!(particles.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_particle_closure_always() {
    // []P expands to P /\ ()[]P
    let p = state_pred(1);
    let always_p = LiveExpr::always(p);
    let particles = particle_closure(Particle::new(always_p));
    assert_eq!(particles.len(), 1);
    // Should contain P and ()[]P
    let particle = &particles[0];
    assert!(particle.formulas().len() >= 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_particle_closure_eventually() {
    // <>P expands to P \/ ()<>P (branching)
    let p = state_pred(1);
    let eventually_p = LiveExpr::eventually(p);
    let particles = particle_closure(Particle::new(eventually_p));
    // Two branches: one with P now, one with ()<>P
    assert_eq!(particles.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_local_consistency() {
    let p = state_pred(1);

    // Consistent: just P
    let particle1 = Particle::new(p.clone());
    assert!(is_locally_consistent(&particle1));

    // Inconsistent: P and ~P
    let particle2 = Particle::from_vec(vec![p.clone(), LiveExpr::not(p.clone())]);
    assert!(!is_locally_consistent(&particle2));

    // Inconsistent: FALSE
    let particle3 = Particle::new(LiveExpr::Bool(false));
    assert!(!is_locally_consistent(&particle3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tableau_construction() {
    // Simple: []P
    let p = state_pred(1);
    let always_p = LiveExpr::always(p);
    let tableau = Tableau::new(always_p);

    assert!(!tableau.is_empty());
    assert!(tableau.init_count() > 0);

    // All initial nodes should have successors
    for i in 0..tableau.init_count() {
        assert!(!tableau.nodes()[i].successors().is_empty());
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tableau_eventually_always() {
    // <>[]P (eventually always)
    let p = state_pred(1);
    let ea_p = LiveExpr::eventually(LiveExpr::always(p));
    let tableau = Tableau::new(ea_p);

    // Should have nodes for both branches
    assert!(tableau.len() >= 2);
}
