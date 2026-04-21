// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::resolve::ResolvedCtl;

use crate::explorer::FullReachabilityGraph;
use crate::petri_net::PetriNet;
use crate::resolved_predicate::{eval_predicate, ResolvedPredicate};
use tla_mc_core::{build_predecessor_adjacency, CtlAtomEvaluator, CtlEngine, IndexedCtlGraph};

struct PetriAtomEvaluator<'a> {
    net: &'a PetriNet,
}

impl CtlAtomEvaluator<Vec<u64>, ResolvedPredicate> for PetriAtomEvaluator<'_> {
    fn evaluate(&self, state: &Vec<u64>, atom: &ResolvedPredicate) -> bool {
        eval_predicate(atom, state, self.net)
    }
}

pub(super) struct CtlChecker<'a> {
    full: &'a FullReachabilityGraph,
    net: &'a PetriNet,
    rev_adj: Vec<Vec<u32>>,
}

impl<'a> CtlChecker<'a> {
    pub(super) fn new(full: &'a FullReachabilityGraph, net: &'a PetriNet) -> Self {
        let rev_adj = build_predecessor_adjacency(&full.graph.adj);
        Self { full, net, rev_adj }
    }

    pub(super) fn eval(&self, formula: &ResolvedCtl) -> Vec<bool> {
        self.engine().eval(formula)
    }

    fn engine(
        &self,
    ) -> CtlEngine<'_, Vec<u64>, (u32, u32), ResolvedPredicate, PetriAtomEvaluator<'_>> {
        let graph = IndexedCtlGraph::new(&self.full.markings, &self.full.graph.adj, &self.rev_adj);
        CtlEngine::new(graph, PetriAtomEvaluator { net: self.net })
    }

    #[cfg(test)]
    fn pre_a(&self, sat: &[bool]) -> Vec<bool> {
        self.engine().pre_a(sat)
    }

    #[cfg(test)]
    fn lfp_ef(&self, sat: &[bool]) -> Vec<bool> {
        self.engine().lfp_ef(sat)
    }

    #[cfg(test)]
    fn gfp_eg(&self, sat: &[bool]) -> Vec<bool> {
        self.engine().gfp_eg(sat)
    }

    #[cfg(test)]
    fn lfp_eu(&self, sat_phi: &[bool], sat_psi: &[bool]) -> Vec<bool> {
        self.engine().lfp_eu(sat_phi, sat_psi)
    }
}

#[cfg(test)]
#[path = "checker_tests.rs"]
mod checker_tests;
