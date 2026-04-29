// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::ops::ControlFlow;
use std::time::Instant;

use rustc_hash::FxHashMap;
use thiserror::Error;

use super::resolve::ResolvedCtl;

use crate::explorer::fingerprint::fingerprint_marking;
use crate::explorer::{ExplorationConfig, ExplorationSetup};
use crate::marking::{pack_marking_config, MarkingConfig};
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::resolved_predicate::eval_predicate;

// Keep local deadline polling aligned with the explicit-state explorer.
const LOCAL_DEADLINE_CHECK_INTERVAL: u32 = 4096;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FormulaKey(*const ResolvedCtl);

impl FormulaKey {
    fn of(formula: &ResolvedCtl) -> Self {
        Self(std::ptr::from_ref(formula))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct EvalKey {
    state_id: u32,
    formula: FormulaKey,
}

impl EvalKey {
    fn new(state_id: u32, formula: &ResolvedCtl) -> Self {
        Self {
            state_id,
            formula: FormulaKey::of(formula),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CacheEntry {
    Active { assume_on_cycle: bool },
    Ready(bool),
}

impl CacheEntry {
    fn value(self) -> bool {
        match self {
            Self::Active { assume_on_cycle } => assume_on_cycle,
            Self::Ready(value) => value,
        }
    }
}

#[derive(Debug, Error, Clone, Copy, PartialEq, Eq)]
pub(super) enum LocalCheckAbort {
    #[error("local CTL checker exceeded state budget")]
    StateLimitReached,
    #[error("local CTL checker hit the deadline")]
    DeadlineExceeded,
}

struct LocalStateSpace<'a> {
    net: &'a PetriNet,
    max_states: usize,
    pack_capacity: usize,
    marking_config: MarkingConfig,
    state_ids: FxHashMap<u128, u32>,
    markings: Vec<Box<[u64]>>,
    deadline: Option<Instant>,
    deadline_counter: u32,
}

impl<'a> LocalStateSpace<'a> {
    fn new(net: &'a PetriNet, config: &ExplorationConfig) -> Self {
        let setup = ExplorationSetup::analyze(net);
        let mut state_ids = FxHashMap::default();
        state_ids.insert(fingerprint_marking(&setup.initial_packed), 0);

        Self {
            net,
            max_states: config.max_states(),
            pack_capacity: setup.pack_capacity,
            marking_config: setup.marking_config,
            state_ids,
            markings: vec![net.initial_marking.clone().into_boxed_slice()],
            deadline: config.deadline(),
            deadline_counter: 0,
        }
    }

    fn marking(&self, state_id: u32) -> &[u64] {
        &self.markings[state_id as usize]
    }

    fn intern_marking(
        &mut self,
        marking: &[u64],
        pack_buf: &mut Vec<u8>,
    ) -> Result<u32, LocalCheckAbort> {
        self.check_deadline()?;
        pack_marking_config(marking, &self.marking_config, pack_buf);
        let fingerprint = fingerprint_marking(pack_buf);
        if let Some(&existing) = self.state_ids.get(&fingerprint) {
            return Ok(existing);
        }
        if self.markings.len() >= self.max_states {
            return Err(LocalCheckAbort::StateLimitReached);
        }

        let state_id = self.markings.len() as u32;
        self.state_ids.insert(fingerprint, state_id);
        self.markings.push(marking.to_vec().into_boxed_slice());
        Ok(state_id)
    }

    fn check_deadline(&mut self) -> Result<(), LocalCheckAbort> {
        self.deadline_counter = self.deadline_counter.wrapping_add(1);
        if self
            .deadline_counter
            .is_multiple_of(LOCAL_DEADLINE_CHECK_INTERVAL)
            && self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(LocalCheckAbort::DeadlineExceeded);
        }
        Ok(())
    }
}

struct SuccessorVisit<B> {
    saw_any: bool,
    break_value: Option<B>,
}

pub(super) struct LocalCtlChecker<'a> {
    state_space: LocalStateSpace<'a>,
    memo: FxHashMap<EvalKey, CacheEntry>,
}

impl<'a> LocalCtlChecker<'a> {
    pub(super) fn new(net: &'a PetriNet, config: &ExplorationConfig) -> Self {
        Self {
            state_space: LocalStateSpace::new(net, config),
            memo: FxHashMap::default(),
        }
    }

    pub(super) fn eval_root(&mut self, formula: &ResolvedCtl) -> Result<bool, LocalCheckAbort> {
        self.eval(0, formula)
    }

    fn eval(&mut self, state_id: u32, formula: &ResolvedCtl) -> Result<bool, LocalCheckAbort> {
        self.state_space.check_deadline()?;

        let key = EvalKey::new(state_id, formula);
        if let Some(entry) = self.memo.get(&key).copied() {
            return Ok(entry.value());
        }

        let value = match formula {
            ResolvedCtl::Atom(predicate) => eval_predicate(
                predicate,
                self.state_space.marking(state_id),
                self.state_space.net,
            ),
            ResolvedCtl::Not(inner) => !self.eval(state_id, inner)?,
            ResolvedCtl::And(children) => {
                let mut result = true;
                for child in children {
                    if !self.eval(state_id, child)? {
                        result = false;
                        break;
                    }
                }
                result
            }
            ResolvedCtl::Or(children) => {
                let mut result = false;
                for child in children {
                    if self.eval(state_id, child)? {
                        result = true;
                        break;
                    }
                }
                result
            }
            ResolvedCtl::EX(inner) => {
                let visit = self.visit_successors(state_id, |this, successor_id| {
                    if this.eval(successor_id, inner)? {
                        Ok(ControlFlow::Break(()))
                    } else {
                        Ok(ControlFlow::Continue(()))
                    }
                })?;
                visit.break_value.is_some()
            }
            ResolvedCtl::AX(inner) => {
                let visit = self.visit_successors(state_id, |this, successor_id| {
                    if this.eval(successor_id, inner)? {
                        Ok(ControlFlow::Continue(()))
                    } else {
                        Ok(ControlFlow::Break(()))
                    }
                })?;
                !visit.saw_any || visit.break_value.is_none()
            }
            ResolvedCtl::EF(inner) => self.eval_fixpoint(state_id, formula, false, |this| {
                if this.eval(state_id, inner)? {
                    return Ok(true);
                }
                let visit = this.visit_successors(state_id, |this, successor_id| {
                    if this.eval(successor_id, formula)? {
                        Ok(ControlFlow::Break(()))
                    } else {
                        Ok(ControlFlow::Continue(()))
                    }
                })?;
                Ok(visit.break_value.is_some())
            })?,
            ResolvedCtl::AF(inner) => self.eval_fixpoint(state_id, formula, false, |this| {
                if this.eval(state_id, inner)? {
                    return Ok(true);
                }
                let visit = this.visit_successors(state_id, |this, successor_id| {
                    if this.eval(successor_id, formula)? {
                        Ok(ControlFlow::Continue(()))
                    } else {
                        Ok(ControlFlow::Break(()))
                    }
                })?;
                Ok(visit.saw_any && visit.break_value.is_none())
            })?,
            ResolvedCtl::EG(inner) => self.eval_fixpoint(state_id, formula, true, |this| {
                if !this.eval(state_id, inner)? {
                    return Ok(false);
                }
                let visit = this.visit_successors(state_id, |this, successor_id| {
                    if this.eval(successor_id, formula)? {
                        Ok(ControlFlow::Break(()))
                    } else {
                        Ok(ControlFlow::Continue(()))
                    }
                })?;
                Ok(!visit.saw_any || visit.break_value.is_some())
            })?,
            ResolvedCtl::AG(inner) => self.eval_fixpoint(state_id, formula, true, |this| {
                if !this.eval(state_id, inner)? {
                    return Ok(false);
                }
                let visit = this.visit_successors(state_id, |this, successor_id| {
                    if this.eval(successor_id, formula)? {
                        Ok(ControlFlow::Continue(()))
                    } else {
                        Ok(ControlFlow::Break(()))
                    }
                })?;
                Ok(!visit.saw_any || visit.break_value.is_none())
            })?,
            ResolvedCtl::EU(phi, psi) => self.eval_fixpoint(state_id, formula, false, |this| {
                if this.eval(state_id, psi)? {
                    return Ok(true);
                }
                if !this.eval(state_id, phi)? {
                    return Ok(false);
                }
                let visit = this.visit_successors(state_id, |this, successor_id| {
                    if this.eval(successor_id, formula)? {
                        Ok(ControlFlow::Break(()))
                    } else {
                        Ok(ControlFlow::Continue(()))
                    }
                })?;
                Ok(visit.break_value.is_some())
            })?,
            ResolvedCtl::AU(phi, psi) => self.eval_fixpoint(state_id, formula, false, |this| {
                if this.eval(state_id, psi)? {
                    return Ok(true);
                }
                if !this.eval(state_id, phi)? {
                    return Ok(false);
                }
                let visit = this.visit_successors(state_id, |this, successor_id| {
                    if this.eval(successor_id, formula)? {
                        Ok(ControlFlow::Continue(()))
                    } else {
                        Ok(ControlFlow::Break(()))
                    }
                })?;
                Ok(visit.saw_any && visit.break_value.is_none())
            })?,
        };

        self.memo.insert(key, CacheEntry::Ready(value));
        Ok(value)
    }

    fn eval_fixpoint(
        &mut self,
        state_id: u32,
        formula: &ResolvedCtl,
        assume_on_cycle: bool,
        compute: impl FnOnce(&mut Self) -> Result<bool, LocalCheckAbort>,
    ) -> Result<bool, LocalCheckAbort> {
        let key = EvalKey::new(state_id, formula);
        if let Some(entry) = self.memo.get(&key).copied() {
            return Ok(entry.value());
        }

        self.memo
            .insert(key, CacheEntry::Active { assume_on_cycle });
        let value = compute(self)?;
        self.memo.insert(key, CacheEntry::Ready(value));
        Ok(value)
    }

    fn visit_successors<B>(
        &mut self,
        state_id: u32,
        mut visitor: impl FnMut(&mut Self, u32) -> Result<ControlFlow<B>, LocalCheckAbort>,
    ) -> Result<SuccessorVisit<B>, LocalCheckAbort> {
        self.state_space.check_deadline()?;

        let mut current = self.state_space.markings[state_id as usize].to_vec();
        let mut pack_buf = Vec::with_capacity(self.state_space.pack_capacity);
        let mut saw_any = false;

        for tidx in 0..self.state_space.net.num_transitions() {
            let transition = TransitionIdx(tidx as u32);
            if !self.state_space.net.is_enabled(&current, transition) {
                continue;
            }

            saw_any = true;
            self.state_space.net.apply_delta(&mut current, transition);
            let successor_id = self.state_space.intern_marking(&current, &mut pack_buf)?;
            self.state_space.net.undo_delta(&mut current, transition);

            match visitor(self, successor_id)? {
                ControlFlow::Break(value) => {
                    return Ok(SuccessorVisit {
                        saw_any,
                        break_value: Some(value),
                    });
                }
                ControlFlow::Continue(()) => {}
            }
        }

        Ok(SuccessorVisit {
            saw_any,
            break_value: None,
        })
    }
}
