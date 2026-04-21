// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;
use crate::explorer::{
    CheckpointableObserver, ExplorationObserver, ParallelExplorationObserver,
    ParallelExplorationSummary,
};

use super::ReducedNet;

/// Observer wrapper that expands reduced markings to original-index space.
///
/// Wraps any [`ExplorationObserver`] to transparently translate markings from
/// the reduced net's index space back to the original net's index space.
/// This enables property evaluation using original-net indices while exploring
/// a structurally reduced (smaller) state space.
#[allow(dead_code)]
pub(crate) struct ExpandingObserver<'a> {
    reduced: &'a ReducedNet,
    inner: &'a mut dyn ExplorationObserver,
    buf: Vec<u64>,
    error: Option<PnmlError>,
}

#[allow(dead_code)]
impl<'a> ExpandingObserver<'a> {
    pub fn new(reduced: &'a ReducedNet, inner: &'a mut dyn ExplorationObserver) -> Self {
        let buf = vec![0u64; reduced.place_map.len()];
        Self {
            reduced,
            inner,
            buf,
            error: None,
        }
    }

    pub(crate) fn take_error(&mut self) -> Option<PnmlError> {
        self.error.take()
    }
}

impl ExplorationObserver for ExpandingObserver<'_> {
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        match self.reduced.expand_marking_into(marking, &mut self.buf) {
            Ok(()) => self.inner.on_new_state(&self.buf),
            Err(error) => {
                self.error = Some(error);
                false
            }
        }
    }

    fn on_transition_fire(&mut self, trans: crate::petri_net::TransitionIdx) -> bool {
        let orig = self.reduced.transition_unmap[trans.0 as usize];
        self.inner.on_transition_fire(orig)
    }

    fn on_deadlock(&mut self, marking: &[u64]) {
        if self.error.is_some() {
            return;
        }
        match self.reduced.expand_marking_into(marking, &mut self.buf) {
            Ok(()) => self.inner.on_deadlock(&self.buf),
            Err(error) => self.error = Some(error),
        }
    }

    fn is_done(&self) -> bool {
        self.error.is_some() || self.inner.is_done()
    }
}

/// Observer wrapper for the parallel frontier engine.
///
/// Like [`ExpandingObserver`], but its batch summaries own their own expansion
/// buffers so reduced-net markings never share mutable scratch across workers.
pub(crate) struct ParallelExpandingObserver<'a, O> {
    reduced: &'a ReducedNet,
    inner: &'a mut O,
    buf: Vec<u64>,
    error: Option<PnmlError>,
}

impl<'a, O> ParallelExpandingObserver<'a, O> {
    pub fn new(reduced: &'a ReducedNet, inner: &'a mut O) -> Self {
        let buf = vec![0u64; reduced.place_map.len()];
        Self {
            reduced,
            inner,
            buf,
            error: None,
        }
    }

    pub(crate) fn take_error(&mut self) -> Option<PnmlError> {
        self.error.take()
    }
}

impl<O> ExplorationObserver for ParallelExpandingObserver<'_, O>
where
    O: ParallelExplorationObserver,
{
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        match self.reduced.expand_marking_into(marking, &mut self.buf) {
            Ok(()) => self.inner.on_new_state(&self.buf),
            Err(error) => {
                self.error = Some(error);
                false
            }
        }
    }

    fn on_transition_fire(&mut self, trans: crate::petri_net::TransitionIdx) -> bool {
        let orig = self.reduced.transition_unmap[trans.0 as usize];
        self.inner.on_transition_fire(orig)
    }

    fn on_deadlock(&mut self, marking: &[u64]) {
        if self.error.is_some() {
            return;
        }
        match self.reduced.expand_marking_into(marking, &mut self.buf) {
            Ok(()) => self.inner.on_deadlock(&self.buf),
            Err(error) => self.error = Some(error),
        }
    }

    fn is_done(&self) -> bool {
        self.error.is_some() || self.inner.is_done()
    }
}

impl<'a, O> ParallelExplorationObserver for ParallelExpandingObserver<'a, O>
where
    O: ParallelExplorationObserver,
{
    type Summary = ParallelExpandingSummary<'a, O::Summary>;

    fn new_summary(&self) -> Self::Summary {
        ParallelExpandingSummary {
            reduced: self.reduced,
            inner: self.inner.new_summary(),
            buf: vec![0u64; self.reduced.place_map.len()],
            error: None,
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        if self.error.is_none() {
            self.error = summary.error;
        }
        self.inner.merge_summary(summary.inner);
    }
}

impl<O> CheckpointableObserver for ParallelExpandingObserver<'_, O>
where
    O: ParallelExplorationObserver + CheckpointableObserver,
{
    type Snapshot = O::Snapshot;

    const CHECKPOINT_KIND: &'static str = O::CHECKPOINT_KIND;

    fn snapshot(&self) -> Self::Snapshot {
        self.inner.snapshot()
    }

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot) {
        self.error = None;
        self.inner.restore_from_snapshot(snapshot);
    }
}

pub(crate) struct ParallelExpandingSummary<'a, S> {
    reduced: &'a ReducedNet,
    inner: S,
    buf: Vec<u64>,
    error: Option<PnmlError>,
}

impl<S> ParallelExplorationSummary for ParallelExpandingSummary<'_, S>
where
    S: ParallelExplorationSummary,
{
    fn on_new_state(&mut self, marking: &[u64]) {
        if self.error.is_some() {
            return;
        }
        match self.reduced.expand_marking_into(marking, &mut self.buf) {
            Ok(()) => self.inner.on_new_state(&self.buf),
            Err(error) => self.error = Some(error),
        }
    }

    fn on_transition_fire(&mut self, trans: crate::petri_net::TransitionIdx) {
        let orig = self.reduced.transition_unmap[trans.0 as usize];
        self.inner.on_transition_fire(orig);
    }

    fn on_deadlock(&mut self, marking: &[u64]) {
        if self.error.is_some() {
            return;
        }
        match self.reduced.expand_marking_into(marking, &mut self.buf) {
            Ok(()) => self.inner.on_deadlock(&self.buf),
            Err(error) => self.error = Some(error),
        }
    }

    fn stop_requested(&self) -> bool {
        self.error.is_some() || self.inner.stop_requested()
    }
}
