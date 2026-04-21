// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Successor batch routing for parallel BFS transport.
//!
//! Contains [`SuccessorBatchRoute`] and the `successor_batch_route` constructor
//! method on [`ParallelTransport`].
//!
//! Extracted from `transport/mod.rs` for file-size compliance. Part of #3389.

use super::super::work_item::BfsWorkItem;
use super::enqueue::enqueue_successor_item;
use super::shared_queue::{SharedFrontier, SHARED_QUEUE_BATCH_SIZE};
use super::ParallelTransport;
use crossbeam_deque::{Injector, Worker};
use smallvec::SmallVec;
use std::cell::{Cell, RefCell};

pub(super) enum SuccessorBatchRoute<'a, T: BfsWorkItem> {
    WorkStealing {
        local_queue: &'a Worker<(T, usize)>,
        injector: &'a Injector<(T, usize)>,
        route_to_injector: bool,
        injector_pushes: &'a Cell<usize>,
    },
    SharedFrontier {
        frontier: &'a SharedFrontier<T>,
        frontier_batch: &'a RefCell<SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]>>,
    },
}

impl<T: BfsWorkItem> SuccessorBatchRoute<'_, T> {
    pub(super) fn enqueue(&self, item: T, enq_depth: usize) {
        match self {
            Self::WorkStealing {
                local_queue,
                injector,
                route_to_injector,
                injector_pushes,
            } => enqueue_successor_item(
                *route_to_injector,
                item,
                enq_depth,
                local_queue,
                injector,
                injector_pushes,
            ),
            Self::SharedFrontier {
                frontier,
                frontier_batch,
            } => {
                let mut batch = frontier_batch.borrow_mut();
                batch.push((item, enq_depth));
                if batch.len() >= SHARED_QUEUE_BATCH_SIZE {
                    frontier.push_batch(&mut batch);
                }
            }
        }
    }

    pub(super) fn finish(&self) {
        if let Self::SharedFrontier {
            frontier,
            frontier_batch,
        } = self
        {
            frontier.push_batch(&mut frontier_batch.borrow_mut());
        }
    }

    pub(super) fn injector_pushes(&self) -> usize {
        match self {
            Self::WorkStealing {
                injector_pushes, ..
            } => injector_pushes.get(),
            Self::SharedFrontier { .. } => 0,
        }
    }
}

impl<T: BfsWorkItem> ParallelTransport<T> {
    pub(super) fn successor_batch_route<'a>(
        shared_frontier_tail_mode_active: bool,
        shared_frontier: &'a SharedFrontier<T>,
        local_queue: &'a Worker<(T, usize)>,
        injector: &'a Injector<(T, usize)>,
        route_to_injector: bool,
        frontier_batch: &'a RefCell<SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]>>,
        injector_pushes: &'a Cell<usize>,
    ) -> SuccessorBatchRoute<'a, T> {
        if shared_frontier_tail_mode_active {
            SuccessorBatchRoute::SharedFrontier {
                frontier: shared_frontier,
                frontier_batch,
            }
        } else {
            SuccessorBatchRoute::WorkStealing {
                local_queue,
                injector,
                route_to_injector,
                injector_pushes,
            }
        }
    }
}
