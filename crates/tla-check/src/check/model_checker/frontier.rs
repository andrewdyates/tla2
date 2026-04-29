// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BFS frontier queue abstraction.
//!
//! Part of #2335: Extracts the BFS frontier queue behind a trait so the BFS loop
//! is not hardcoded to `VecDeque`. Phase 1 provides the trait + VecDeque impl only.
//! Future phases add checkpoint persistence (Phase 2) and disk-backed spillover (Phase 3).

use std::collections::VecDeque;

/// Abstraction over the BFS frontier queue.
///
/// The BFS loop pushes successor states and pops the next state to explore.
/// This trait decouples the loop from a specific queue implementation, enabling
/// future disk-backed or checkpoint-aware frontiers without changing loop logic.
///
/// Phase 1: Only `VecDeque` impl. Monomorphized — zero vtable overhead.
pub(super) trait BfsFrontier {
    type Entry;

    fn push(&mut self, entry: Self::Entry);
    fn pop(&mut self) -> Option<Self::Entry>;
    fn len(&self) -> usize;

    /// Iterate over all entries without consuming them.
    fn iter(&self) -> impl Iterator<Item = &Self::Entry>;

    /// Snapshot the current queue contents in dequeue order.
    ///
    /// Checkpointing uses this rather than `iter()` because some frontier
    /// implementations store entries in compressed/arena form and must
    /// materialize them on demand.
    fn checkpoint_entries(&self) -> Vec<Self::Entry>
    where
        Self::Entry: Clone;
}

impl<T> BfsFrontier for VecDeque<T> {
    type Entry = T;

    fn push(&mut self, entry: T) {
        self.push_back(entry);
    }

    fn pop(&mut self) -> Option<T> {
        self.pop_front()
    }

    fn len(&self) -> usize {
        VecDeque::len(self)
    }

    fn iter(&self) -> impl Iterator<Item = &T> {
        <VecDeque<T>>::iter(self)
    }

    fn checkpoint_entries(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.iter().cloned().collect()
    }
}
