// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! StateArena and ThreadLocalArena - bump-pointer allocator for Value slices.
//!
//! # Benefits (with bumpalo feature)
//! - O(1) allocation (bump pointer increment)
//! - No per-object malloc overhead
//! - Better cache locality (contiguous memory)
//! - Bulk deallocation (drop entire arena)
//!
//! When the `bumpalo` feature is disabled (e.g., for Kani verification),
//! a simple Vec-based fallback is used that provides the same API.
//!
//! # Usage
//! ```rust,no_run
//! use tla_check::arena::StateArena; // crate-internal path
//! use tla_check::Value;
//!
//! let arena = StateArena::with_capacity(1_000_000); // estimate for 1M states
//! let values = [Value::int(1), Value::int(2)];
//! let slice = arena.alloc_slice(&values);
//! // slice is valid for arena's lifetime
//! # let _ = slice;
//! ```

#[cfg(feature = "bumpalo")]
use bumpalo::Bump;
use std::cell::RefCell;

use crate::Value;

// ============================================================================
// StateArena - bumpalo-based implementation
// ============================================================================

#[cfg(feature = "bumpalo")]
/// Pre-allocated memory arena for state storage.
///
/// The arena is optimized for the model checking use case:
/// - States are allocated during BFS exploration
/// - All states are dropped together at the end
/// - No individual deallocation needed
pub(crate) struct StateArena {
    /// The underlying bump allocator
    bump: Bump,
    /// Statistics: total bytes allocated
    allocated_bytes: RefCell<usize>,
    /// Statistics: number of allocations
    allocation_count: RefCell<usize>,
}

#[cfg(feature = "bumpalo")]
impl StateArena {
    /// Create an arena pre-sized for the expected number of states.
    ///
    /// Default estimate: 500 bytes per state. For MCBakery with 655K states,
    /// this would pre-allocate ~328 MB.
    ///
    /// # Arguments
    /// * `estimated_states` - Expected number of states to explore
    pub(crate) fn with_capacity(estimated_states: usize) -> Self {
        // Estimate 500 bytes per state (target from roadmap)
        let bytes = estimated_states.saturating_mul(500);
        StateArena {
            bump: Bump::with_capacity(bytes),
            allocated_bytes: RefCell::new(0),
            allocation_count: RefCell::new(0),
        }
    }

    /// Create a default arena (1M state capacity).
    pub(crate) fn new() -> Self {
        Self::with_capacity(1_000_000)
    }

    /// Allocate a slice of Values by cloning from a source slice.
    ///
    /// The returned slice is valid for the lifetime of the arena.
    pub(crate) fn alloc_slice(&self, values: &[Value]) -> &[Value] {
        if values.is_empty() {
            return &[];
        }

        // Track statistics
        let size = std::mem::size_of_val(values);
        *self.allocated_bytes.borrow_mut() += size;
        *self.allocation_count.borrow_mut() += 1;

        // Allocate and initialize with clones
        self.bump.alloc_slice_fill_iter(values.iter().cloned())
    }

    /// Allocate a Vec's contents into the arena, returning a slice.
    ///
    /// This is useful when you've built a Vec and want to store it
    /// in arena memory.
    pub(crate) fn alloc_vec(&self, vec: Vec<Value>) -> &[Value] {
        if vec.is_empty() {
            return &[];
        }

        let size = std::mem::size_of::<Value>() * vec.len();
        *self.allocated_bytes.borrow_mut() += size;
        *self.allocation_count.borrow_mut() += 1;

        self.bump.alloc_slice_fill_iter(vec)
    }

    /// Get the total bytes allocated from this arena.
    pub(crate) fn allocated_bytes(&self) -> usize {
        *self.allocated_bytes.borrow()
    }

    /// Get the number of allocations made from this arena.
    pub(crate) fn allocation_count(&self) -> usize {
        *self.allocation_count.borrow()
    }

    /// Get the underlying bump allocator's current chunk capacity.
    pub(crate) fn chunk_capacity(&self) -> usize {
        self.bump.chunk_capacity()
    }

    /// Reset the arena, deallocating all memory and starting fresh.
    ///
    /// This is useful for reusing an arena across multiple model checking runs.
    pub(crate) fn reset(&mut self) {
        self.bump.reset();
        *self.allocated_bytes.borrow_mut() = 0;
        *self.allocation_count.borrow_mut() = 0;
    }
}

#[cfg(feature = "bumpalo")]
impl Default for StateArena {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "bumpalo")]
impl std::fmt::Debug for StateArena {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StateArena")
            .field("allocated_bytes", &self.allocated_bytes())
            .field("allocation_count", &self.allocation_count())
            .field("chunk_capacity", &self.chunk_capacity())
            .finish()
    }
}

// ============================================================================
// StateArena - Vec-based fallback (no bumpalo)
// ============================================================================

#[cfg(not(feature = "bumpalo"))]
/// Simple Vec-based arena fallback for when bumpalo is disabled.
///
/// This provides the same API but uses standard Vec allocations.
/// Used for Kani verification where bumpalo's ptr_mask intrinsic is unsupported.
pub(crate) struct StateArena {
    allocated_bytes: RefCell<usize>,
    allocation_count: RefCell<usize>,
}

#[cfg(not(feature = "bumpalo"))]
impl StateArena {
    pub(crate) fn with_capacity(_estimated_states: usize) -> Self {
        StateArena {
            allocated_bytes: RefCell::new(0),
            allocation_count: RefCell::new(0),
        }
    }

    pub(crate) fn new() -> Self {
        Self::with_capacity(1_000_000)
    }

    /// Allocate a slice by leaking a Box (provides same lifetime semantics)
    pub(crate) fn alloc_slice(&self, values: &[Value]) -> &[Value] {
        if values.is_empty() {
            return &[];
        }
        let size = std::mem::size_of_val(values);
        *self.allocated_bytes.borrow_mut() += size;
        *self.allocation_count.borrow_mut() += 1;
        // Leak the allocation to get a 'static reference
        Box::leak(values.to_vec().into_boxed_slice())
    }

    pub(crate) fn alloc_vec(&self, vec: Vec<Value>) -> &[Value] {
        if vec.is_empty() {
            return &[];
        }
        let size = std::mem::size_of::<Value>() * vec.len();
        *self.allocated_bytes.borrow_mut() += size;
        *self.allocation_count.borrow_mut() += 1;
        Box::leak(vec.into_boxed_slice())
    }

    pub(crate) fn allocated_bytes(&self) -> usize {
        *self.allocated_bytes.borrow()
    }

    pub(crate) fn allocation_count(&self) -> usize {
        *self.allocation_count.borrow()
    }

    pub(crate) fn chunk_capacity(&self) -> usize {
        0 // No pre-allocation in fallback
    }

    pub(crate) fn reset(&mut self) {
        // Leaked memory cannot be reclaimed in fallback mode
        *self.allocated_bytes.borrow_mut() = 0;
        *self.allocation_count.borrow_mut() = 0;
    }
}

#[cfg(not(feature = "bumpalo"))]
impl Default for StateArena {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(not(feature = "bumpalo"))]
impl std::fmt::Debug for StateArena {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StateArena (fallback)")
            .field("allocated_bytes", &self.allocated_bytes())
            .field("allocation_count", &self.allocation_count())
            .finish()
    }
}

/// Thread-local arena for parallel model checking.
///
/// Each worker thread gets its own arena to avoid contention.
/// This is used when the ModelChecker is run in parallel mode.
#[derive(Default)]
pub(crate) struct ThreadLocalArena {
    arena: StateArena,
}

impl ThreadLocalArena {
    /// Create a new thread-local arena with default capacity.
    pub(crate) fn new() -> Self {
        ThreadLocalArena {
            arena: StateArena::new(),
        }
    }

    /// Get a reference to the arena.
    pub(crate) fn get(&self) -> &StateArena {
        &self.arena
    }
}
