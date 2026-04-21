// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooperative cancellation for CHC solvers
//!
//! This module provides a cancellation token that allows portfolio solving to
//! stop losing engines early when a winner is found. The token is thread-safe
//! and can be shared across multiple engine threads.
//!
//! # Usage
//!
//! ```rust,no_run
//! use z4_chc::CancellationToken;
//!
//! // Create a token (portfolio solver)
//! let token = CancellationToken::new();
//!
//! // Share with engines
//! let engine_token = token.clone();
//!
//! // In engine main loop
//! if engine_token.is_cancelled() {
//!     // Return early from solver
//! }
//!
//! // When winner found (portfolio)
//! token.cancel();
//! ```

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// A thread-safe cancellation token for cooperative engine cancellation.
///
/// Engines check this token periodically in their main loops and return early
/// if cancellation is requested. This allows portfolio solving to stop losing
/// engines promptly when a winner is found.
#[derive(Debug, Clone)]
pub struct CancellationToken {
    cancelled: Arc<AtomicBool>,
}

impl Default for CancellationToken {
    fn default() -> Self {
        Self::new()
    }
}

impl CancellationToken {
    /// Create a new cancellation token in the non-cancelled state.
    pub fn new() -> Self {
        Self {
            cancelled: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Check if cancellation has been requested.
    ///
    /// This is a cheap atomic load operation and can be called frequently
    /// in main loops without significant overhead.
    #[inline]
    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Relaxed)
    }

    /// Request cancellation. All clones of this token will see the request.
    ///
    /// This operation is idempotent - calling it multiple times has no
    /// additional effect.
    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Relaxed);
    }

    /// Reset the token to non-cancelled state.
    ///
    /// This is useful for reusing tokens across multiple solving attempts.
    pub fn reset(&self) {
        self.cancelled.store(false, Ordering::Relaxed);
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
