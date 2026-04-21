// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Synchronization primitives

mod cancellation_token;
pub use cancellation_token::{
    guard::DropGuard, guard_ref::DropGuardRef, CancellationToken, WaitForCancellationFuture,
    WaitForCancellationFutureOwned,
};
pub(crate) use cancellation_token::{RunUntilCancelledFuture, RunUntilCancelledFutureOwned};

mod mpsc;
pub use mpsc::{PollSendError, PollSender};

mod poll_semaphore;
pub use poll_semaphore::PollSemaphore;

mod reusable_box;
pub use reusable_box::ReusableBoxFuture;

#[cfg(test)]
mod tests;
