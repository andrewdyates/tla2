#![allow(dead_code)]

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub(crate) fn block_on_future<F: Future>(future: F) -> F::Output {
    tokio_test::block_on(future)
}

pub(crate) struct PollN {
    polls_remaining: usize,
}

impl PollN {
    pub(crate) fn new_ok(polls: usize) -> Self {
        Self {
            polls_remaining: polls,
        }
    }
}

impl Future for PollN {
    type Output = Result<(), ()>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.polls_remaining == 0 {
            Poll::Ready(Ok(()))
        } else {
            self.polls_remaining -= 1;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}
