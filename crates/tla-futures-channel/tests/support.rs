#![allow(dead_code)]

use std::fmt;
use std::ptr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use std::task::{Context, RawWaker, RawWakerVTable, Waker};

pub(crate) struct WakeCounter(Arc<AtomicUsize>);

impl PartialEq<usize> for WakeCounter {
    fn eq(&self, other: &usize) -> bool {
        self.0.load(Ordering::SeqCst) == *other
    }
}

impl fmt::Debug for WakeCounter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.load(Ordering::SeqCst).fmt(f)
    }
}

pub(crate) fn new_count_waker() -> (Waker, WakeCounter) {
    let counter = Arc::new(AtomicUsize::new(0));
    let data = Arc::into_raw(counter.clone()) as *const ();
    let waker = unsafe { Waker::from_raw(RawWaker::new(data, &COUNT_VTABLE)) };
    (waker, WakeCounter(counter))
}

pub(crate) fn noop_context() -> Context<'static> {
    Context::from_waker(static_waker(&NOOP_WAKER, &NOOP_VTABLE))
}

pub(crate) fn panic_waker_ref() -> &'static Waker {
    static_waker(&PANIC_WAKER, &PANIC_VTABLE)
}

fn static_waker(
    storage: &'static OnceLock<Waker>,
    vtable: &'static RawWakerVTable,
) -> &'static Waker {
    storage.get_or_init(|| unsafe {
        Waker::from_raw(RawWaker::new(ptr::null(), vtable))
    })
}

static NOOP_WAKER: OnceLock<Waker> = OnceLock::new();
static PANIC_WAKER: OnceLock<Waker> = OnceLock::new();

static COUNT_VTABLE: RawWakerVTable =
    RawWakerVTable::new(count_clone, count_wake, count_wake_by_ref, count_drop);
static NOOP_VTABLE: RawWakerVTable =
    RawWakerVTable::new(noop_clone, noop_wake, noop_wake, noop_wake);
static PANIC_VTABLE: RawWakerVTable =
    RawWakerVTable::new(panic_clone, panic_wake, panic_wake, noop_wake);

unsafe fn count_clone(data: *const ()) -> RawWaker {
    Arc::increment_strong_count(data as *const AtomicUsize);
    RawWaker::new(data, &COUNT_VTABLE)
}

unsafe fn count_wake(data: *const ()) {
    let counter = Arc::from_raw(data as *const AtomicUsize);
    counter.fetch_add(1, Ordering::SeqCst);
}

unsafe fn count_wake_by_ref(data: *const ()) {
    (*(data as *const AtomicUsize)).fetch_add(1, Ordering::SeqCst);
}

unsafe fn count_drop(data: *const ()) {
    drop(Arc::from_raw(data as *const AtomicUsize));
}

unsafe fn noop_clone(_: *const ()) -> RawWaker {
    RawWaker::new(ptr::null(), &NOOP_VTABLE)
}

unsafe fn panic_clone(_: *const ()) -> RawWaker {
    RawWaker::new(ptr::null(), &PANIC_VTABLE)
}

unsafe fn noop_wake(_: *const ()) {}

unsafe fn panic_wake(_: *const ()) {
    panic!("test waker must not be woken");
}
