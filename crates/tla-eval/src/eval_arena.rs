// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-BFS-step bump arena for eval temporaries.
//!
//! Replaces per-object `Arc` allocation + atomic refcounting with O(1) bump
//! allocation and O(chunks) bulk reset. Matches the JVM TLAB model that gives
//! TLC its allocation advantage.
//!
//! # Lifecycle
//!
//! 1. `begin_state()` — reset cursor (no per-object dealloc)
//! 2. Successor generation — all arena allocations via `alloc()`
//! 3. `end_state()` — arena ready for reuse
//!
//! # Thread Safety
//!
//! Each worker thread owns its own `EvalArena`. No cross-thread sharing.
//! Access is through `with_eval_arena()` which uses a thread-local RefCell.
//!
//! # Part of #3580

use std::alloc::Layout;
use std::cell::RefCell;
use std::ptr::NonNull;

use tla_core::name_intern::NameId;
use tla_value::CompactValue;

/// Chunk size for arena allocation. 64KB matches typical TLAB size.
const CHUNK_SIZE: usize = 64 * 1024;

/// Maximum alignment supported by the arena (8 bytes, sufficient for all
/// BindingNode fields and pointer-sized values).
const MAX_ALIGN: usize = 8;

/// Drop callback registered against arena-resident data that still needs a
/// destructor run before the arena chunk is reused.
struct DeferredDrop {
    ptr: *mut u8,
    drop_fn: unsafe fn(*mut u8),
}

/// Per-BFS-step bump arena.
///
/// Allocates objects by bumping a cursor forward within fixed-size chunks.
/// Reset moves the cursor back to the start of the first chunk without
/// deallocating individual objects. Chunks are retained for reuse across
/// BFS steps to amortize mmap/brk cost.
pub struct EvalArena {
    /// Backing storage chunks. Retained across resets for reuse.
    chunks: Vec<NonNull<u8>>,
    /// Byte offset within the current chunk.
    cursor: usize,
    /// Index of the current chunk in `chunks`.
    current_chunk: usize,
    /// Destructors to run before the arena chunk is reused.
    ///
    /// Arena allocations do not get per-object `Drop`, so any arena-resident
    /// field with owned heap state must register an explicit destructor here.
    /// Cleared on `end_state()` before the chunks are poisoned for the next step.
    deferred_drops: Vec<DeferredDrop>,
    /// Total bytes allocated in this arena lifetime (diagnostic).
    total_allocated: usize,
    /// Number of individual allocations (diagnostic).
    alloc_count: usize,
    /// Number of reset calls (diagnostic).
    reset_count: usize,
    /// Whether the arena is active (between begin_state/end_state).
    active: bool,
}

// SAFETY: EvalArena is owned by a single thread (thread-local via RefCell).
// The raw pointers in `chunks` point to memory exclusively owned by this arena.
unsafe impl Send for EvalArena {}

impl EvalArena {
    /// Create a new arena with one pre-allocated chunk.
    pub fn new() -> Self {
        let mut arena = EvalArena {
            chunks: Vec::with_capacity(4),
            cursor: 0,
            current_chunk: 0,
            deferred_drops: Vec::new(),
            total_allocated: 0,
            alloc_count: 0,
            reset_count: 0,
            active: false,
        };
        arena.alloc_chunk();
        arena
    }

    /// Mark the beginning of a new BFS state's processing.
    ///
    /// Resets the arena cursor without deallocating chunks. All prior
    /// allocations become invalid — callers must not hold references
    /// across this boundary.
    pub fn begin_state(&mut self) {
        debug_assert!(
            !self.active,
            "begin_state called while arena is already active"
        );
        self.cursor = 0;
        self.current_chunk = 0;
        self.active = true;
    }

    /// Mark the end of a BFS state's processing.
    ///
    /// After this call, no arena-allocated references should be live.
    pub fn end_state(&mut self) {
        debug_assert!(self.active, "end_state called while arena is not active");
        self.active = false;
        self.clear_deferred_drops();

        // Debug mode: poison freed memory to catch use-after-free after the
        // BFS step boundary.
        #[cfg(debug_assertions)]
        {
            for chunk_ptr in &self.chunks {
                // SAFETY: We own these chunks exclusively and they are CHUNK_SIZE bytes.
                unsafe {
                    std::ptr::write_bytes(chunk_ptr.as_ptr(), 0xDE, CHUNK_SIZE);
                }
            }
        }

        self.reset_count += 1;
    }

    /// Schedule a destructor for arena-resident data at `end_state()`.
    ///
    /// Used when an arena-allocated object contains fields with non-trivial
    /// drop semantics (for example `CompactValue` holding a boxed compound
    /// `Value`). Arena chunks themselves are reused wholesale, so these
    /// destructors must be driven explicitly before reset.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a live `T` stored inside this arena.
    /// - The pointee must remain valid until `end_state()` for the current step.
    /// - The pointee must not be dropped through any other path.
    pub unsafe fn defer_drop_in_place<T>(&mut self, ptr: *mut T) {
        unsafe fn drop_in_place_ptr<T>(ptr: *mut u8) {
            // SAFETY: caller registered a live `T` pointer with matching type.
            unsafe {
                std::ptr::drop_in_place(ptr.cast::<T>());
            }
        }

        self.deferred_drops.push(DeferredDrop {
            ptr: ptr.cast::<u8>(),
            drop_fn: drop_in_place_ptr::<T>,
        });
    }

    /// Allocate `size` bytes with alignment `align` from the arena.
    ///
    /// Returns a pointer to uninitialized memory. The caller must initialize
    /// the memory before reading.
    ///
    /// # Safety
    ///
    /// - The returned pointer is valid only until `end_state()` for this BFS step.
    /// - `align` must be a power of 2 and <= MAX_ALIGN.
    /// - `size` must be > 0 and <= CHUNK_SIZE.
    pub unsafe fn alloc_raw(&mut self, layout: Layout) -> NonNull<u8> {
        debug_assert!(self.active, "alloc_raw called while arena is not active");
        debug_assert!(layout.align() <= MAX_ALIGN);
        debug_assert!(layout.size() <= CHUNK_SIZE);

        let align = layout.align();
        let size = layout.size();

        // Align cursor up
        let aligned_cursor = (self.cursor + align - 1) & !(align - 1);

        if aligned_cursor + size <= CHUNK_SIZE {
            // Fast path: fits in current chunk
            let chunk_ptr = self.chunks[self.current_chunk];
            // SAFETY: aligned_cursor + size <= CHUNK_SIZE, and chunk_ptr points
            // to CHUNK_SIZE bytes of allocated memory.
            let ptr = unsafe { chunk_ptr.as_ptr().add(aligned_cursor) };
            self.cursor = aligned_cursor + size;
            self.total_allocated += size;
            self.alloc_count += 1;
            // SAFETY: ptr is within a valid allocation and non-null
            // (derived from NonNull + offset within bounds).
            unsafe { NonNull::new_unchecked(ptr) }
        } else {
            // Slow path: move to next chunk
            self.current_chunk += 1;
            if self.current_chunk >= self.chunks.len() {
                self.alloc_chunk();
            }
            self.cursor = size;
            self.total_allocated += size;
            self.alloc_count += 1;
            let chunk_ptr = self.chunks[self.current_chunk];
            // SAFETY: size <= CHUNK_SIZE, so ptr is within bounds.
            // chunk_ptr is NonNull, so the result is non-null.
            unsafe { NonNull::new_unchecked(chunk_ptr.as_ptr()) }
        }
    }

    /// Allocate and initialize a value of type T in the arena, returning a raw pointer.
    ///
    /// This is the primitive used by arena callsites that need to perform
    /// follow-up arena mutations (for example registering a deferred drop for
    /// a field inside the allocated object) without holding a Rust borrow on
    /// `self` through the returned value reference.
    ///
    /// # Safety
    ///
    /// The returned pointer is valid only until `end_state()` for this BFS step.
    /// The caller must ensure no dereferences outlive the current BFS state.
    pub unsafe fn alloc_ptr<T>(&mut self, value: T) -> *mut T {
        let layout = Layout::new::<T>();
        // SAFETY: Layout::new::<T>() produces valid alignment and size.
        let ptr = unsafe { self.alloc_raw(layout) };
        let typed_ptr = ptr.as_ptr() as *mut T;
        // SAFETY: ptr is aligned and points to enough memory for T.
        unsafe {
            typed_ptr.write(value);
            typed_ptr
        }
    }

    /// Allocate and initialize a value of type T in the arena.
    ///
    /// # Safety
    ///
    /// The returned reference is valid only until `end_state()` for this BFS step.
    /// The caller must ensure no references outlive the current BFS state.
    pub unsafe fn alloc<T>(&mut self, value: T) -> &mut T {
        // SAFETY: alloc_ptr returns a valid pointer for the current arena epoch.
        unsafe { &mut *self.alloc_ptr(value) }
    }

    /// Number of chunks currently allocated.
    pub fn chunk_count(&self) -> usize {
        self.chunks.len()
    }

    /// Total bytes allocated across all states (cumulative).
    pub fn total_allocated(&self) -> usize {
        self.total_allocated
    }

    /// Total individual allocations across all states (cumulative).
    pub fn alloc_count(&self) -> usize {
        self.alloc_count
    }

    /// Number of state resets performed.
    pub fn reset_count(&self) -> usize {
        self.reset_count
    }

    /// Whether the arena is currently active (between begin/end_state).
    pub fn is_active(&self) -> bool {
        self.active
    }

    /// Allocate a new chunk from the global allocator.
    fn alloc_chunk(&mut self) {
        let layout = Layout::from_size_align(CHUNK_SIZE, MAX_ALIGN)
            .expect("EvalArena chunk layout is valid");
        // SAFETY: layout has non-zero size and valid alignment.
        let ptr = unsafe { std::alloc::alloc(layout) };
        let ptr = NonNull::new(ptr).expect("EvalArena: allocation failed (OOM)");
        self.chunks.push(ptr);
    }

    fn clear_deferred_drops(&mut self) {
        while let Some(deferred) = self.deferred_drops.pop() {
            // SAFETY: `deferred` was registered from a live arena allocation and
            // is executed before the arena chunk is reused or deallocated.
            unsafe {
                (deferred.drop_fn)(deferred.ptr);
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn deferred_drop_count(&self) -> usize {
        self.deferred_drops.len()
    }
}

impl Drop for EvalArena {
    fn drop(&mut self) {
        self.clear_deferred_drops();
        let layout = Layout::from_size_align(CHUNK_SIZE, MAX_ALIGN)
            .expect("EvalArena chunk layout is valid");
        for chunk_ptr in &self.chunks {
            // SAFETY: Each chunk was allocated with the same layout via alloc_chunk().
            unsafe {
                std::alloc::dealloc(chunk_ptr.as_ptr(), layout);
            }
        }
    }
}

impl Default for EvalArena {
    fn default() -> Self {
        Self::new()
    }
}

// --- Arena-allocated binding node ---

/// Compact binding source tag for arena nodes.
///
/// Mirrors `BindingSource` but as a 1-byte discriminant. The `Instance` variant's
/// `Box<OpEvalDeps>` is stored separately (INSTANCE is the cold path — arena nodes
/// are only used for Eager values with None/Local/Liveness sources).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ArenaSourceTag {
    /// No dependency info (simple cons, operator parameters).
    None = 0,
    /// Local binding (LET/quantifier) — carries binding depth.
    Local = 1,
    /// Liveness replay binding — carries binding depth.
    Liveness = 2,
}

/// Arena-allocated binding node. No refcount overhead.
///
/// Size: 32B (vs ~64B for Arc<BindingNode> with 16B Arc header + 48B node).
/// Only used for Eager values with non-Instance sources (the hot path).
/// Instance bindings and Lazy values fall through to the heap path.
///
/// # Safety
///
/// The pointer in `next` is valid only until `end_state()` for the current step.
/// Callers must not hold references across BFS state boundaries.
#[repr(C)]
pub struct ArenaBindingNode {
    /// Interned name identifier for this binding.
    pub name: NameId,
    /// Source tag discriminant (1B).
    pub source_tag: ArenaSourceTag,
    /// Padding for alignment.
    _pad: [u8; 3],
    /// Compact eager value (8B). Only Eager values are arena-allocated.
    pub value: CompactValue,
    /// Binding depth for Local/Liveness sources. Unused (0) for None.
    pub binding_depth: u32,
    /// Padding to align `next` to 8B boundary.
    _pad2: [u8; 4],
    /// Next node in the arena chain (null = end of arena segment).
    /// When null, lookup continues to the heap chain base.
    pub next: *const ArenaBindingNode,
}

// Compile-time size assertion: ArenaBindingNode must be exactly 32 bytes.
const _: () = assert!(std::mem::size_of::<ArenaBindingNode>() == 32);
const _: () = assert!(std::mem::align_of::<ArenaBindingNode>() <= MAX_ALIGN);

// SAFETY: ArenaBindingNode contains no interior mutability or non-Send fields.
// The raw pointer `next` points to arena memory owned by the thread-local
// EvalArena (single-threaded access guaranteed by RefCell).
unsafe impl Send for ArenaBindingNode {}
unsafe impl Sync for ArenaBindingNode {}

impl EvalArena {
    /// Allocate a binding node in the arena.
    ///
    /// Returns a raw pointer valid until `end_state()` for this BFS step.
    /// Only Eager values with non-Instance sources should use this path.
    ///
    /// # Safety
    ///
    /// The returned pointer must not be dereferenced after `end_state()`.
    pub unsafe fn alloc_binding_node(
        &mut self,
        name: NameId,
        value: CompactValue,
        source_tag: ArenaSourceTag,
        binding_depth: u32,
        next: *const ArenaBindingNode,
    ) -> *const ArenaBindingNode {
        // SAFETY: ArenaBindingNode is 32B with 8B alignment, fits in arena.
        let node_ptr = unsafe {
            self.alloc_ptr(ArenaBindingNode {
                name,
                source_tag,
                _pad: [0; 3],
                value,
                binding_depth,
                _pad2: [0; 4],
                next,
            })
        };
        if unsafe { (*node_ptr).value.is_heap() } {
            // SAFETY: `node.value` lives in arena memory until `end_state()`,
            // and no other path will run its destructor.
            unsafe {
                self.defer_drop_in_place(std::ptr::addr_of_mut!((*node_ptr).value));
            }
        }
        node_ptr as *const ArenaBindingNode
    }
}

// --- Thread-local arena access ---

thread_local! {
    static EVAL_ARENA: RefCell<Option<EvalArena>> = const { RefCell::new(None) };
}

/// Initialize the thread-local eval arena for this worker thread.
///
/// Called once per worker thread at startup. The arena persists for the
/// lifetime of the thread, reusing chunks across BFS states.
pub fn init_thread_arena() {
    EVAL_ARENA.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if borrow.is_none() {
            *borrow = Some(EvalArena::new());
        }
    });
}

/// Access the thread-local eval arena.
///
/// Returns None if the arena has not been initialized (e.g., in test contexts
/// or non-worker threads).
pub fn with_eval_arena<R>(f: impl FnOnce(&mut EvalArena) -> R) -> Option<R> {
    EVAL_ARENA.with(|cell| {
        let mut borrow = cell.borrow_mut();
        borrow.as_mut().map(f)
    })
}

/// Signal the start of a new BFS state's processing to the thread-local arena.
pub fn arena_begin_state() {
    with_eval_arena(|arena| arena.begin_state());
}

/// Signal the end of a BFS state's processing to the thread-local arena.
pub fn arena_end_state() {
    with_eval_arena(|arena| arena.end_state());
}

/// Panic-safe guard for a single BFS state's arena lifetime.
///
/// Begins the thread-local arena state on creation and ends it on drop. This
/// mirrors the repo's other panic-safe cleanup guards: if successor evaluation
/// unwinds and the panic is caught, the arena is returned to an inactive state
/// so the next BFS state on that thread can begin normally.
#[must_use = "bind the arena state guard for the duration of one BFS state"]
pub struct ArenaStateGuard {
    active: bool,
}

impl ArenaStateGuard {
    /// Enter the current BFS state's arena scope.
    pub fn new() -> Self {
        let active = with_eval_arena(|arena| arena.begin_state()).is_some();
        Self { active }
    }
}

impl Drop for ArenaStateGuard {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        with_eval_arena(|arena| {
            if arena.is_active() {
                arena.end_state();
            }
        });
    }
}

/// Report arena stats to stderr if `TLA2_ARENA_STATS=1`.
///
/// Called at the end of BFS exploration. Reports total allocations,
/// bytes allocated, chunks used, and states processed (reset count).
pub fn report_arena_stats() {
    if !{
        static ARENA_STATS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ARENA_STATS.get_or_init(|| std::env::var("TLA2_ARENA_STATS").as_deref() == Ok("1"))
    } {
        return;
    }
    with_eval_arena(|arena| {
        eprintln!("=== Eval Arena Stats ===");
        eprintln!("  Allocations:  {}", arena.alloc_count());
        eprintln!(
            "  Bytes total:  {} ({:.1} MB)",
            arena.total_allocated(),
            arena.total_allocated() as f64 / (1024.0 * 1024.0)
        );
        eprintln!("  Chunks used:  {}", arena.chunk_count());
        eprintln!("  States reset: {}", arena.reset_count());
        if arena.reset_count() > 0 {
            eprintln!(
                "  Avg allocs/state: {:.1}",
                arena.alloc_count() as f64 / arena.reset_count() as f64
            );
            eprintln!(
                "  Avg bytes/state:  {:.0}",
                arena.total_allocated() as f64 / arena.reset_count() as f64
            );
        }
    });
}

#[cfg(test)]
#[path = "eval_arena_tests.rs"]
mod tests;
