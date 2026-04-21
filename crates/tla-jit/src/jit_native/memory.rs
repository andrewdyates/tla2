// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Vendored from cranelift-jit 0.112.3, src/memory.rs
// Original: Copyright (c) Bytecode Alliance. Apache-2.0 WITH LLVM-exception.
// Modified: Stripped Windows/SELinux, replaced `region`/`wasmtime-jit-icache-coherence` with libc.

use std::alloc;
use std::io;
use std::mem;
use std::ptr;

use super::ModuleError;

/// Result alias using ModuleError.
type ModuleResult<T> = Result<T, ModuleError>;

/// A simple struct consisting of a pointer and length.
struct PtrLen {
    ptr: *mut u8,
    len: usize,
}

impl PtrLen {
    fn new() -> Self {
        Self {
            ptr: ptr::null_mut(),
            len: 0,
        }
    }

    fn with_size(size: usize) -> io::Result<Self> {
        assert_ne!(size, 0);
        let page_size = page_size();
        let alloc_size = page_ceil(size, page_size);
        let layout = alloc::Layout::from_size_align(alloc_size, page_size).unwrap();
        // SAFETY: We assert that the size is non-zero above.
        let ptr = unsafe { alloc::alloc(layout) };

        if !ptr.is_null() {
            Ok(Self {
                ptr,
                len: alloc_size,
            })
        } else {
            Err(io::Error::from(io::ErrorKind::OutOfMemory))
        }
    }
}

impl Drop for PtrLen {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            let page_size = page_size();
            let layout = alloc::Layout::from_size_align(self.len, page_size).unwrap();
            unsafe {
                // Restore write permissions before dealloc (may have been set R-X).
                libc::mprotect(
                    self.ptr as *mut libc::c_void,
                    self.len,
                    libc::PROT_READ | libc::PROT_WRITE,
                );
                alloc::dealloc(self.ptr, layout);
            }
        }
    }
}

/// JIT memory manager. Bump-allocates into page-aligned regions,
/// then flips permissions to executable.
///
/// When dropped, all memory regions are freed via `PtrLen::drop`. Callers
/// must ensure that no function pointers into this memory are called after
/// the owning `JITModule` is dropped. The module ownership pattern in
/// `FingerprintCompiler._modules` / `BfsStepCompiler._extra_modules` /
/// `CompiledSccHelpers._modules` ensures modules live as long as their
/// function pointers are in use (#4082).
pub(crate) struct Memory {
    allocations: Vec<PtrLen>,
    already_protected: usize,
    current: PtrLen,
    position: usize,
}

unsafe impl Send for Memory {}

impl Memory {
    pub(crate) fn new() -> Self {
        Self {
            allocations: Vec::new(),
            already_protected: 0,
            current: PtrLen::new(),
            position: 0,
        }
    }

    fn finish_current(&mut self) {
        self.allocations
            .push(mem::replace(&mut self.current, PtrLen::new()));
        self.position = 0;
    }

    pub(crate) fn allocate(&mut self, size: usize, align: u64) -> io::Result<*mut u8> {
        let align = usize::try_from(align).expect("alignment too big");
        if self.position % align != 0 {
            self.position += align - self.position % align;
            debug_assert!(self.position % align == 0);
        }

        if size <= self.current.len - self.position {
            let ptr = unsafe { self.current.ptr.add(self.position) };
            self.position += size;
            return Ok(ptr);
        }

        self.finish_current();

        self.current = PtrLen::with_size(size)?;
        self.position = size;

        Ok(self.current.ptr)
    }

    /// Flush the instruction cache for the given region.
    /// Required on aarch64; no-op on x86-64.
    #[inline]
    unsafe fn flush_icache(ptr: *const u8, len: usize) {
        #[cfg(target_arch = "aarch64")]
        {
            // On macOS aarch64, use sys_icache_invalidate.
            #[cfg(target_os = "macos")]
            {
                extern "C" {
                    fn sys_icache_invalidate(start: *const libc::c_void, size: libc::size_t);
                }
                sys_icache_invalidate(ptr as *const libc::c_void, len);
            }
            // On Linux aarch64, use __clear_cache from compiler builtins.
            #[cfg(target_os = "linux")]
            {
                extern "C" {
                    fn __clear_cache(start: *mut libc::c_void, end: *mut libc::c_void);
                }
                __clear_cache(ptr as *mut libc::c_void, ptr.add(len) as *mut libc::c_void);
            }
        }
        // x86-64 has coherent I-cache: no flush needed.
        #[cfg(target_arch = "x86_64")]
        {
            let _ = (ptr, len);
        }
    }

    /// Ensure an instruction pipeline flush across all threads.
    /// On aarch64, use an ISB barrier. On x86-64, this is a no-op.
    #[inline]
    unsafe fn pipeline_flush() {
        #[cfg(target_arch = "aarch64")]
        {
            std::arch::asm!("isb");
        }
    }

    /// Set all memory allocated up to now as readable and executable.
    pub(crate) fn set_readable_and_executable(&mut self) -> ModuleResult<()> {
        self.finish_current();

        // Flush I-cache for all new allocations BEFORE marking R-X.
        for alloc in &self.allocations[self.already_protected..] {
            if alloc.len != 0 {
                unsafe { Self::flush_icache(alloc.ptr, alloc.len) };
            }
        }

        // Flip permissions to R-X.
        for alloc in &self.allocations[self.already_protected..] {
            if alloc.len != 0 {
                let ret = unsafe {
                    libc::mprotect(
                        alloc.ptr as *mut libc::c_void,
                        alloc.len,
                        libc::PROT_READ | libc::PROT_EXEC,
                    )
                };
                if ret != 0 {
                    return Err(ModuleError::Allocation {
                        message: "unable to make memory readable+executable",
                        err: io::Error::last_os_error(),
                    });
                }
            }
        }

        // Pipeline flush to ensure all threads see the new code.
        unsafe { Self::pipeline_flush() };

        self.already_protected = self.allocations.len();
        Ok(())
    }

    /// Set all memory allocated up to now as readonly.
    pub(crate) fn set_readonly(&mut self) -> ModuleResult<()> {
        self.finish_current();

        for alloc in &self.allocations[self.already_protected..] {
            if alloc.len != 0 {
                let ret = unsafe {
                    libc::mprotect(alloc.ptr as *mut libc::c_void, alloc.len, libc::PROT_READ)
                };
                if ret != 0 {
                    return Err(ModuleError::Allocation {
                        message: "unable to make memory readonly",
                        err: io::Error::last_os_error(),
                    });
                }
            }
        }

        self.already_protected = self.allocations.len();
        Ok(())
    }

    /// Free all allocated memory regions.
    ///
    /// # Safety
    ///
    /// Invalidates any outstanding function pointers. Only call when
    /// no JIT-compiled functions are executing or will be called again.
    pub(crate) unsafe fn free_memory(&mut self) {
        self.allocations.clear();
        self.already_protected = 0;
    }
}

impl Drop for Memory {
    fn drop(&mut self) {
        // Each PtrLen in `allocations` restores mprotect(RW) and calls
        // dealloc in its own Drop impl, so simply dropping the Vec is
        // sufficient. Previously this used mem::forget to leak pages
        // (#4082); now that JITModule ownership is tracked properly,
        // leaking is no longer needed.
    }
}

/// Get the system page size.
fn page_size() -> usize {
    // SAFETY: sysconf is safe and _SC_PAGESIZE always succeeds.
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

/// Round `size` up to the nearest multiple of `page_size`.
fn page_ceil(size: usize, page_size: usize) -> usize {
    debug_assert!(page_size.is_power_of_two());
    (size + page_size - 1) & !(page_size - 1)
}
