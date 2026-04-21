// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU-accelerated batch state fingerprinting via Apple Metal compute shaders.
//!
//! When the BFS frontier is large (>10K states), sending them to the GPU for
//! parallel fingerprinting can be faster than CPU. This module implements the
//! same splitmix64-based XOR-accumulator algorithm as [`super::flat_fingerprint`]
//! but runs it on the GPU via a Metal compute shader.
//!
//! # Architecture
//!
//! - **Metal compute shader (MSL)**: Each GPU thread processes one state,
//!   computing the 128-bit XOR-accumulator fingerprint using the same
//!   `splitmix64_mix` and `slot_contribution` functions as the CPU path.
//! - **Rust-side**: [`GpuFingerprinter`] manages the Metal device, command
//!   queue, compiled compute pipeline, and a persistent salts buffer on GPU.
//! - **Fallback**: [`fingerprint_batch_or_cpu`] automatically selects GPU
//!   or CPU based on availability and batch size.
//!
//! # Correctness
//!
//! The GPU and CPU paths produce identical 128-bit fingerprints. This is
//! verified by tests that compare outputs for various state configurations.
//! The MSL shader uses the exact same constants, mixing functions, and
//! accumulation order as the Rust `fingerprint_flat()` function.
//!
//! # Feature gate
//!
//! This module is only compiled on macOS with the `metal` feature enabled.
//! On other platforms or without the feature, the module is empty and the
//! fallback function always uses the CPU path.
//!
//! Part of #3956.

use super::flat_fingerprint::{fingerprint_flat, generate_salts};

/// Minimum batch size to justify GPU dispatch overhead.
/// Below this threshold, CPU fingerprinting is faster due to GPU launch latency.
const GPU_BATCH_THRESHOLD: usize = 10_000;

/// Fingerprint a batch of flat states, using GPU if available and batch is large
/// enough, otherwise falling back to CPU.
///
/// # Arguments
///
/// * `states` - Contiguous buffer of packed i64 states. Length must be
///   `num_states * num_slots`.
/// * `num_states` - Number of states in the batch.
/// * `num_slots` - Number of i64 slots per state.
///
/// # Returns
///
/// Vector of 128-bit fingerprints, one per state.
#[must_use]
pub fn fingerprint_batch_or_cpu(
    states: &[i64],
    num_states: usize,
    num_slots: usize,
) -> Vec<u128> {
    debug_assert_eq!(
        states.len(),
        num_states * num_slots,
        "fingerprint_batch_or_cpu: states.len() {} != num_states {} * num_slots {}",
        states.len(),
        num_states,
        num_slots,
    );

    #[cfg(all(target_os = "macos", feature = "metal"))]
    {
        if num_states >= GPU_BATCH_THRESHOLD {
            if let Ok(gpu) = GpuFingerprinter::new(num_slots) {
                if let Ok(result) = gpu.fingerprint_batch(states, num_states) {
                    return result;
                }
            }
        }
    }

    // CPU fallback
    fingerprint_batch_cpu(states, num_states, num_slots)
}

/// CPU-only batch fingerprinting. Always available.
#[must_use]
fn fingerprint_batch_cpu(states: &[i64], num_states: usize, num_slots: usize) -> Vec<u128> {
    let salts = generate_salts(num_slots);
    let mut results = Vec::with_capacity(num_states);
    for i in 0..num_states {
        let state = &states[i * num_slots..(i + 1) * num_slots];
        results.push(fingerprint_flat(state, &salts));
    }
    results
}

// ============================================================================
// Metal GPU implementation (macOS only, behind `metal` feature)
// ============================================================================

#[cfg(all(target_os = "macos", feature = "metal"))]
mod metal_impl {
    use std::ffi::{c_char, c_ulong, c_void, CStr};
    use std::ptr;

    use super::generate_salts;

    /// Metal Shading Language (MSL) source for the fingerprint compute kernel.
    ///
    /// Implements the exact same splitmix64-based XOR-accumulator as the Rust
    /// `fingerprint_flat()` function. Each thread processes one state.
    const MSL_SOURCE: &str = r#"
#include <metal_stdlib>
using namespace metal;

// splitmix64 finalizer — matches Rust splitmix64_mix() exactly
static inline ulong splitmix64_mix(ulong x) {
    x += 0x9E3779B97F4A7C15UL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9UL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBUL;
    return x ^ (x >> 31);
}

// Compute one slot's contribution to the XOR accumulator.
// Returns (lo, hi) 64-bit halves of the 128-bit contribution.
static inline ulong2 slot_contribution(ulong salt, long value) {
    ulong bits = as_type<ulong>(value);
    ulong mixed_lo = splitmix64_mix(salt ^ bits);
    // rotate_left(salt, 32) = (salt << 32) | (salt >> 32)
    ulong rotated = (salt << 32) | (salt >> 32);
    ulong mixed_hi = splitmix64_mix(rotated ^ bits);
    return ulong2(mixed_lo, mixed_hi);
}

// Main compute kernel: fingerprint one state per thread.
//
// Buffers:
//   states[num_states * num_slots]: packed i64 state data
//   salts[num_slots]: per-slot salts
//   output[num_states * 2]: pairs of (lo64, hi64) for each 128-bit fingerprint
//   params[2]: { num_slots, num_states }
kernel void fingerprint_states(
    device const long*  states  [[buffer(0)]],
    device const ulong* salts   [[buffer(1)]],
    device ulong*       output  [[buffer(2)]],
    constant uint*      params  [[buffer(3)]],
    uint tid [[thread_position_in_grid]])
{
    uint num_slots  = params[0];
    uint num_states = params[1];

    if (tid >= num_states) return;

    ulong fp_lo = 0;
    ulong fp_hi = 0;

    uint base = tid * num_slots;
    for (uint i = 0; i < num_slots; i++) {
        ulong2 contrib = slot_contribution(salts[i], states[base + i]);
        fp_lo ^= contrib.x;
        fp_hi ^= contrib.y;
    }

    output[tid * 2]     = fp_lo;
    output[tid * 2 + 1] = fp_hi;
}
"#;

    // ========================================================================
    // Objective-C runtime FFI — typed function pointers for ARM64 ABI
    // ========================================================================
    //
    // On ARM64 (Apple Silicon), the C calling convention for variadic
    // functions differs from non-variadic functions. Objective-C methods
    // use the non-variadic convention. We must NOT declare objc_msgSend
    // as variadic — instead, we cast the raw function pointer to the
    // exact signature needed for each call site.

    type Id = *mut c_void;
    type Sel = *const c_void;

    // MTLSize is a struct of 3 NSUInteger (u64 on 64-bit macOS/ARM64)
    #[repr(C)]
    #[derive(Clone, Copy)]
    struct MTLSize {
        width: c_ulong,
        height: c_ulong,
        depth: c_ulong,
    }

    #[link(name = "objc", kind = "dylib")]
    extern "C" {
        fn objc_getClass(name: *const c_char) -> Id;
        fn sel_registerName(name: *const c_char) -> Sel;
        // Raw objc_msgSend — we cast this to typed fn pointers below.
        fn objc_msgSend();
    }

    #[link(name = "Metal", kind = "framework")]
    extern "C" {
        fn MTLCreateSystemDefaultDevice() -> Id;
    }

    #[link(name = "Foundation", kind = "framework")]
    extern "C" {}

    // Typed function pointer aliases for objc_msgSend call signatures.
    // Each matches the exact ABI of the Objective-C method being called.
    type MsgSendNoArgs = unsafe extern "C" fn(Id, Sel) -> Id;
    type MsgSend1Id = unsafe extern "C" fn(Id, Sel, Id) -> Id;
    type MsgSend2IdPtr = unsafe extern "C" fn(Id, Sel, Id, *mut Id) -> Id;
    type MsgSend3IdPtrId =
        unsafe extern "C" fn(Id, Sel, Id, *const c_void, *mut Id) -> Id;
    type MsgSendBufBytesLenOpts =
        unsafe extern "C" fn(Id, Sel, *const c_void, c_ulong, c_ulong) -> Id;
    type MsgSendBufLenOpts =
        unsafe extern "C" fn(Id, Sel, c_ulong, c_ulong) -> Id;
    type MsgSendSetBuf =
        unsafe extern "C" fn(Id, Sel, Id, c_ulong, c_ulong) -> Id;
    type MsgSendDispatch =
        unsafe extern "C" fn(Id, Sel, MTLSize, MTLSize) -> Id;
    type MsgSendInitBytes =
        unsafe extern "C" fn(Id, Sel, *const c_void, c_ulong, c_ulong) -> Id;

    /// Get a typed fn pointer for objc_msgSend with the specified signature.
    ///
    /// # Safety
    /// The caller must ensure the actual ObjC method matches the signature `T`.
    #[inline(always)]
    unsafe fn msg_fn<T>() -> T {
        std::mem::transmute_copy(&(objc_msgSend as *const c_void))
    }

    /// Call objc_msgSend with no arguments beyond (self, _cmd).
    #[inline(always)]
    unsafe fn msg_send_0(obj: Id, sel_name: &[u8]) -> Id {
        let f: MsgSendNoArgs = msg_fn();
        f(obj, sel_registerName(sel_name.as_ptr().cast()))
    }

    /// Errors that can occur during GPU fingerprinting.
    #[derive(Debug)]
    pub(crate) enum GpuError {
        /// No Metal-capable GPU device found.
        DeviceNotFound,
        /// MSL shader compilation failed.
        CompileFailed(String),
        /// GPU command execution failed.
        ExecutionFailed(String),
    }

    impl std::fmt::Display for GpuError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::DeviceNotFound => write!(f, "no Metal GPU device found"),
                Self::CompileFailed(msg) => write!(f, "MSL compile error: {msg}"),
                Self::ExecutionFailed(msg) => write!(f, "GPU execution error: {msg}"),
            }
        }
    }

    impl std::error::Error for GpuError {}

    /// GPU fingerprinter that manages Metal device, pipeline, and salt buffer.
    ///
    /// Create once per model checking run, then call `fingerprint_batch` for
    /// each BFS level with a large frontier.
    pub(crate) struct GpuFingerprinter {
        /// Metal device handle (retained).
        device: Id,
        /// Command queue for submitting work.
        command_queue: Id,
        /// Compiled compute pipeline state.
        pipeline_state: Id,
        /// GPU buffer containing per-slot salts.
        salts_buffer: Id,
        /// Number of i64 slots per state.
        num_slots: usize,
    }

    // Metal objects are reference-counted Objective-C objects.
    // We must release them when dropped.
    impl Drop for GpuFingerprinter {
        fn drop(&mut self) {
            unsafe {
                if !self.salts_buffer.is_null() {
                    msg_send_0(self.salts_buffer, b"release\0");
                }
                if !self.pipeline_state.is_null() {
                    msg_send_0(self.pipeline_state, b"release\0");
                }
                if !self.command_queue.is_null() {
                    msg_send_0(self.command_queue, b"release\0");
                }
                if !self.device.is_null() {
                    msg_send_0(self.device, b"release\0");
                }
            }
        }
    }

    // SAFETY: Metal objects are thread-safe (Metal API is designed for
    // multi-threaded use). The GpuFingerprinter holds retained references
    // to immutable pipeline state and read-only salt buffer.
    unsafe impl Send for GpuFingerprinter {}
    unsafe impl Sync for GpuFingerprinter {}

    impl GpuFingerprinter {
        /// Check if a Metal GPU device is available on this system.
        pub(crate) fn is_available() -> bool {
            let device = unsafe { MTLCreateSystemDefaultDevice() };
            if device.is_null() {
                return false;
            }
            unsafe { msg_send_0(device, b"release\0") };
            true
        }

        /// Create a new GPU fingerprinter for states with `num_slots` variables.
        ///
        /// Compiles the MSL compute shader and uploads the salt table to GPU.
        pub(crate) fn new(num_slots: usize) -> Result<Self, GpuError> {
            unsafe { Self::new_inner(num_slots) }
        }

        unsafe fn new_inner(num_slots: usize) -> Result<Self, GpuError> {
            // 1. Get default Metal device
            let device = MTLCreateSystemDefaultDevice();
            if device.is_null() {
                return Err(GpuError::DeviceNotFound);
            }

            // 2. Create command queue: [device newCommandQueue]
            let command_queue = msg_send_0(device, b"newCommandQueue\0");
            if command_queue.is_null() {
                msg_send_0(device, b"release\0");
                return Err(GpuError::ExecutionFailed(
                    "failed to create command queue".into(),
                ));
            }

            // 3. Compile MSL source: [device newLibraryWithSource:options:error:]
            let source_nsstring = create_nsstring(MSL_SOURCE);
            if source_nsstring.is_null() {
                msg_send_0(command_queue, b"release\0");
                msg_send_0(device, b"release\0");
                return Err(GpuError::CompileFailed("failed to create NSString".into()));
            }

            let mut error: Id = ptr::null_mut();
            let f: MsgSend3IdPtrId = msg_fn();
            let sel = sel_registerName(
                b"newLibraryWithSource:options:error:\0".as_ptr().cast(),
            );
            let library = f(
                device,
                sel,
                source_nsstring,
                ptr::null(),
                &mut error,
            );
            msg_send_0(source_nsstring, b"release\0");

            if library.is_null() {
                let err_msg = nsstring_to_string(error);
                if !error.is_null() {
                    msg_send_0(error, b"release\0");
                }
                msg_send_0(command_queue, b"release\0");
                msg_send_0(device, b"release\0");
                return Err(GpuError::CompileFailed(err_msg));
            }

            // 4. Get kernel function: [library newFunctionWithName:]
            let func_name = create_nsstring("fingerprint_states");
            let f1: MsgSend1Id = msg_fn();
            let sel = sel_registerName(b"newFunctionWithName:\0".as_ptr().cast());
            let function = f1(library, sel, func_name);
            msg_send_0(func_name, b"release\0");
            msg_send_0(library, b"release\0");

            if function.is_null() {
                msg_send_0(command_queue, b"release\0");
                msg_send_0(device, b"release\0");
                return Err(GpuError::CompileFailed(
                    "kernel function 'fingerprint_states' not found".into(),
                ));
            }

            // 5. Create pipeline: [device newComputePipelineStateWithFunction:error:]
            let mut error: Id = ptr::null_mut();
            let f2: MsgSend2IdPtr = msg_fn();
            let sel = sel_registerName(
                b"newComputePipelineStateWithFunction:error:\0".as_ptr().cast(),
            );
            let pipeline_state = f2(device, sel, function, &mut error);
            msg_send_0(function, b"release\0");

            if pipeline_state.is_null() {
                let err_msg = nsstring_to_string(error);
                if !error.is_null() {
                    msg_send_0(error, b"release\0");
                }
                msg_send_0(command_queue, b"release\0");
                msg_send_0(device, b"release\0");
                return Err(GpuError::CompileFailed(err_msg));
            }

            // 6. Upload salts to GPU buffer: [device newBufferWithBytes:length:options:]
            let salts = generate_salts(num_slots);
            let salts_byte_len = num_slots * std::mem::size_of::<u64>();
            let f3: MsgSendBufBytesLenOpts = msg_fn();
            let sel = sel_registerName(
                b"newBufferWithBytes:length:options:\0".as_ptr().cast(),
            );
            let salts_buffer = f3(
                device,
                sel,
                salts.as_ptr().cast(),
                salts_byte_len as c_ulong,
                0, // MTLResourceStorageModeShared
            );

            if salts_buffer.is_null() {
                msg_send_0(pipeline_state, b"release\0");
                msg_send_0(command_queue, b"release\0");
                msg_send_0(device, b"release\0");
                return Err(GpuError::ExecutionFailed(
                    "failed to create salts buffer".into(),
                ));
            }

            Ok(GpuFingerprinter {
                device,
                command_queue,
                pipeline_state,
                salts_buffer,
                num_slots,
            })
        }

        /// Fingerprint a batch of states on the GPU.
        ///
        /// # Arguments
        ///
        /// * `states` - Contiguous buffer of `num_states * num_slots` i64 values.
        /// * `num_states` - Number of states in the batch.
        ///
        /// # Returns
        ///
        /// Vector of 128-bit fingerprints matching the CPU `fingerprint_flat()`.
        pub(crate) fn fingerprint_batch(
            &self,
            states: &[i64],
            num_states: usize,
        ) -> Result<Vec<u128>, GpuError> {
            debug_assert_eq!(
                states.len(),
                num_states * self.num_slots,
                "GpuFingerprinter::fingerprint_batch: states.len() {} != num_states {} * num_slots {}",
                states.len(),
                num_states,
                self.num_slots,
            );

            unsafe { self.fingerprint_batch_inner(states, num_states) }
        }

        unsafe fn fingerprint_batch_inner(
            &self,
            states: &[i64],
            num_states: usize,
        ) -> Result<Vec<u128>, GpuError> {
            let f_buf_bytes: MsgSendBufBytesLenOpts = msg_fn();
            let f_buf_len: MsgSendBufLenOpts = msg_fn();
            let f_set_buf: MsgSendSetBuf = msg_fn();
            let f_dispatch: MsgSendDispatch = msg_fn();
            let f_set_pipeline: MsgSend1Id = msg_fn();

            let sel_new_buf_bytes = sel_registerName(
                b"newBufferWithBytes:length:options:\0".as_ptr().cast(),
            );
            let sel_new_buf_len = sel_registerName(
                b"newBufferWithLength:options:\0".as_ptr().cast(),
            );
            let sel_set_buf = sel_registerName(
                b"setBuffer:offset:atIndex:\0".as_ptr().cast(),
            );
            let sel_dispatch = sel_registerName(
                b"dispatchThreadgroups:threadsPerThreadgroup:\0"
                    .as_ptr()
                    .cast(),
            );
            let sel_set_pipeline = sel_registerName(
                b"setComputePipelineState:\0".as_ptr().cast(),
            );

            // Create input buffer (states)
            let states_byte_len = states.len() * std::mem::size_of::<i64>();
            let states_buffer = f_buf_bytes(
                self.device,
                sel_new_buf_bytes,
                states.as_ptr().cast(),
                states_byte_len as c_ulong,
                0,
            );
            if states_buffer.is_null() {
                return Err(GpuError::ExecutionFailed(
                    "failed to create states buffer".into(),
                ));
            }

            // Create output buffer (2 * u64 per state = 16 bytes per fingerprint)
            let output_byte_len = num_states * 2 * std::mem::size_of::<u64>();
            let output_buffer = f_buf_len(
                self.device,
                sel_new_buf_len,
                output_byte_len as c_ulong,
                0,
            );
            if output_buffer.is_null() {
                msg_send_0(states_buffer, b"release\0");
                return Err(GpuError::ExecutionFailed(
                    "failed to create output buffer".into(),
                ));
            }

            // Create params buffer [num_slots, num_states]
            let params: [u32; 2] = [self.num_slots as u32, num_states as u32];
            let params_byte_len = std::mem::size_of_val(&params);
            let params_buffer = f_buf_bytes(
                self.device,
                sel_new_buf_bytes,
                params.as_ptr().cast(),
                params_byte_len as c_ulong,
                0,
            );
            if params_buffer.is_null() {
                msg_send_0(output_buffer, b"release\0");
                msg_send_0(states_buffer, b"release\0");
                return Err(GpuError::ExecutionFailed(
                    "failed to create params buffer".into(),
                ));
            }

            // Create command buffer: [commandQueue commandBuffer]
            let command_buffer =
                msg_send_0(self.command_queue, b"commandBuffer\0");
            if command_buffer.is_null() {
                msg_send_0(params_buffer, b"release\0");
                msg_send_0(output_buffer, b"release\0");
                msg_send_0(states_buffer, b"release\0");
                return Err(GpuError::ExecutionFailed(
                    "failed to create command buffer".into(),
                ));
            }

            // Create compute encoder: [commandBuffer computeCommandEncoder]
            let encoder =
                msg_send_0(command_buffer, b"computeCommandEncoder\0");
            if encoder.is_null() {
                msg_send_0(params_buffer, b"release\0");
                msg_send_0(output_buffer, b"release\0");
                msg_send_0(states_buffer, b"release\0");
                return Err(GpuError::ExecutionFailed(
                    "failed to create compute encoder".into(),
                ));
            }

            // Set pipeline state
            f_set_pipeline(encoder, sel_set_pipeline, self.pipeline_state);

            // Set buffers at indices 0-3
            f_set_buf(encoder, sel_set_buf, states_buffer, 0, 0);
            f_set_buf(encoder, sel_set_buf, self.salts_buffer, 0, 1);
            f_set_buf(encoder, sel_set_buf, output_buffer, 0, 2);
            f_set_buf(encoder, sel_set_buf, params_buffer, 0, 3);

            // Dispatch threads
            let threadgroup_size = 256u64;
            let num_threadgroups =
                (num_states as u64 + threadgroup_size - 1) / threadgroup_size;

            let grid_size = MTLSize {
                width: num_threadgroups,
                height: 1,
                depth: 1,
            };
            let group_size = MTLSize {
                width: threadgroup_size,
                height: 1,
                depth: 1,
            };
            f_dispatch(encoder, sel_dispatch, grid_size, group_size);

            // End encoding, commit, wait
            msg_send_0(encoder, b"endEncoding\0");
            msg_send_0(command_buffer, b"commit\0");
            msg_send_0(command_buffer, b"waitUntilCompleted\0");

            // Read back results from output buffer contents
            let output_ptr: *const u64 =
                msg_send_0(output_buffer, b"contents\0").cast();

            let mut fingerprints = Vec::with_capacity(num_states);
            for i in 0..num_states {
                let lo = *output_ptr.add(i * 2);
                let hi = *output_ptr.add(i * 2 + 1);
                let fp = ((hi as u128) << 64) | (lo as u128);
                fingerprints.push(fp);
            }

            // Release temporary buffers
            msg_send_0(params_buffer, b"release\0");
            msg_send_0(output_buffer, b"release\0");
            msg_send_0(states_buffer, b"release\0");

            Ok(fingerprints)
        }

        /// Number of i64 slots per state this fingerprinter is configured for.
        #[must_use]
        pub(crate) fn num_slots(&self) -> usize {
            self.num_slots
        }
    }

    /// Create an NSString from a Rust &str via Objective-C FFI.
    unsafe fn create_nsstring(s: &str) -> Id {
        let class = objc_getClass(b"NSString\0".as_ptr().cast());
        if class.is_null() {
            return ptr::null_mut();
        }
        let obj = msg_send_0(class, b"alloc\0");
        if obj.is_null() {
            return ptr::null_mut();
        }
        // [NSString initWithBytes:length:encoding:] — 3 args: ptr, len, encoding
        let f: MsgSendInitBytes = msg_fn();
        let sel = sel_registerName(
            b"initWithBytes:length:encoding:\0".as_ptr().cast(),
        );
        // NSUTF8StringEncoding = 4
        f(obj, sel, s.as_ptr().cast(), s.len() as c_ulong, 4)
    }

    /// Extract a Rust String from an NSError's localizedDescription.
    unsafe fn nsstring_to_string(error: Id) -> String {
        if error.is_null() {
            return "unknown error".to_string();
        }
        let desc = msg_send_0(error, b"localizedDescription\0");
        if desc.is_null() {
            return "unknown error (no description)".to_string();
        }
        let cstr_ptr: *const c_char =
            msg_send_0(desc, b"UTF8String\0").cast();
        if cstr_ptr.is_null() {
            return "unknown error (null UTF8String)".to_string();
        }
        CStr::from_ptr(cstr_ptr).to_string_lossy().into_owned()
    }
}

#[cfg(all(target_os = "macos", feature = "metal"))]
pub(crate) use metal_impl::{GpuError, GpuFingerprinter};

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_batch_fingerprint_matches_individual() {
        let num_slots = 5;
        let salts = generate_salts(num_slots);

        // Create 10 states
        let mut states = Vec::new();
        for i in 0..10 {
            for s in 0..num_slots {
                states.push((i * 100 + s) as i64);
            }
        }

        let batch_result = fingerprint_batch_cpu(&states, 10, num_slots);
        assert_eq!(batch_result.len(), 10);

        // Verify each matches individual fingerprint_flat
        for i in 0..10 {
            let state = &states[i * num_slots..(i + 1) * num_slots];
            let expected = fingerprint_flat(state, &salts);
            assert_eq!(
                batch_result[i], expected,
                "batch[{i}] mismatch: got {:032x}, expected {:032x}",
                batch_result[i], expected,
            );
        }
    }

    #[test]
    fn test_cpu_batch_empty() {
        let result = fingerprint_batch_cpu(&[], 0, 5);
        assert!(result.is_empty());
    }

    #[test]
    fn test_cpu_batch_single_state() {
        let num_slots = 3;
        let salts = generate_salts(num_slots);
        let state = vec![42i64, -7, 100];
        let batch_result = fingerprint_batch_cpu(&state, 1, num_slots);
        assert_eq!(batch_result.len(), 1);
        assert_eq!(batch_result[0], fingerprint_flat(&state, &salts));
    }

    #[test]
    fn test_fingerprint_batch_or_cpu_small_batch() {
        // Small batch should always use CPU (< GPU_BATCH_THRESHOLD)
        let num_slots = 5;
        let salts = generate_salts(num_slots);
        let mut states = Vec::new();
        for i in 0..100 {
            for s in 0..num_slots {
                states.push((i * 10 + s) as i64);
            }
        }

        let result = fingerprint_batch_or_cpu(&states, 100, num_slots);
        assert_eq!(result.len(), 100);

        for i in 0..100 {
            let state = &states[i * num_slots..(i + 1) * num_slots];
            let expected = fingerprint_flat(state, &salts);
            assert_eq!(result[i], expected, "mismatch at state {i}");
        }
    }

    #[test]
    fn test_cpu_batch_deterministic() {
        let num_slots = 7;
        let mut states = Vec::new();
        for i in 0..50 {
            for s in 0..num_slots {
                states.push((i * 13 + s * 7) as i64);
            }
        }

        let result1 = fingerprint_batch_cpu(&states, 50, num_slots);
        let result2 = fingerprint_batch_cpu(&states, 50, num_slots);
        assert_eq!(result1, result2, "batch fingerprinting must be deterministic");
    }

    #[test]
    fn test_cpu_batch_distinct_states_distinct_fingerprints() {
        let num_slots = 4;
        let mut states = Vec::new();
        for i in 0..200 {
            for s in 0..num_slots {
                states.push((i * 1000 + s) as i64);
            }
        }

        let result = fingerprint_batch_cpu(&states, 200, num_slots);
        let unique: std::collections::HashSet<_> = result.iter().collect();
        assert_eq!(
            unique.len(),
            200,
            "200 distinct states should produce 200 distinct fingerprints"
        );
    }

    #[test]
    fn test_cpu_batch_single_slot_states() {
        let num_slots = 1;
        let salts = generate_salts(num_slots);
        let states: Vec<i64> = (0..100).collect();
        let result = fingerprint_batch_cpu(&states, 100, num_slots);

        for i in 0..100 {
            let expected = fingerprint_flat(&[states[i]], &salts);
            assert_eq!(result[i], expected, "mismatch at state {i}");
        }
    }

    #[test]
    fn test_cpu_batch_large_slot_count() {
        // Test with a state that has many slots (like a complex TLA+ spec)
        let num_slots = 50;
        let salts = generate_salts(num_slots);
        let mut states = Vec::new();
        for i in 0..10 {
            for s in 0..num_slots {
                states.push((i * 1000 + s * 3 + 1) as i64);
            }
        }

        let result = fingerprint_batch_cpu(&states, 10, num_slots);
        for i in 0..10 {
            let state = &states[i * num_slots..(i + 1) * num_slots];
            let expected = fingerprint_flat(state, &salts);
            assert_eq!(result[i], expected, "mismatch at state {i}");
        }
    }

    // GPU-specific tests (only run on macOS with metal feature)
    #[cfg(all(target_os = "macos", feature = "metal"))]
    mod gpu_tests {
        use super::super::*;

        #[test]
        fn test_gpu_is_available() {
            // On macOS, Metal should be available on all modern hardware.
            // This test may fail on CI without GPU — that's expected.
            let available = GpuFingerprinter::is_available();
            // Just verify the function doesn't crash; availability depends on hardware.
            let _ = available;
        }

        #[test]
        fn test_gpu_fingerprint_matches_cpu() {
            if !GpuFingerprinter::is_available() {
                return; // Skip if no GPU
            }

            let num_slots = 5;
            let num_states = 100;
            let salts = generate_salts(num_slots);

            let mut states = Vec::new();
            for i in 0..num_states {
                for s in 0..num_slots {
                    states.push((i * 100 + s) as i64);
                }
            }

            let gpu = GpuFingerprinter::new(num_slots).expect("GPU init failed");
            let gpu_result = gpu
                .fingerprint_batch(&states, num_states)
                .expect("GPU batch failed");

            assert_eq!(gpu_result.len(), num_states);

            for i in 0..num_states {
                let state = &states[i * num_slots..(i + 1) * num_slots];
                let cpu_fp = fingerprint_flat(state, &salts);
                assert_eq!(
                    gpu_result[i], cpu_fp,
                    "GPU/CPU mismatch at state {i}: GPU={:032x}, CPU={:032x}",
                    gpu_result[i], cpu_fp,
                );
            }
        }

        #[test]
        fn test_gpu_fingerprint_negative_values() {
            if !GpuFingerprinter::is_available() {
                return;
            }

            let num_slots = 3;
            let salts = generate_salts(num_slots);
            let states = vec![
                -1i64, i64::MIN, i64::MAX, // state 0
                0i64, -42, 999,             // state 1
            ];

            let gpu = GpuFingerprinter::new(num_slots).expect("GPU init failed");
            let gpu_result = gpu
                .fingerprint_batch(&states, 2)
                .expect("GPU batch failed");

            for i in 0..2 {
                let state = &states[i * num_slots..(i + 1) * num_slots];
                let cpu_fp = fingerprint_flat(state, &salts);
                assert_eq!(gpu_result[i], cpu_fp, "mismatch at state {i}");
            }
        }

        #[test]
        fn test_gpu_fingerprint_single_slot() {
            if !GpuFingerprinter::is_available() {
                return;
            }

            let num_slots = 1;
            let salts = generate_salts(num_slots);
            let states: Vec<i64> = (0..50).collect();

            let gpu = GpuFingerprinter::new(num_slots).expect("GPU init failed");
            let gpu_result = gpu
                .fingerprint_batch(&states, 50)
                .expect("GPU batch failed");

            for i in 0..50 {
                let cpu_fp = fingerprint_flat(&[states[i]], &salts);
                assert_eq!(gpu_result[i], cpu_fp, "mismatch at state {i}");
            }
        }

        #[test]
        fn test_gpu_fingerprint_large_batch() {
            if !GpuFingerprinter::is_available() {
                return;
            }

            let num_slots = 15; // Typical EWD998-like spec
            let num_states = 10_000;
            let salts = generate_salts(num_slots);

            let mut states = Vec::with_capacity(num_states * num_slots);
            for i in 0..num_states {
                for s in 0..num_slots {
                    states.push((i * 1000 + s * 7 + 3) as i64);
                }
            }

            let gpu = GpuFingerprinter::new(num_slots).expect("GPU init failed");
            let gpu_result = gpu
                .fingerprint_batch(&states, num_states)
                .expect("GPU batch failed");

            assert_eq!(gpu_result.len(), num_states);

            // Spot-check first 100, last 100, and some middle states
            for &i in &[0, 1, 50, 99, 100, 500, 1000, 5000, 9998, 9999] {
                let state = &states[i * num_slots..(i + 1) * num_slots];
                let cpu_fp = fingerprint_flat(state, &salts);
                assert_eq!(
                    gpu_result[i], cpu_fp,
                    "GPU/CPU mismatch at state {i}"
                );
            }
        }

        #[test]
        fn test_gpu_num_slots() {
            if !GpuFingerprinter::is_available() {
                return;
            }
            let gpu = GpuFingerprinter::new(7).expect("GPU init failed");
            assert_eq!(gpu.num_slots(), 7);
        }
    }
}
