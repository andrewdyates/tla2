// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU batch fingerprinting for CompactValue state arrays.
//!
//! Ships a batch of N states (each: `num_vars` u64 CompactValue bits) plus
//! pre-computed per-variable FNV salts to the GPU. A WGSL compute shader
//! computes one fingerprint per state in parallel.
//!
//! The GPU result is bit-identical to the CPU reference implementation in
//! `tla-check/src/state/value_hash_state.rs::compute_fingerprint_from_compact_array`.

use crate::error::GpuError;
use crate::GpuContext;

/// Uniform parameters passed to the fingerprint compute shader.
///
/// Layout must match the WGSL `Params` struct exactly.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct FingerprintParams {
    /// Number of variables per state.
    num_vars: u32,
    /// Number of states in the batch.
    num_states: u32,
    /// FNV prime low 32 bits.
    fnv_prime_lo: u32,
    /// FNV prime high 32 bits.
    fnv_prime_hi: u32,
}

/// Result of a GPU batch fingerprint computation.
pub struct FingerprintResult {
    /// One 64-bit fingerprint per state, in the same order as the input batch.
    pub fingerprints: Vec<u64>,
}

impl GpuContext {
    /// Compute fingerprints for a batch of states on the GPU.
    ///
    /// # Arguments
    ///
    /// * `states_flat` - Flattened CompactValue bits: `[state0_var0, state0_var1, ...,
    ///   state1_var0, ...]`. Length must be `num_states * num_vars`.
    /// * `salts` - Per-variable FNV salts from `VarRegistry::fp_salt()`.
    ///   Length must be `num_vars`.
    /// * `num_vars` - Number of variables per state.
    ///
    /// # Errors
    ///
    /// Returns `GpuError` if the input dimensions are inconsistent or if a GPU
    /// buffer operation fails.
    pub fn fingerprint_batch(
        &self,
        states_flat: &[u64],
        salts: &[u64],
        num_vars: usize,
    ) -> Result<FingerprintResult, GpuError> {
        if num_vars == 0 {
            return Err(GpuError::ZeroVariables);
        }
        if states_flat.is_empty() {
            return Err(GpuError::EmptyBatch);
        }
        if states_flat.len() % num_vars != 0 {
            return Err(GpuError::StateLengthMismatch {
                len: states_flat.len(),
                num_vars,
            });
        }
        if salts.len() != num_vars {
            return Err(GpuError::SaltLengthMismatch {
                salts_len: salts.len(),
                num_vars,
            });
        }

        let num_states = states_flat.len() / num_vars;

        // FNV-1a prime: 0x00000100_000001b3
        let fnv_prime: u64 = 0x0100_0000_01b3;
        let params = FingerprintParams {
            num_vars: num_vars as u32,
            num_states: num_states as u32,
            fnv_prime_lo: fnv_prime as u32,
            fnv_prime_hi: (fnv_prime >> 32) as u32,
        };

        // Create GPU buffers
        let states_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("fingerprint_states"),
            size: (states_flat.len() * 8) as u64,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let salts_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("fingerprint_salts"),
            size: (salts.len() * 8) as u64,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let output_size = (num_states * 8) as u64;
        let output_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("fingerprint_output"),
            size: output_size,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });

        let staging_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("fingerprint_staging"),
            size: output_size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let params_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("fingerprint_params"),
            size: std::mem::size_of::<FingerprintParams>() as u64,
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        // Upload data
        self.queue
            .write_buffer(&states_buffer, 0, bytemuck::cast_slice(states_flat));
        self.queue
            .write_buffer(&salts_buffer, 0, bytemuck::cast_slice(salts));
        self.queue
            .write_buffer(&params_buffer, 0, bytemuck::bytes_of(&params));

        // Bind group
        let bind_group_layout = self.fingerprint_pipeline.get_bind_group_layout(0);
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("fingerprint_bind_group"),
            layout: &bind_group_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: states_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: salts_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: output_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: params_buffer.as_entire_binding(),
                },
            ],
        });

        // Encode and submit
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("fingerprint_encoder"),
            });

        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("fingerprint_pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.fingerprint_pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            // Dispatch one invocation per state, workgroup size = 64
            let workgroups = (num_states as u32 + 63) / 64;
            pass.dispatch_workgroups(workgroups, 1, 1);
        }

        encoder.copy_buffer_to_buffer(&output_buffer, 0, &staging_buffer, 0, output_size);
        self.queue.submit(std::iter::once(encoder.finish()));

        // Read back results
        let buffer_slice = staging_buffer.slice(..);
        let (tx, rx) = std::sync::mpsc::channel();
        buffer_slice.map_async(wgpu::MapMode::Read, move |result| {
            let _ = tx.send(result);
        });
        self.device.poll(wgpu::Maintain::Wait);

        rx.recv()
            .map_err(|_| GpuError::BufferMapping)?
            .map_err(|_| GpuError::BufferMapping)?;

        let data = buffer_slice.get_mapped_range();
        let fingerprints: Vec<u64> = bytemuck::cast_slice(&data).to_vec();
        drop(data);
        staging_buffer.unmap();

        Ok(FingerprintResult { fingerprints })
    }
}

/// CPU reference implementation of the batch fingerprint algorithm.
///
/// Computes the same result as the GPU shader, useful for testing and fallback.
/// This mirrors `compute_fingerprint_from_compact_array` from tla-check but
/// operates on raw u64 bits rather than `CompactValue` types, making it
/// independent of the tla-value crate.
pub fn cpu_fingerprint_batch(
    states_flat: &[u64],
    salts: &[u64],
    num_vars: usize,
) -> Vec<u64> {
    let fnv_prime: u64 = 0x0100_0000_01b3;
    let num_states = states_flat.len() / num_vars;
    let mut fingerprints = Vec::with_capacity(num_states);

    for state_idx in 0..num_states {
        let base = state_idx * num_vars;
        let mut combined: u64 = 0;

        for var_idx in 0..num_vars {
            let value_bits = states_flat[base + var_idx];
            let value_fp = compact_value_fp_from_bits(value_bits);
            let salt = salts[var_idx];
            let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
            combined ^= contribution;
        }

        // Finalize
        combined = combined.wrapping_mul(fnv_prime);
        combined ^= combined >> 33;
        combined = combined.wrapping_mul(fnv_prime);

        fingerprints.push(combined);
    }

    fingerprints
}

/// Compute a value fingerprint from raw CompactValue bits.
///
/// This is the CPU reference for what the GPU shader does per-variable.
/// For inline types (Bool, SmallInt), it computes the fingerprint directly
/// from the bits. For heap types, it returns the raw bits as a proxy
/// (the caller should not ship heap-backed values to the GPU).
pub(crate) fn compact_value_fp_from_bits(bits: u64) -> u64 {
    let tag = bits & 0b111;

    match tag {
        // TAG_BOOL = 0b010
        0b010 => {
            let b = (bits >> 3) & 1;
            // Bool fingerprint: tag=0 discriminant, then 1 or 0
            // Simple hash: mix tag and value
            let mut h: u64 = 0xcbf2_9ce4_8422_2325; // FNV_OFFSET
            h ^= 0; // bool type tag = 0
            h = h.wrapping_mul(0x0100_0000_01b3);
            h ^= b;
            h = h.wrapping_mul(0x0100_0000_01b3);
            h
        }
        // TAG_INT = 0b001
        0b001 => {
            // Extract i61 value via arithmetic shift
            let n = (bits as i64) >> 3;
            // Int fingerprint: tag=1 discriminant, then LE bytes of i64
            let mut h: u64 = 0xcbf2_9ce4_8422_2325; // FNV_OFFSET
            h ^= 1; // int type tag = 1
            h = h.wrapping_mul(0x0100_0000_01b3);
            for byte in n.to_le_bytes() {
                h ^= byte as u64;
                h = h.wrapping_mul(0x0100_0000_01b3);
            }
            h
        }
        // TAG_HEAP = 0b000 or other tags: return raw bits as proxy.
        // GPU path should only receive inline values.
        _ => bits,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_fingerprint_batch_single_bool_state() {
        // One state with one Bool(true) variable
        // CompactValue::from_bool(true) = TAG_BOOL | (1 << 3) = 0b010 | 0b1000 = 0b1010 = 10
        let states_flat = vec![0b1010_u64]; // Bool(true)
        let salts = vec![0xcbf2_9ce4_8422_2325_u64]; // FNV_OFFSET as salt

        let fps = cpu_fingerprint_batch(&states_flat, &salts, 1);
        assert_eq!(fps.len(), 1);
        // Verify deterministic: same input => same output
        let fps2 = cpu_fingerprint_batch(&states_flat, &salts, 1);
        assert_eq!(fps, fps2);
    }

    #[test]
    fn test_cpu_fingerprint_batch_two_states() {
        // Two states, each with 2 variables: Bool(false), SmallInt(42)
        // Bool(false) = TAG_BOOL = 0b010 = 2
        // SmallInt(42) = (42 << 3) | TAG_INT = 336 | 1 = 337
        let bool_false_bits: u64 = 0b010;
        let int_42_bits: u64 = (42_u64 << 3) | 0b001;

        let states_flat = vec![
            bool_false_bits,
            int_42_bits, // state 0
            bool_false_bits,
            int_42_bits, // state 1 (same)
        ];
        let salts = vec![0xcbf2_9ce4_8422_2325, 0x0100_0000_01b3];

        let fps = cpu_fingerprint_batch(&states_flat, &salts, 2);
        assert_eq!(fps.len(), 2);
        // Same states => same fingerprints
        assert_eq!(fps[0], fps[1]);
    }

    #[test]
    fn test_cpu_fingerprint_batch_different_states_differ() {
        let bool_true_bits: u64 = 0b010 | (1 << 3);
        let bool_false_bits: u64 = 0b010;

        let states_flat = vec![
            bool_true_bits,  // state 0: Bool(true)
            bool_false_bits, // state 1: Bool(false)
        ];
        let salts = vec![0xcbf2_9ce4_8422_2325];

        let fps = cpu_fingerprint_batch(&states_flat, &salts, 1);
        assert_eq!(fps.len(), 2);
        assert_ne!(fps[0], fps[1], "different states must produce different fingerprints");
    }

    #[test]
    fn test_compact_value_fp_from_bits_bool() {
        let fp_true = compact_value_fp_from_bits(0b010 | (1 << 3));
        let fp_false = compact_value_fp_from_bits(0b010);
        assert_ne!(fp_true, fp_false);
    }

    #[test]
    fn test_compact_value_fp_from_bits_int() {
        let fp_0 = compact_value_fp_from_bits((0_u64 << 3) | 0b001);
        let fp_1 = compact_value_fp_from_bits((1_u64 << 3) | 0b001);
        let fp_neg1 = compact_value_fp_from_bits((((-1_i64) as u64) << 3) | 0b001);
        assert_ne!(fp_0, fp_1);
        assert_ne!(fp_0, fp_neg1);
        assert_ne!(fp_1, fp_neg1);
    }

    #[test]
    fn test_gpu_fingerprint_batch_matches_cpu() {
        // Initialize GPU context — skip if no GPU available
        let gpu = pollster::block_on(async {
            GpuContext::new().await
        });
        let gpu = match gpu {
            Ok(g) => g,
            Err(GpuError::NoAdapter) => {
                eprintln!("No GPU adapter found, skipping GPU test");
                return;
            }
            Err(e) => panic!("unexpected GPU init error: {e}"),
        };

        // Build test data: 4 states, 3 vars each
        let bool_true: u64 = 0b010 | (1 << 3);
        let bool_false: u64 = 0b010;
        let int_7: u64 = (7_u64 << 3) | 0b001;
        let int_neg3: u64 = (((-3_i64) as u64) << 3) | 0b001;

        let states_flat = vec![
            bool_true, int_7, bool_false,    // state 0
            bool_false, int_neg3, bool_true, // state 1
            bool_true, int_7, bool_true,     // state 2
            bool_false, int_7, bool_false,   // state 3
        ];
        let salts = vec![
            0xcbf2_9ce4_8422_2325_u64,
            0x0100_0000_01b3_u64,
            0xdead_beef_cafe_babe_u64,
        ];

        let cpu_fps = cpu_fingerprint_batch(&states_flat, &salts, 3);
        let gpu_result = gpu.fingerprint_batch(&states_flat, &salts, 3)
            .expect("GPU fingerprint batch should succeed");

        assert_eq!(
            cpu_fps, gpu_result.fingerprints,
            "GPU fingerprints must be bit-identical to CPU reference"
        );
    }
}
