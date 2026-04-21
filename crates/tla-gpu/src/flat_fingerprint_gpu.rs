// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU batch fingerprinting for flat i64 state arrays.
//!
//! Ships a batch of N states (each: `slots_per_state` i64 values) plus
//! pre-computed per-slot splitmix64 salts to the GPU. A WGSL compute shader
//! computes one 128-bit fingerprint per state in parallel using the
//! XOR-accumulator algorithm from `tla-check::state::flat_fingerprint`.
//!
//! The GPU result is bit-identical to the CPU reference implementation.
//!
//! Part of #3956: GPU Phase 1 — Metal compute shader for batch state fingerprinting.

use crate::error::GpuError;

/// Uniform parameters for the flat fingerprint compute shader.
///
/// Layout must match the WGSL `Params` struct exactly (16 bytes, 4x u32).
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct FlatFingerprintParams {
    /// Number of i64 slots per state.
    slots_per_state: u32,
    /// Number of states in the batch.
    num_states: u32,
    /// Padding to align to 16 bytes.
    _pad0: u32,
    _pad1: u32,
}

/// Result of a GPU flat fingerprint batch computation.
pub struct FlatFingerprintResult {
    /// One 128-bit fingerprint per state, in input order.
    pub fingerprints: Vec<u128>,
}

/// GPU context specialized for flat-state fingerprinting.
///
/// Wraps a wgpu device, queue, and the flat fingerprint compute pipeline.
/// Created once at checker startup, reused for all GPU dispatches.
///
/// Part of #3956.
pub struct FlatFingerprintGpu {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
}

impl FlatFingerprintGpu {
    /// Initialize the flat fingerprint GPU context.
    ///
    /// Requests a GPU adapter (Metal on macOS), obtains a device and queue,
    /// and compiles the flat fingerprint WGSL shader.
    ///
    /// # Errors
    ///
    /// - [`GpuError::NoAdapter`] if no GPU is available.
    /// - [`GpuError::DeviceRequest`] if device creation fails.
    pub async fn new() -> Result<Self, GpuError> {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
            backends: wgpu::Backends::all(),
            ..Default::default()
        });

        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                compatible_surface: None,
                force_fallback_adapter: false,
            })
            .await
            .ok_or(GpuError::NoAdapter)?;

        let (device, queue) = adapter
            .request_device(
                &wgpu::DeviceDescriptor {
                    label: Some("tla-gpu-flat-fp"),
                    required_features: wgpu::Features::empty(),
                    required_limits: wgpu::Limits::default(),
                    memory_hints: wgpu::MemoryHints::Performance,
                },
                None,
            )
            .await?;

        let shader_source = include_str!("shaders/flat_fingerprint.wgsl");
        let shader_module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("flat_fingerprint_shader"),
            source: wgpu::ShaderSource::Wgsl(shader_source.into()),
        });

        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("flat_fingerprint_pipeline"),
            layout: None,
            module: &shader_module,
            entry_point: Some("main"),
            compilation_options: Default::default(),
            cache: None,
        });

        Ok(Self {
            device,
            queue,
            pipeline,
        })
    }

    /// Compute 128-bit fingerprints for a batch of flat states on the GPU.
    ///
    /// # Arguments
    ///
    /// * `states_flat` - Contiguous i64 arena: `[s0_slot0, s0_slot1, ..., s1_slot0, ...]`.
    ///   Length must be `num_states * slots_per_state`.
    /// * `salts` - Per-slot splitmix64 salts from `generate_salts()`.
    ///   Length must be `slots_per_state`.
    /// * `slots_per_state` - Number of i64 values per state.
    ///
    /// # Errors
    ///
    /// Returns `GpuError` if dimensions are inconsistent or GPU ops fail.
    pub fn fingerprint_batch(
        &self,
        states_flat: &[i64],
        salts: &[u64],
        slots_per_state: usize,
    ) -> Result<FlatFingerprintResult, GpuError> {
        if slots_per_state == 0 {
            return Err(GpuError::ZeroVariables);
        }
        if states_flat.is_empty() {
            return Err(GpuError::EmptyBatch);
        }
        if states_flat.len() % slots_per_state != 0 {
            return Err(GpuError::StateLengthMismatch {
                len: states_flat.len(),
                num_vars: slots_per_state,
            });
        }
        if salts.len() != slots_per_state {
            return Err(GpuError::SaltLengthMismatch {
                salts_len: salts.len(),
                num_vars: slots_per_state,
            });
        }

        let num_states = states_flat.len() / slots_per_state;

        let params = FlatFingerprintParams {
            slots_per_state: slots_per_state as u32,
            num_states: num_states as u32,
            _pad0: 0,
            _pad1: 0,
        };

        // Reinterpret i64 as u64 for byte casting (same bit pattern).
        // SAFETY: i64 and u64 have identical layout; we cast the slice pointer.
        let states_as_u64: &[u64] =
            unsafe { std::slice::from_raw_parts(states_flat.as_ptr().cast::<u64>(), states_flat.len()) };

        // Create GPU buffers
        let states_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("flat_fp_states"),
            size: (states_as_u64.len() * 8) as u64,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let salts_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("flat_fp_salts"),
            size: (salts.len() * 8) as u64,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        // Output: 4 x u32 per state = 16 bytes per state
        let output_size = (num_states * 16) as u64;
        let output_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("flat_fp_output"),
            size: output_size,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });

        let staging_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("flat_fp_staging"),
            size: output_size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let params_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("flat_fp_params"),
            size: std::mem::size_of::<FlatFingerprintParams>() as u64,
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        // Upload data
        self.queue
            .write_buffer(&states_buffer, 0, bytemuck::cast_slice(states_as_u64));
        self.queue
            .write_buffer(&salts_buffer, 0, bytemuck::cast_slice(salts));
        self.queue
            .write_buffer(&params_buffer, 0, bytemuck::bytes_of(&params));

        // Bind group
        let bind_group_layout = self.pipeline.get_bind_group_layout(0);
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("flat_fp_bind_group"),
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
                label: Some("flat_fp_encoder"),
            });

        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("flat_fp_pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
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
        let raw_u32s: &[u32] = bytemuck::cast_slice(&data);

        // Reconstruct 128-bit fingerprints from 4 x u32 per state
        let mut fingerprints = Vec::with_capacity(num_states);
        for i in 0..num_states {
            let base = i * 4;
            let lo_lo = raw_u32s[base] as u128;
            let lo_hi = raw_u32s[base + 1] as u128;
            let hi_lo = raw_u32s[base + 2] as u128;
            let hi_hi = raw_u32s[base + 3] as u128;
            let fp = lo_lo | (lo_hi << 32) | (hi_lo << 64) | (hi_hi << 96);
            fingerprints.push(fp);
        }

        drop(data);
        staging_buffer.unmap();

        Ok(FlatFingerprintResult { fingerprints })
    }
}

/// CPU reference implementation of the flat XOR-accumulator batch fingerprint.
///
/// Produces bit-identical results to the GPU shader and to the
/// `fingerprint_flat()` function in `tla-check::state::flat_fingerprint`.
///
/// This is used for testing GPU correctness and as a fallback when no GPU
/// is available.
///
/// Part of #3956.
pub fn cpu_flat_fingerprint_batch(
    states_flat: &[i64],
    salts: &[u64],
    slots_per_state: usize,
) -> Vec<u128> {
    let num_states = states_flat.len() / slots_per_state;
    let mut fingerprints = Vec::with_capacity(num_states);

    for state_idx in 0..num_states {
        let base = state_idx * slots_per_state;
        let mut fp = 0u128;

        for s in 0..slots_per_state {
            let val = states_flat[base + s];
            let salt = salts[s];
            fp ^= slot_contribution(salt, val);
        }

        fingerprints.push(fp);
    }

    fingerprints
}

/// Compute a single slot's contribution to the XOR accumulator.
///
/// Identical to `flat_fingerprint::slot_contribution` in tla-check.
#[inline(always)]
fn slot_contribution(salt: u64, value: i64) -> u128 {
    let bits = value as u64;
    let mixed_lo = splitmix64_mix(salt ^ bits);
    let mixed_hi = splitmix64_mix(salt.rotate_left(32) ^ bits);
    ((mixed_hi as u128) << 64) | (mixed_lo as u128)
}

/// SplitMix64 finalizer / bit mixer.
///
/// Identical to `flat_fingerprint::splitmix64_mix` in tla-check.
#[inline(always)]
fn splitmix64_mix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^ (x >> 31)
}

/// Generate deterministic per-slot salts using splitmix64 PRNG.
///
/// Identical to `flat_fingerprint::generate_salts` in tla-check.
pub fn generate_salts(num_slots: usize) -> Vec<u64> {
    const SEED: u64 = 0x6c62_272e_07bb_0142;
    let mut salts = Vec::with_capacity(num_slots);
    let mut state = SEED;
    for _ in 0..num_slots {
        state = splitmix64_mix(state);
        salts.push(state);
    }
    salts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_flat_fp_deterministic() {
        let salts = generate_salts(3);
        let states = vec![1i64, 2, 3, 4, 5, 6]; // 2 states, 3 slots each
        let fps1 = cpu_flat_fingerprint_batch(&states, &salts, 3);
        let fps2 = cpu_flat_fingerprint_batch(&states, &salts, 3);
        assert_eq!(fps1, fps2, "CPU flat fingerprint must be deterministic");
    }

    #[test]
    fn test_cpu_flat_fp_different_states_differ() {
        let salts = generate_salts(3);
        let states = vec![1i64, 2, 3, 4, 5, 7]; // 2 states with different last slot
        let fps = cpu_flat_fingerprint_batch(&states, &salts, 3);
        assert_eq!(fps.len(), 2);
        assert_ne!(fps[0], fps[1], "different states must produce different fps");
    }

    #[test]
    fn test_cpu_flat_fp_same_states_match() {
        let salts = generate_salts(3);
        let states = vec![1i64, 2, 3, 1, 2, 3]; // 2 identical states
        let fps = cpu_flat_fingerprint_batch(&states, &salts, 3);
        assert_eq!(fps.len(), 2);
        assert_eq!(fps[0], fps[1], "identical states must produce identical fps");
    }

    #[test]
    fn test_cpu_flat_fp_nonzero() {
        let salts = generate_salts(5);
        let states = vec![42i64, -7, 0, i64::MAX, i64::MIN];
        let fps = cpu_flat_fingerprint_batch(&states, &salts, 5);
        assert_eq!(fps.len(), 1);
        assert_ne!(fps[0], 0, "fingerprint should be non-zero for non-trivial input");
    }

    #[test]
    fn test_cpu_flat_fp_collision_resistance() {
        let salts = generate_salts(3);
        let mut seen = std::collections::HashSet::new();
        for i in 0i64..200 {
            let states = vec![i, i.wrapping_mul(7), i.wrapping_add(13)];
            let fps = cpu_flat_fingerprint_batch(&states, &salts, 3);
            assert!(
                seen.insert(fps[0]),
                "collision at i={}: fp {:032x}",
                i,
                fps[0],
            );
        }
        assert_eq!(seen.len(), 200);
    }

    #[test]
    fn test_generate_salts_deterministic() {
        let s1 = generate_salts(10);
        let s2 = generate_salts(10);
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_generate_salts_nonzero() {
        let salts = generate_salts(20);
        for (i, &s) in salts.iter().enumerate() {
            assert_ne!(s, 0, "salt at index {} should be non-zero", i);
        }
    }

    #[test]
    fn test_gpu_flat_fp_matches_cpu() {
        let gpu = pollster::block_on(async { FlatFingerprintGpu::new().await });
        let gpu = match gpu {
            Ok(g) => g,
            Err(GpuError::NoAdapter) => {
                eprintln!("No GPU adapter found, skipping GPU test");
                return;
            }
            Err(e) => panic!("unexpected GPU init error: {e}"),
        };

        let slots_per_state = 5;
        let salts = generate_salts(slots_per_state);

        // Build 8 states
        let mut states_flat = Vec::new();
        for i in 0i64..8 {
            for s in 0..slots_per_state {
                states_flat.push(i * 100 + s as i64);
            }
        }

        let cpu_fps = cpu_flat_fingerprint_batch(&states_flat, &salts, slots_per_state);
        let gpu_result = gpu
            .fingerprint_batch(&states_flat, &salts, slots_per_state)
            .expect("GPU flat fingerprint batch should succeed");

        assert_eq!(
            cpu_fps, gpu_result.fingerprints,
            "GPU flat fingerprints must be bit-identical to CPU reference"
        );
    }

    #[test]
    fn test_gpu_flat_fp_large_batch() {
        let gpu = pollster::block_on(async { FlatFingerprintGpu::new().await });
        let gpu = match gpu {
            Ok(g) => g,
            Err(GpuError::NoAdapter) => {
                eprintln!("No GPU adapter found, skipping GPU test");
                return;
            }
            Err(e) => panic!("unexpected GPU init error: {e}"),
        };

        let slots_per_state = 15; // EWD998-like
        let salts = generate_salts(slots_per_state);

        // Build 1000 states
        let mut states_flat = Vec::new();
        for i in 0i64..1000 {
            for s in 0..slots_per_state {
                states_flat.push(i * slots_per_state as i64 + s as i64);
            }
        }

        let cpu_fps = cpu_flat_fingerprint_batch(&states_flat, &salts, slots_per_state);
        let gpu_result = gpu
            .fingerprint_batch(&states_flat, &salts, slots_per_state)
            .expect("GPU batch should succeed");

        assert_eq!(cpu_fps.len(), 1000);
        assert_eq!(gpu_result.fingerprints.len(), 1000);
        assert_eq!(
            cpu_fps, gpu_result.fingerprints,
            "GPU must match CPU for 1000-state batch"
        );
    }

    #[test]
    fn test_gpu_flat_fp_single_state() {
        let gpu = pollster::block_on(async { FlatFingerprintGpu::new().await });
        let gpu = match gpu {
            Ok(g) => g,
            Err(GpuError::NoAdapter) => {
                eprintln!("No GPU adapter found, skipping GPU test");
                return;
            }
            Err(e) => panic!("unexpected GPU init error: {e}"),
        };

        let slots_per_state = 3;
        let salts = generate_salts(slots_per_state);
        let states_flat = vec![42i64, -7, 0];

        let cpu_fps = cpu_flat_fingerprint_batch(&states_flat, &salts, slots_per_state);
        let gpu_result = gpu
            .fingerprint_batch(&states_flat, &salts, slots_per_state)
            .expect("GPU single state should succeed");

        assert_eq!(cpu_fps, gpu_result.fingerprints);
    }

    #[test]
    fn test_gpu_flat_fp_negative_values() {
        let gpu = pollster::block_on(async { FlatFingerprintGpu::new().await });
        let gpu = match gpu {
            Ok(g) => g,
            Err(GpuError::NoAdapter) => {
                eprintln!("No GPU adapter found, skipping GPU test");
                return;
            }
            Err(e) => panic!("unexpected GPU init error: {e}"),
        };

        let slots_per_state = 4;
        let salts = generate_salts(slots_per_state);
        let states_flat = vec![
            -1i64, -100, i64::MIN, i64::MAX,
            0, 1, -1, 42,
        ];

        let cpu_fps = cpu_flat_fingerprint_batch(&states_flat, &salts, slots_per_state);
        let gpu_result = gpu
            .fingerprint_batch(&states_flat, &salts, slots_per_state)
            .expect("GPU negative values should succeed");

        assert_eq!(cpu_fps, gpu_result.fingerprints);
    }
}
