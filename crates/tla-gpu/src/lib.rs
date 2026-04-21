// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU-accelerated batch operations for TLA2 model checking.
//!
//! This crate provides GPU compute acceleration via `wgpu` (Metal on macOS,
//! Vulkan on Linux). The primary entry point is [`GpuContext`], which wraps
//! a wgpu device and queue along with pre-compiled compute pipelines.
//!
//! ## Feature Gate
//!
//! This crate is intended to be an optional dependency of `tla-check`,
//! gated behind `--features gpu`.
//!
//! ## Phase 1: Batch Fingerprinting
//!
//! The [`GpuContext::fingerprint_batch`] method ships a batch of N states
//! to the GPU and computes their fingerprints in parallel. The result is
//! bit-identical to the CPU reference implementation.
//!
//! ## Apple Silicon Unified Memory
//!
//! On Apple Silicon, wgpu's Metal backend maps GPU buffers into the unified
//! address space. This means zero-copy data transfer between CPU and GPU,
//! making even small batches worthwhile.

pub mod error;
pub mod fingerprint;
pub mod flat_fingerprint_gpu;

pub use error::GpuError;
pub use fingerprint::FingerprintResult;
pub use flat_fingerprint_gpu::{FlatFingerprintGpu, FlatFingerprintResult};

/// GPU compute context for batch model checking operations.
///
/// Wraps a wgpu device, queue, and pre-compiled compute pipelines.
/// Initialized once at checker startup, then reused for all GPU dispatches.
pub struct GpuContext {
    pub(crate) device: wgpu::Device,
    pub(crate) queue: wgpu::Queue,
    pub(crate) fingerprint_pipeline: wgpu::ComputePipeline,
}

impl GpuContext {
    /// Initialize the GPU context.
    ///
    /// Requests a GPU adapter, obtains a device and queue, and compiles the
    /// fingerprint compute shader. Returns `GpuError::NoAdapter` if no
    /// suitable GPU is found.
    ///
    /// # Errors
    ///
    /// - [`GpuError::NoAdapter`] if no GPU adapter is available.
    /// - [`GpuError::DeviceRequest`] if the adapter cannot provide a device.
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
                    label: Some("tla-gpu"),
                    required_features: wgpu::Features::empty(),
                    required_limits: wgpu::Limits::default(),
                    memory_hints: wgpu::MemoryHints::Performance,
                },
                None,
            )
            .await?;

        let shader_source = include_str!("shaders/fingerprint.wgsl");
        let shader_module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("fingerprint_shader"),
            source: wgpu::ShaderSource::Wgsl(shader_source.into()),
        });

        let fingerprint_pipeline =
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("fingerprint_pipeline"),
                layout: None, // Auto-layout from shader bindings
                module: &shader_module,
                entry_point: Some("main"),
                compilation_options: Default::default(),
                cache: None,
            });

        Ok(Self {
            device,
            queue,
            fingerprint_pipeline,
        })
    }

    /// Check if a GPU adapter is available without fully initializing.
    ///
    /// Useful for quick feature detection before committing to GPU path.
    pub async fn is_available() -> bool {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
            backends: wgpu::Backends::all(),
            ..Default::default()
        });
        instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                compatible_surface: None,
                force_fallback_adapter: false,
            })
            .await
            .is_some()
    }
}
