// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Create and initialize TLC tool output if `--output tlc-tool` is active.
pub(super) fn setup_tlc_tool_output(
    output_format: OutputFormat,
    workers: usize,
) -> Result<Option<tlc_tool::TlcToolOutput>> {
    if matches!(output_format, OutputFormat::TlcTool) && workers != 1 {
        bail!("--output tlc-tool requires --workers 1 (sequential mode) today");
    }
    if !matches!(output_format, OutputFormat::TlcTool) {
        return Ok(None);
    }
    let mut out = tlc_tool::TlcToolOutput::new();
    out.emit(
        tlc_codes::ec::TLC_VERSION,
        tlc_codes::mp::NONE,
        &tlc_tool::format_tlc_version_message(),
    );
    out.emit(
        tlc_codes::ec::TLC_MODE_MC,
        tlc_codes::mp::NONE,
        &tlc_tool::format_tlc_mode_message(workers.max(1)),
    );
    let now = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
    out.emit(
        tlc_codes::ec::TLC_STARTING,
        tlc_codes::mp::NONE,
        &tlc_tool::format_tlc_starting_message(&now),
    );
    out.emit(
        tlc_codes::ec::TLC_SANY_START,
        tlc_codes::mp::NONE,
        tlc_tool::format_tlc_sany_start_message(),
    );
    Ok(Some(out))
}

/// Create fingerprint storage based on CLI options.
///
/// Maps CLI flags to `StorageConfig` and delegates to `FingerprintSetFactory::create()`,
/// centralizing backend selection through the factory (Part of #2568, Step 2).
pub(super) fn setup_fingerprint_storage(
    mmap_fingerprints: Option<usize>,
    huge_pages: bool,
    disk_fingerprints: Option<usize>,
    initial_capacity: Option<usize>,
    store_states: bool,
    mmap_dir: &Option<PathBuf>,
    output_format: OutputFormat,
) -> Result<Option<std::sync::Arc<dyn tla_check::FingerprintSet>>> {
    use tla_check::{FingerprintSetFactory, StorageConfig, StorageMode};

    if let Some(capacity) = mmap_fingerprints {
        if store_states {
            bail!("--mmap-fingerprints is incompatible with --store-states");
        }
        // Part of #3856: select MmapHugePages when --huge-pages or TLA2_HUGE_PAGES is set.
        let mode = if huge_pages {
            StorageMode::MmapHugePages
        } else {
            StorageMode::Mmap
        };
        if matches!(output_format, OutputFormat::Human) {
            let hp_label = if huge_pages { " (huge pages)" } else { "" };
            println!(
                "Mmap fingerprint storage{}: capacity {} ({:.1} MB)",
                hp_label,
                capacity,
                (capacity * 8) as f64 / (1024.0 * 1024.0)
            );
            if let Some(ref dir) = mmap_dir {
                println!("Mmap backing directory: {}", dir.display());
            }
        }
        let config = StorageConfig {
            mode,
            capacity: Some(capacity),
            backing_dir: mmap_dir.clone(),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config)
            .with_context(|| "Failed to create mmap fingerprint storage")?;
        Ok(Some(storage))
    } else if let Some(capacity) = disk_fingerprints {
        if store_states {
            bail!("--disk-fingerprints is incompatible with --store-states");
        }
        let disk_dir = mmap_dir
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("--disk-fingerprints requires --mmap-dir"))?;
        if matches!(output_format, OutputFormat::Human) {
            println!(
                "Disk fingerprint storage: primary capacity {} ({:.1} MB in-memory)",
                capacity,
                (capacity * 8) as f64 / (1024.0 * 1024.0)
            );
            println!("Disk backing directory: {}", disk_dir.display());
            println!("  (fingerprints will evict to disk when primary fills)");
        }
        let config = StorageConfig {
            mode: StorageMode::Disk,
            capacity: Some(capacity),
            backing_dir: Some(disk_dir.clone()),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config)
            .with_context(|| "Failed to create disk fingerprint storage")?;
        Ok(Some(storage))
    } else if let Some(capacity) = initial_capacity {
        const SHARD_BITS: u32 = 6;
        let num_shards = 1usize << SHARD_BITS;
        let per_shard = capacity.div_ceil(num_shards);
        let total_memory_mb = (capacity * 8) as f64 / (1024.0 * 1024.0);
        if matches!(output_format, OutputFormat::Human) {
            println!(
                "Sharded fingerprint storage: {} shards, {} capacity/shard, total {} ({:.1} MB)",
                num_shards, per_shard, capacity, total_memory_mb
            );
        }
        let config = StorageConfig {
            mode: StorageMode::Sharded,
            shard_bits: SHARD_BITS,
            capacity: Some(capacity),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config)
            .with_context(|| "Failed to create sharded fingerprint storage")?;
        Ok(Some(storage))
    } else {
        if mmap_dir.is_some() {
            bail!("--mmap-dir requires --mmap-fingerprints or --disk-fingerprints");
        }
        Ok(None)
    }
}

/// Create trace file and trace locations storage if requested.
pub(super) fn setup_trace_storage(
    trace_file_path: &Option<PathBuf>,
    store_states: bool,
    mmap_trace_locations: Option<usize>,
    mmap_dir: &Option<PathBuf>,
    output_format: OutputFormat,
) -> Result<(Option<TraceFile>, Option<TraceLocationsStorage>)> {
    let trace_file = if let Some(ref path) = trace_file_path {
        if store_states {
            bail!("--trace-file is incompatible with --store-states");
        }
        if matches!(output_format, OutputFormat::Human) {
            println!("Trace file: {}", path.display());
            println!("  (enables counterexample reconstruction from disk)");
        }
        let tf = TraceFile::create(path)
            .with_context(|| format!("Failed to create trace file: {}", path.display()))?;
        Some(tf)
    } else {
        None
    };
    let trace_locs_storage = if let Some(capacity) = mmap_trace_locations {
        if trace_file_path.is_none() {
            bail!("--mmap-trace-locations requires --trace-file");
        }
        if matches!(output_format, OutputFormat::Human) {
            println!("Mmap trace locations: {} capacity", capacity);
        }
        let storage = TraceLocationsStorage::mmap(capacity, mmap_dir.clone())
            .with_context(|| "Failed to create mmap trace locations storage")?;
        Some(storage)
    } else {
        None
    };
    Ok((trace_file, trace_locs_storage))
}

/// Log checkpoint/resume settings and enforce current CLI mode restrictions.
pub(super) fn log_and_validate_checkpoint(
    checkpoint_dir: &Option<PathBuf>,
    checkpoint_interval: u64,
    resume_from: &Option<PathBuf>,
    workers: usize,
    output_format: OutputFormat,
) -> Result<()> {
    // Log checkpoint configuration (only for human output)
    if matches!(output_format, OutputFormat::Human) {
        if let Some(ref dir) = checkpoint_dir {
            println!("Checkpoint directory: {}", dir.display());
            println!("Checkpoint interval: {} seconds", checkpoint_interval);
        }
    }

    // Log resume information if resuming
    if let Some(ref dir) = resume_from {
        use tla_check::Checkpoint;
        if matches!(output_format, OutputFormat::Human) {
            println!("Resuming from checkpoint: {}", dir.display());
        }
        // Validate checkpoint exists and is loadable (preview info)
        let checkpoint = Checkpoint::load(dir)
            .with_context(|| format!("Failed to load checkpoint from {}", dir.display()))?;
        if matches!(output_format, OutputFormat::Human) {
            println!(
                "  Previous progress: {} states, {} frontier, {} transitions",
                checkpoint.metadata.stats.states_found,
                checkpoint.frontier.len(),
                checkpoint.metadata.stats.transitions
            );
        }
    }

    // Part of #2749: Checkpoint/resume now supported for both sequential and
    // parallel modes. Parallel resume re-explores from scratch (frontier
    // serialization not yet supported for crossbeam work-stealing deques).
    // Auto mode (--workers 0) does not support checkpoint/resume because
    // AdaptiveChecker may switch strategies mid-run.
    if (checkpoint_dir.is_some() || resume_from.is_some()) && workers == 0 {
        bail!("--checkpoint and --resume are not supported with --workers 0 (auto mode). Use --workers 1 or --workers N");
    }

    Ok(())
}
