// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Context for checking cache hits.
pub(super) struct CacheLookupCtx<'a> {
    pub(super) cache_file: &'a cache::CacheFile,
    pub(super) cache_key: &'a str,
    pub(super) config_key: &'a str,
    pub(super) signature: &'a str,
    pub(super) force: bool,
    pub(super) output_format: OutputFormat,
    pub(super) max_states: usize,
    pub(super) max_depth: usize,
}

/// Check for a cache hit and print cached results if found. Returns true if hit.
pub(super) fn check_cache_hit(ctx: &CacheLookupCtx<'_>) -> Result<bool> {
    if ctx.force {
        return Ok(false);
    }
    let entry = match ctx.cache_file.entries.get(ctx.cache_key) {
        Some(e) => e,
        None => return Ok(false),
    };
    if entry.config != ctx.config_key
        || entry.signature != ctx.signature
        || !matches!(entry.result, cache::CacheResult::Pass)
        || entry.stats.is_none()
    {
        return Ok(false);
    }
    // Only use the cache for human output (CheckStats is non-exhaustive).
    if !matches!(ctx.output_format, OutputFormat::Human) {
        return Ok(false);
    }
    println!(
        "Cache hit: PASS (sig: {}, verified {})",
        entry.signature, entry.verified_at
    );
    if let Some(secs) = entry.duration_secs {
        println!("Cached run time: {:.3}s", secs);
    }
    println!();

    let stats = entry
        .stats
        .as_ref()
        .context("cache entry missing stats for PASS")?;

    if let Some(bounds) = check_report::format_configured_bounds(ctx.max_states, ctx.max_depth) {
        println!(
            "Model checking complete: No errors found within configured bounds ({}).",
            bounds
        );
    } else {
        println!("Model checking complete: No errors found (exhaustive).");
    }
    println!();
    println!("Statistics:");
    println!(
        "  States found: {}{}",
        stats.states_found,
        check_report::format_guard_suppression_suffix(stats.suppressed_guard_errors as usize)
    );
    println!("  Initial states: {}", stats.initial_states);
    println!("  Transitions: {}", stats.transitions);
    println!("  Max queue depth: {}", stats.max_queue_depth);
    println!("  Time: {:.3}s", 0.0);
    if !stats.detected_actions.is_empty() {
        println!();
        println!("Detected actions ({}):", stats.detected_actions.len());
        for action in &stats.detected_actions {
            println!("  {}", action);
        }
    }
    #[cfg(feature = "memory-stats")]
    tla_check::memory_stats::print_stats();
    Ok(true)
}

/// Context for updating the cache after model checking.
pub(super) struct CacheUpdateCtx<'a> {
    pub(super) result: &'a CheckResult,
    pub(super) cache_file: &'a mut cache::CacheFile,
    pub(super) cache_path: &'a Path,
    pub(super) cache_key: &'a str,
    pub(super) config_key: &'a str,
    pub(super) signature: &'a str,
    pub(super) config: &'a Config,
    pub(super) dependencies: &'a [String],
    pub(super) cache_options: &'a cache::CheckOptions,
    pub(super) elapsed: std::time::Duration,
    pub(super) output_format: OutputFormat,
}

/// Update the incremental cache on successful model checking (Part of #706).
pub(super) fn update_check_cache(ctx: CacheUpdateCtx<'_>) {
    if let CheckResult::Success(stats) = ctx.result {
        let entry = cache::CacheEntry {
            config: ctx.config_key.to_string(),
            signature: ctx.signature.to_string(),
            result: cache::CacheResult::Pass,
            state_count: Some(stats.states_found as u64),
            invariants_checked: ctx.config.invariants.clone(),
            duration_secs: Some(ctx.elapsed.as_secs_f64()),
            verified_at: chrono::Utc::now().to_rfc3339(),
            dependencies: ctx.dependencies.to_vec(),
            options: ctx.cache_options.clone(),
            stats: Some(cache::CacheStats {
                states_found: stats.states_found as u64,
                initial_states: stats.initial_states as u64,
                max_queue_depth: stats.max_queue_depth as u64,
                transitions: stats.transitions as u64,
                max_depth: stats.max_depth as u64,
                suppressed_guard_errors: stats.suppressed_guard_errors as u64,
                detected_actions: stats.detected_actions.clone(),
            }),
        };
        ctx.cache_file
            .entries
            .insert(ctx.cache_key.to_string(), entry);
        ctx.cache_file.tool_version = cache::tool_fingerprint().to_string();
        if let Err(e) = cache::save_cache(ctx.cache_path, ctx.cache_file) {
            if matches!(ctx.output_format, OutputFormat::Human) {
                eprintln!(
                    "Warning: failed to write cache {}: {e}",
                    ctx.cache_path.display()
                );
            }
        }
    }
}
