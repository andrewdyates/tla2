// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared Petri/MCC CLI runtime for `tla2` and `pnml-tools`.

use std::path::{Path, PathBuf};

use anyhow::{bail, Result};
use clap::{Args, ValueEnum};

use crate::error::PnmlError;
use crate::examination::Examination;
use crate::explorer::{CheckpointConfig, ExplorationConfig, FpsetBackend, StorageMode};

/// Shared runtime knobs for Petri/MCC execution.
#[derive(Debug, Clone, Args)]
pub struct PetriRunArgs {
    /// Timeout in seconds (overrides BK_TIME_CONFINEMENT env var).
    #[arg(long)]
    pub timeout: Option<u64>,

    /// Maximum number of states to explore (0 = auto-size from available memory).
    #[arg(long)]
    pub max_states: Option<usize>,

    /// Fraction of available memory to use for state storage (>0.0 and <=1.0).
    #[arg(long, default_value = "0.25", value_parser = parse_memory_fraction)]
    pub memory_fraction: f64,

    /// Number of BFS worker threads (must be >= 1; 1 = sequential).
    #[arg(long, default_value = "1", value_parser = parse_positive_usize)]
    pub threads: usize,

    /// State-storage backend.
    #[arg(long, value_enum, default_value = "auto")]
    pub storage: RequestedStorageMode,

    /// Directory where mmap/disk storage keeps backing files.
    #[arg(long, value_name = "DIR")]
    pub storage_dir: Option<PathBuf>,

    /// Directory where explorer checkpoints are written.
    #[arg(long)]
    pub checkpoint_dir: Option<PathBuf>,

    /// Save a checkpoint every N explored states (must be >= 1).
    #[arg(long, default_value = "100000", value_parser = parse_positive_usize)]
    pub checkpoint_interval_states: usize,

    /// Resume observer exploration from `--checkpoint-dir`.
    #[arg(long, requires = "checkpoint_dir")]
    pub resume_checkpoint: bool,

    /// Fingerprint set backend for parallel BFS deduplication.
    ///
    /// `sharded` uses RwLock-based sharded sets (default).
    /// `cas` uses lock-free CAS-based open addressing, eliminating lock
    /// contention at 8+ workers.
    #[arg(long, value_enum, default_value = "sharded")]
    pub fpset_backend: RequestedFpsetBackend,
}

/// User-facing storage selection before it is mapped onto explorer backends.
#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum RequestedStorageMode {
    Auto,
    Memory,
    Mmap,
    Disk,
    /// Fingerprint-only BFS: 8 bytes/state via lock-free CAS table.
    FingerprintOnly,
}

/// User-facing fingerprint set backend selection before it is mapped onto
/// the internal [`FpsetBackend`] configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum RequestedFpsetBackend {
    /// RwLock-based sharded fingerprint sets (default).
    Sharded,
    /// Lock-free CAS-based open addressing (16 partitions).
    ///
    /// Eliminates RwLock contention that caps sharded throughput at ~4 workers.
    Cas,
}

/// Which top-level command is invoking the shared Petri runtime.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PetriCommandMode {
    /// Direct `tla2 petri` invocation with explicit inputs.
    Petri,
    /// MCC-style invocation (`tla2 mcc` or legacy `pnml-tools`).
    Mcc,
}

impl PetriCommandMode {
    fn requires_model_input(self) -> bool {
        matches!(self, Self::Petri)
    }

    fn requires_explicit_examination(self) -> bool {
        matches!(self, Self::Petri)
    }
}

/// Parse the shared memory-fraction flag.
pub fn parse_memory_fraction(raw: &str) -> Result<f64, String> {
    let fraction = raw
        .parse::<f64>()
        .map_err(|err| format!("invalid memory fraction '{raw}': {err}"))?;
    if !(fraction > 0.0 && fraction <= 1.0) {
        return Err(String::from("memory-fraction must be > 0 and <= 1.0"));
    }
    Ok(fraction)
}

/// Parse shared positive-integer flags that must be at least 1.
pub fn parse_positive_usize(raw: &str) -> Result<usize, String> {
    let value = raw
        .parse::<usize>()
        .map_err(|err| format!("invalid positive integer '{raw}': {err}"))?;
    if value == 0 {
        return Err(String::from("value must be >= 1"));
    }
    Ok(value)
}

/// Normalize the state limit option: `0` means auto-size.
#[must_use]
pub fn resolve_max_states(max_states: Option<usize>) -> Option<usize> {
    max_states.filter(|&limit| limit != 0)
}

fn auto_size_message(
    num_places: usize,
    packed_places: usize,
    bytes_per_place: usize,
    primary_capacity: usize,
    storage_mode: StorageMode,
    unbounded: bool,
) -> String {
    let bytes_per_state = packed_places * bytes_per_place + 48;
    let limit_suffix = if unbounded {
        String::from("state_limit=unbounded")
    } else {
        format!("max_states={primary_capacity}")
    };
    if packed_places == num_places {
        format!(
            "auto-sized ({storage_mode:?}): {} places × {}B/place = {}B/state → primary_capacity={} {}",
            num_places, bytes_per_place, bytes_per_state, primary_capacity, limit_suffix,
        )
    } else {
        format!(
            "auto-sized ({storage_mode:?}): {} places ({} packed) × {}B/place = {}B/state → primary_capacity={} {}",
            num_places, packed_places, bytes_per_place, bytes_per_state, primary_capacity, limit_suffix,
        )
    }
}

#[must_use]
pub fn resolve_fpset_backend(requested: RequestedFpsetBackend) -> FpsetBackend {
    match requested {
        RequestedFpsetBackend::Sharded => FpsetBackend::Sharded,
        RequestedFpsetBackend::Cas => FpsetBackend::Cas,
    }
}

#[must_use]
pub fn resolve_storage_mode(
    requested: RequestedStorageMode,
    explicit_limit: Option<usize>,
    auto_budget: usize,
) -> StorageMode {
    match requested {
        RequestedStorageMode::Memory => StorageMode::Memory,
        RequestedStorageMode::Mmap => StorageMode::Mmap,
        RequestedStorageMode::Disk => StorageMode::Disk,
        RequestedStorageMode::FingerprintOnly => StorageMode::FingerprintOnly,
        RequestedStorageMode::Auto => match explicit_limit {
            Some(limit) if limit <= auto_budget => StorageMode::Memory,
            Some(limit) if limit <= auto_budget.saturating_mul(4).max(auto_budget) => {
                StorageMode::Mmap
            }
            Some(_) | None => StorageMode::Disk,
        },
    }
}

#[must_use]
pub fn checkpoint_supported(examination: Examination) -> bool {
    matches!(
        examination,
        Examination::ReachabilityDeadlock
            | Examination::OneSafe
            | Examination::QuasiLiveness
            | Examination::StableMarking
            | Examination::StateSpace
    )
}

fn read_trimmed_env_var(key: &str) -> Option<String> {
    std::env::var(key)
        .ok()
        .map(|value| value.trim().to_owned())
        .filter(|value| !value.is_empty())
}

fn normalize_model_dir(path: &Path) -> Result<PathBuf> {
    if path.is_dir() {
        return Ok(path.to_path_buf());
    }
    let treat_as_file = path.is_file()
        || path
            .extension()
            .and_then(|ext| ext.to_str())
            .is_some_and(|ext| ext.eq_ignore_ascii_case("pnml"));
    if !treat_as_file {
        return Ok(path.to_path_buf());
    }

    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    if parent.as_os_str().is_empty() {
        Ok(PathBuf::from("."))
    } else {
        Ok(parent.to_path_buf())
    }
}

fn resolve_model_dir(mode: PetriCommandMode, model_input: Option<PathBuf>) -> Result<PathBuf> {
    match model_input {
        Some(path) => normalize_model_dir(&path),
        None if mode.requires_model_input() => {
            bail!("model path is required for `tla2 petri`");
        }
        None => read_trimmed_env_var("BK_INPUT")
            .map(|value| normalize_model_dir(Path::new(&value)))
            .transpose()
            .map(|path| path.unwrap_or_else(|| PathBuf::from("."))),
    }
}

fn resolve_examination(
    mode: PetriCommandMode,
    examination_name: Option<String>,
) -> Result<Examination> {
    let exam_name = examination_name
        .map(|value| value.trim().to_owned())
        .filter(|value| !value.is_empty())
        .or_else(|| read_trimmed_env_var("BK_EXAMINATION"));
    let Some(exam_name) = exam_name else {
        if mode.requires_explicit_examination() {
            bail!("`tla2 petri` requires --examination <NAME>");
        }
        bail!("examination not specified (use --examination or set BK_EXAMINATION)");
    };
    Ok(Examination::from_name(&exam_name)?)
}

fn validate_run_args(args: &PetriRunArgs) -> Result<()> {
    if args.threads == 0 {
        bail!("--threads must be >= 1");
    }
    if args.checkpoint_interval_states == 0 {
        bail!("--checkpoint-interval-states must be >= 1");
    }
    Ok(())
}

fn build_config(
    model: &crate::model::PreparedModel,
    args: &PetriRunArgs,
) -> Result<ExplorationConfig> {
    validate_run_args(args)?;
    let deadline = crate::timeout::compute_deadline(args.timeout);
    let workers = args.threads;
    let explicit_limit = resolve_max_states(args.max_states);
    let info = ExplorationConfig::describe_auto(model.net(), Some(args.memory_fraction));
    let storage_mode = resolve_storage_mode(args.storage, explicit_limit, info.max_states);

    let mut config = if let Some(max_states) = explicit_limit {
        let base = ExplorationConfig::new(max_states)
            .with_deadline(deadline)
            .with_workers(workers)
            .with_storage_mode(storage_mode)
            .with_storage_dir(args.storage_dir.clone());
        if storage_mode == StorageMode::Memory {
            base
        } else {
            base.with_storage_primary_capacity(info.max_states.min(max_states).max(1))
        }
    } else if storage_mode == StorageMode::Memory {
        eprintln!(
            "{}",
            auto_size_message(
                info.num_places,
                info.packed_places,
                info.bytes_per_place,
                info.max_states,
                storage_mode,
                false,
            )
        );
        ExplorationConfig::auto_sized(model.net(), deadline, Some(args.memory_fraction))
            .with_workers(workers)
            .with_storage_mode(storage_mode)
            .with_storage_dir(args.storage_dir.clone())
    } else {
        eprintln!(
            "{}",
            auto_size_message(
                info.num_places,
                info.packed_places,
                info.bytes_per_place,
                info.max_states,
                storage_mode,
                true,
            )
        );
        ExplorationConfig::new(usize::MAX)
            .with_deadline(deadline)
            .with_workers(workers)
            .with_storage_mode(storage_mode)
            .with_storage_primary_capacity(info.max_states)
            .with_storage_dir(args.storage_dir.clone())
    };

    if let Some(dir) = args.checkpoint_dir.clone() {
        config = config.with_checkpoint(
            CheckpointConfig::new(dir, args.checkpoint_interval_states)
                .with_resume(args.resume_checkpoint),
        );
    }

    config = config.with_fpset_backend(resolve_fpset_backend(args.fpset_backend));

    Ok(config)
}

/// Run Petri/MCC execution through the shared `tla-petri` runtime.
pub fn run_cli(
    mode: PetriCommandMode,
    model_input: Option<PathBuf>,
    examination_name: Option<String>,
    args: PetriRunArgs,
) -> Result<()> {
    if args.resume_checkpoint && args.checkpoint_dir.is_none() {
        bail!("--resume-checkpoint requires --checkpoint-dir");
    }

    let model_dir = resolve_model_dir(mode, model_input)?;
    let examination = resolve_examination(mode, examination_name)?;
    if args.checkpoint_dir.is_some() && !checkpoint_supported(examination) {
        bail!(
            "checkpoint/resume currently supports ReachabilityDeadlock, OneSafe, QuasiLiveness, StableMarking, and StateSpace"
        );
    }
    if args.resume_checkpoint {
        let dir = args
            .checkpoint_dir
            .as_ref()
            .expect("checkpoint dir validated above");
        if !dir.join("checkpoint.json").exists() {
            bail!(
                "resume requested but no checkpoint found at {}",
                dir.display()
            );
        }
    }

    let model = match crate::model::load_model_dir(&model_dir) {
        Ok(model) => model,
        Err(PnmlError::UnsupportedNetType { .. }) => {
            let model_name = model_dir
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("unknown");
            println!(
                "{}",
                crate::output::cannot_compute_line(model_name, examination.as_str())
            );
            return Ok(());
        }
        Err(error) => return Err(error.into()),
    };

    let config = build_config(&model, &args)?;
    crate::model::run_examination_for_model(&model, examination, &config);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // Serialize env-var tests so BK_INPUT/BK_EXAMINATION mutations do not race.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    struct EnvVarGuard<'a> {
        key: &'a str,
        prev: Option<String>,
    }

    impl<'a> EnvVarGuard<'a> {
        fn set(key: &'a str, value: Option<&str>) -> Self {
            let prev = std::env::var(key).ok();
            match value {
                Some(value) => std::env::set_var(key, value),
                None => std::env::remove_var(key),
            }
            Self { key, prev }
        }
    }

    impl Drop for EnvVarGuard<'_> {
        fn drop(&mut self) {
            if let Some(prev) = &self.prev {
                std::env::set_var(self.key, prev);
            } else {
                std::env::remove_var(self.key);
            }
        }
    }

    fn with_env_var<T>(key: &str, value: Option<&str>, f: impl FnOnce() -> T) -> T {
        let _lock = ENV_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let _guard = EnvVarGuard::set(key, value);
        f()
    }

    #[test]
    fn max_states_zero_means_auto_sizing() {
        assert_eq!(resolve_max_states(Some(0)), None);
    }

    #[test]
    fn max_states_nonzero_stays_explicit() {
        assert_eq!(resolve_max_states(Some(123)), Some(123));
    }

    #[test]
    fn parse_memory_fraction_accepts_valid_value() {
        assert_eq!(parse_memory_fraction("0.25").unwrap(), 0.25);
    }

    #[test]
    fn parse_memory_fraction_rejects_zero() {
        let err = parse_memory_fraction("0").expect_err("zero should be rejected");
        assert!(err.contains("memory-fraction must be > 0 and <= 1.0"));
    }

    #[test]
    fn parse_memory_fraction_rejects_above_one() {
        let err = parse_memory_fraction("1.5").expect_err("values above one should fail");
        assert!(err.contains("memory-fraction must be > 0 and <= 1.0"));
    }

    #[test]
    fn parse_positive_usize_accepts_nonzero() {
        assert_eq!(parse_positive_usize("4").unwrap(), 4);
    }

    #[test]
    fn parse_positive_usize_rejects_zero() {
        let err = parse_positive_usize("0").expect_err("zero should be rejected");
        assert!(err.contains(">= 1"));
    }

    #[test]
    fn resolve_storage_mode_prefers_disk_for_unbounded_auto_runs() {
        assert_eq!(
            resolve_storage_mode(RequestedStorageMode::Auto, None, 100),
            StorageMode::Disk
        );
    }

    #[test]
    fn normalize_model_dir_keeps_directories() {
        assert_eq!(
            normalize_model_dir(Path::new("benchmarks/mcc/2024/INPUTS")).unwrap(),
            PathBuf::from("benchmarks/mcc/2024/INPUTS")
        );
    }

    #[test]
    fn normalize_model_dir_maps_model_file_to_parent_directory() {
        assert_eq!(
            normalize_model_dir(Path::new("benchmarks/mcc/2024/INPUTS/model.pnml")).unwrap(),
            PathBuf::from("benchmarks/mcc/2024/INPUTS")
        );
    }

    #[test]
    fn normalize_model_dir_maps_bare_model_file_to_current_dir() {
        assert_eq!(
            normalize_model_dir(Path::new("model.pnml")).unwrap(),
            PathBuf::from(".")
        );
    }

    #[test]
    fn resolve_model_dir_requires_input_for_petri_mode() {
        let err = resolve_model_dir(PetriCommandMode::Petri, None)
            .expect_err("petri mode should require an explicit model path");
        assert!(err.to_string().contains("model path is required"));
    }

    #[test]
    fn resolve_examination_requires_explicit_name_for_petri_mode() {
        let err = with_env_var("BK_EXAMINATION", None, || {
            resolve_examination(PetriCommandMode::Petri, None)
                .expect_err("petri mode should require an explicit examination")
        });
        assert!(err.to_string().contains("requires --examination"));
    }

    #[test]
    fn resolve_model_dir_uses_bk_input_for_mcc_mode() {
        let model_dir = with_env_var(
            "BK_INPUT",
            Some("benchmarks/mcc/2024/INPUTS/TokenRing-PT-010"),
            || {
                resolve_model_dir(PetriCommandMode::Mcc, None)
                    .expect("mcc mode should use BK_INPUT")
            },
        );
        assert_eq!(
            model_dir,
            PathBuf::from("benchmarks/mcc/2024/INPUTS/TokenRing-PT-010")
        );
    }

    #[test]
    fn resolve_model_dir_normalizes_bk_input_model_file_for_mcc_mode() {
        let model_dir = with_env_var(
            "BK_INPUT",
            Some("  benchmarks/mcc/2024/INPUTS/TokenRing-PT-010/model.pnml  "),
            || {
                resolve_model_dir(PetriCommandMode::Mcc, None)
                    .expect("mcc mode should normalize file-style BK_INPUT")
            },
        );
        assert_eq!(
            model_dir,
            PathBuf::from("benchmarks/mcc/2024/INPUTS/TokenRing-PT-010")
        );
    }

    #[test]
    fn resolve_model_dir_defaults_to_current_dir_for_mcc_mode() {
        let model_dir = with_env_var("BK_INPUT", None, || {
            resolve_model_dir(PetriCommandMode::Mcc, None)
                .expect("mcc mode should default to current dir")
        });
        assert_eq!(model_dir, PathBuf::from("."));
    }

    #[test]
    fn resolve_model_dir_treats_empty_bk_input_as_current_dir() {
        let model_dir = with_env_var("BK_INPUT", Some("   "), || {
            resolve_model_dir(PetriCommandMode::Mcc, None)
                .expect("blank BK_INPUT should fall back to current dir")
        });
        assert_eq!(model_dir, PathBuf::from("."));
    }

    #[test]
    fn resolve_examination_uses_bk_examination_for_mcc_mode() {
        let examination = with_env_var("BK_EXAMINATION", Some("  ReachabilityDeadlock  "), || {
            resolve_examination(PetriCommandMode::Mcc, None)
                .expect("mcc mode should use BK_EXAMINATION")
        });
        assert_eq!(examination, Examination::ReachabilityDeadlock);
    }

    #[test]
    fn resolve_examination_ignores_blank_bk_examination_in_mcc_mode() {
        let err = with_env_var("BK_EXAMINATION", Some("   "), || {
            resolve_examination(PetriCommandMode::Mcc, None)
                .expect_err("blank BK_EXAMINATION should be treated as missing")
        });
        assert!(err.to_string().contains("examination not specified"));
    }

    #[test]
    fn resolve_examination_rejects_blank_cli_name_for_petri_mode() {
        let err = resolve_examination(PetriCommandMode::Petri, Some("   ".to_string()))
            .expect_err("blank CLI examination should be treated as missing");
        assert!(err.to_string().contains("requires --examination"));
    }

    #[test]
    fn validate_run_args_rejects_zero_threads() {
        let err = validate_run_args(&PetriRunArgs {
            timeout: None,
            max_states: None,
            memory_fraction: 0.25,
            threads: 0,
            storage: RequestedStorageMode::Auto,
            storage_dir: None,
            checkpoint_dir: None,
            checkpoint_interval_states: 100_000,
            resume_checkpoint: false,
            fpset_backend: RequestedFpsetBackend::Sharded,
        })
        .expect_err("zero threads should be rejected");
        assert!(err.to_string().contains("--threads must be >= 1"));
    }

    #[test]
    fn validate_run_args_rejects_zero_checkpoint_interval() {
        let err = validate_run_args(&PetriRunArgs {
            timeout: None,
            max_states: None,
            memory_fraction: 0.25,
            threads: 1,
            storage: RequestedStorageMode::Auto,
            storage_dir: None,
            checkpoint_dir: Some(PathBuf::from("checkpoint")),
            checkpoint_interval_states: 0,
            resume_checkpoint: false,
            fpset_backend: RequestedFpsetBackend::Sharded,
        })
        .expect_err("zero checkpoint interval should be rejected");
        assert!(err
            .to_string()
            .contains("--checkpoint-interval-states must be >= 1"));
    }

    #[test]
    fn resolve_fpset_backend_sharded() {
        assert_eq!(
            resolve_fpset_backend(RequestedFpsetBackend::Sharded),
            FpsetBackend::Sharded,
        );
    }

    #[test]
    fn resolve_fpset_backend_cas() {
        assert_eq!(
            resolve_fpset_backend(RequestedFpsetBackend::Cas),
            FpsetBackend::Cas,
        );
    }
}
