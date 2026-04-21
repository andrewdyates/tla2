// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const CACHE_SCHEMA_VERSION: u32 = 1;
const SIGNATURE_FORMAT_VERSION: &[u8] = b"tla2-check-cache-sig-v3\0";

fn modified_ns(meta: &fs::Metadata) -> u128 {
    use std::time::UNIX_EPOCH;
    meta.modified()
        .ok()
        .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
        .map(|d| d.as_nanos())
        .unwrap_or(0)
}

pub fn tool_fingerprint() -> &'static str {
    static FINGERPRINT: OnceLock<String> = OnceLock::new();
    FINGERPRINT
        .get_or_init(|| {
            let version = env!("CARGO_PKG_VERSION");
            let profile = if cfg!(debug_assertions) {
                "debug"
            } else {
                "release"
            };
            let Ok(exe) = std::env::current_exe() else {
                return format!("{version}+profile:{profile}");
            };
            let Ok(meta) = fs::metadata(&exe) else {
                return format!("{version}+profile:{profile}");
            };

            let len = meta.len();
            let modified_ns = modified_ns(&meta);

            format!("{version}+profile:{profile}+exe:{len}+mtime_ns:{modified_ns}")
        })
        .as_str()
}

fn cached_home_dir() -> &'static Path {
    static HOME: OnceLock<PathBuf> = OnceLock::new();
    HOME.get_or_init(|| {
        std::env::var_os("HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("."))
    })
    .as_path()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheFile {
    pub version: u32,
    pub tool_version: String,
    pub entries: BTreeMap<String, CacheEntry>,
}

impl CacheFile {
    pub fn empty() -> Self {
        Self {
            version: CACHE_SCHEMA_VERSION,
            tool_version: tool_fingerprint().to_string(),
            entries: BTreeMap::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheEntry {
    pub config: String,
    pub signature: String,
    pub result: CacheResult,

    pub state_count: Option<u64>,
    pub invariants_checked: Vec<String>,
    pub duration_secs: Option<f64>,
    pub verified_at: String,

    pub dependencies: Vec<String>,
    pub options: CheckOptions,
    pub stats: Option<CacheStats>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CacheResult {
    Pass,
    Fail,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStats {
    pub states_found: u64,
    pub initial_states: u64,
    pub max_queue_depth: u64,
    pub transitions: u64,
    pub max_depth: u64,
    #[serde(default)]
    pub suppressed_guard_errors: u64,
    pub detected_actions: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckOptions {
    pub no_deadlock: bool,
    #[serde(default)]
    pub check_deadlock: bool,
    pub max_states: u64,
    pub max_depth: u64,
    pub bmc_depth: u64,
    pub pdr_enabled: bool,
    pub por_enabled: bool,
    pub continue_on_error: bool,
}

pub fn default_cache_path() -> PathBuf {
    cached_home_dir().join(".tla2").join("cache.json")
}

pub fn canonical_string(path: &Path) -> String {
    fs::canonicalize(path)
        .unwrap_or_else(|_| path.to_path_buf())
        .to_string_lossy()
        .to_string()
}

pub fn dependency_paths_to_strings(paths: Vec<PathBuf>) -> Vec<String> {
    paths.into_iter().map(|p| canonical_string(&p)).collect()
}

pub fn load_cache(path: &Path) -> Result<CacheFile> {
    let bytes = match fs::read(path) {
        Ok(b) => b,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(CacheFile::empty()),
        Err(e) => return Err(e).with_context(|| format!("read cache {}", path.display())),
    };

    let mut cache: CacheFile = serde_json::from_slice(&bytes).context("parse cache JSON")?;
    if cache.version != CACHE_SCHEMA_VERSION {
        return Ok(CacheFile::empty());
    }

    // The entry signature includes `tool_fingerprint()`, so old entries cannot hit after a tool
    // upgrade anyway. Clear them to avoid confusing cache bloat.
    let cur_tool = tool_fingerprint();
    if cache.tool_version != cur_tool {
        cache.tool_version = cur_tool.to_string();
        cache.entries.clear();
    }

    Ok(cache)
}

pub fn save_cache(path: &Path, cache: &CacheFile) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("create cache dir {}", parent.display()))?;
    }

    let bytes = serde_json::to_vec_pretty(cache).context("serialize cache JSON")?;
    fs::write(path, bytes).with_context(|| format!("write cache {}", path.display()))?;
    Ok(())
}

/// Collect all `TLA2_*` environment variables that could affect model checking
/// behavior. Sorted by key for deterministic hashing. This ensures that running
/// with different env vars (e.g., `TLA2_TIR_EVAL=all`) produces a different
/// cache signature, preventing stale cached results from being reused.
///
/// Part of #3283: the cache signature previously omitted env vars, causing
/// `TLA2_TIR_EVAL` runs to return cached non-TIR results.
pub(crate) fn collect_behavior_env_vars() -> Vec<(String, String)> {
    let mut vars: Vec<(String, String)> = std::env::vars()
        .filter(|(k, _)| k.starts_with("TLA2_"))
        .collect();
    vars.sort_by(|a, b| a.0.cmp(&b.0));
    vars
}

pub fn compute_signature(
    spec_path: &Path,
    spec_bytes: &[u8],
    config_path: &Path,
    config_bytes: &[u8],
    dependencies: &[String],
    options: &CheckOptions,
) -> Result<String> {
    compute_signature_with_env(
        spec_path,
        spec_bytes,
        config_path,
        config_bytes,
        dependencies,
        options,
        &collect_behavior_env_vars(),
    )
}

/// Core signature computation that accepts env vars explicitly.
/// Part of #3283: env vars are included in the hash so that runs with different
/// settings (e.g., `TLA2_TIR_EVAL`, `TLA2_SKIP_LIVENESS`) produce different signatures.
pub(crate) fn compute_signature_with_env(
    spec_path: &Path,
    spec_bytes: &[u8],
    config_path: &Path,
    config_bytes: &[u8],
    dependencies: &[String],
    options: &CheckOptions,
    env_vars: &[(String, String)],
) -> Result<String> {
    let mut hasher = Sha256::new();
    hasher.update(SIGNATURE_FORMAT_VERSION);
    hasher.update(tool_fingerprint().as_bytes());
    hasher.update([0]);

    // Part of #3283: include TLA2_* env vars in signature so that runs with
    // different environment settings (e.g., TLA2_TIR_EVAL, TLA2_SKIP_LIVENESS)
    // do not hit each other's cache entries.
    hasher.update((env_vars.len() as u32).to_le_bytes());
    for (key, val) in env_vars {
        hasher.update(key.as_bytes());
        hasher.update([b'=']);
        hasher.update(val.as_bytes());
        hasher.update([0]);
    }

    hasher.update(canonical_string(spec_path).as_bytes());
    hasher.update((spec_bytes.len() as u64).to_le_bytes());
    hasher.update(spec_bytes);

    hasher.update(canonical_string(config_path).as_bytes());
    hasher.update((config_bytes.len() as u64).to_le_bytes());
    hasher.update(config_bytes);

    let mut deps = dependencies.to_vec();
    deps.sort();
    for dep in deps {
        hasher.update(dep.as_bytes());
        hasher.update([0]);

        // If any dependency module changes, cached results must not be reused. Prefer hashing
        // the file contents; fall back to metadata, and finally to just the path string if
        // neither is available.
        let dep_path = Path::new(&dep);
        if let Ok(mut f) = fs::File::open(dep_path) {
            if let Ok(meta) = f.metadata() {
                hasher.update(meta.len().to_le_bytes());
                hasher.update(modified_ns(&meta).to_le_bytes());
            }

            let mut buf = [0u8; 8192];
            loop {
                match f.read(&mut buf) {
                    Ok(0) => break,
                    Ok(n) => hasher.update(&buf[..n]),
                    Err(_) => break,
                }
            }
        } else if let Ok(meta) = fs::metadata(dep_path) {
            hasher.update(meta.len().to_le_bytes());
            hasher.update(modified_ns(&meta).to_le_bytes());
        }
    }

    let opts_json = serde_json::to_vec(options).context("serialize cache options")?;
    hasher.update(opts_json);

    let digest = hasher.finalize();
    let mut out = String::with_capacity(digest.len() * 2);
    for b in digest {
        use std::fmt::Write as _;
        write!(out, "{:02x}", b).expect("hex formatting into String");
    }
    Ok(out)
}

#[cfg(test)]
mod tests;
