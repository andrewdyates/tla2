// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Module search path discovery and file lookup.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use super::error::LoadError;
use super::ModuleLoader;
#[cfg(test)]
use crate::stdlib::is_stdlib_module;

fn env_library_paths() -> &'static [PathBuf] {
    static PATHS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    PATHS
        .get_or_init(|| {
            let mut search_paths = Vec::new();
            for key in ["TLA_PATH", "TLA_LIBRARY", "TLA2_LIB"] {
                if let Some(raw) = std::env::var_os(key) {
                    for path in std::env::split_paths(&raw) {
                        if path.exists() && !search_paths.contains(&path) {
                            search_paths.push(path);
                        }
                    }
                }
            }
            search_paths
        })
        .as_slice()
}

impl ModuleLoader {
    /// Create a new module loader with base directory derived from the main file
    pub fn new(main_file: &Path) -> Self {
        let base_dir = main_file
            .parent()
            .map_or_else(|| PathBuf::from("."), std::path::Path::to_path_buf);

        let mut search_paths: Vec<PathBuf> = Vec::new();

        // Parse environment-provided library paths.
        //
        // Note: `split_paths` uses the platform's path separator (e.g. ':' on
        // Unix, ';' on Windows).
        for path in env_library_paths() {
            if !search_paths.contains(path) {
                search_paths.push(path.clone());
            }
        }

        // Auto-discover standard library paths
        // 1. Relative to executable (for installed versions)
        if let Ok(exe_path) = std::env::current_exe() {
            if let Some(exe_dir) = exe_path.parent() {
                // Check sibling directories: ../lib/tla, ../share/tla2/lib
                for rel in &["../lib/tla", "../share/tla2/lib", "lib/tla"] {
                    let lib_path = exe_dir.join(rel);
                    if lib_path.exists() && !search_paths.contains(&lib_path) {
                        search_paths.push(lib_path);
                    }
                }
            }
        }

        // 2. Relative to the source tree for development (repo-local checkouts).
        //
        // This avoids a fragile dependency on the process current directory.
        // In particular, callers may execute the `tla` binary from outside the
        // repo root (e.g. `cd /tmp && /path/to/target/release/tla ...`), but we
        // still want to find repo-local stub modules like `FunctionTheorems`.
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        for rel in &["../../test_specs/tla_library", "../../test_specs"] {
            let lib_path = manifest_dir.join(rel);
            if lib_path.exists() && !search_paths.contains(&lib_path) {
                search_paths.push(lib_path);
            }
        }

        // 3. Relative to cwd for development (test_specs/tla_library, test_specs).
        //
        // Kept for compatibility with ad-hoc scripts that run from the repo root.
        for rel in &["test_specs/tla_library", "test_specs"] {
            let lib_path = PathBuf::from(rel);
            if lib_path.exists() && !search_paths.contains(&lib_path) {
                search_paths.push(lib_path);
            }
        }

        Self {
            base_dir,
            search_paths,
            cache: std::collections::HashMap::new(),
            next_file_id: 1, // 0 is reserved for main file
            loading_stack: Vec::new(),
        }
    }

    /// Create a loader with explicit base directory
    pub fn with_base_dir(base_dir: PathBuf) -> Self {
        Self {
            base_dir,
            search_paths: Vec::new(),
            cache: std::collections::HashMap::new(),
            next_file_id: 1,
            loading_stack: Vec::new(),
        }
    }

    /// Add a search path
    pub fn add_search_path(&mut self, path: PathBuf) {
        self.search_paths.push(path);
    }

    /// Get the base directory
    pub fn base_dir(&self) -> &Path {
        &self.base_dir
    }

    /// Check if a module is a standard library module
    #[cfg(test)]
    pub(crate) fn is_stdlib(&self, name: &str) -> bool {
        is_stdlib_module(name)
    }

    /// Find the .tla file for a module
    pub(super) fn find_module(&self, name: &str) -> Result<PathBuf, LoadError> {
        let filename = format!("{name}.tla");
        let mut searched = Vec::new();

        // Search in base directory first
        let base_path = self.base_dir.join(&filename);
        searched.push(self.base_dir.clone());
        if base_path.exists() {
            return Ok(base_path);
        }

        // Search in additional search paths
        for search_path in &self.search_paths {
            searched.push(search_path.clone());
            let path = search_path.join(&filename);
            if path.exists() {
                return Ok(path);
            }
        }

        // Search parent directories (up to 3 levels)
        let mut current = self.base_dir.clone();
        for _ in 0..3 {
            if let Some(parent) = current.parent() {
                current = parent.to_path_buf();
                searched.push(current.clone());
                let path = current.join(&filename);
                if path.exists() {
                    return Ok(path);
                }
            } else {
                break;
            }
        }

        Err(LoadError::NotFound {
            module: name.to_string(),
            search_paths: searched,
        })
    }
}
