// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Module loader for TLA+ EXTENDS and INSTANCE
//!
//! This module provides functionality to load TLA+ modules from disk,
//! enabling support for user-defined modules referenced via EXTENDS.
//!
//! # Search Order
//!
//! When searching for a module `Foo`, the loader looks in:
//! 1. The same directory as the main .tla file
//! 2. Parent directories (up to a limit)
//! 3. Directories in `TLA_PATH`, `TLA_LIBRARY`, and `TLA2_LIB`
//! 4. Known standard-library locations relative to the executable
//! 5. Repo-local `test_specs/` (development checkouts)
//!
//! # Example
//!
//! ```rust,no_run
//! use std::path::Path;
//! use tla_core::ModuleLoader;
//!
//! # fn main() -> Result<(), tla_core::LoadError> {
//! let mut loader = ModuleLoader::new(Path::new("/path/to/Main.tla"));
//! let _voting = loader.load("Voting")?;
//! # Ok(())
//! # }
//! ```

mod dependency;
mod error;
mod parse;
mod resolution;
mod search;

#[cfg(test)]
mod tests;

// Re-export all public types
pub use error::{LoadError, LoadedModule};

use std::collections::HashMap;
use std::path::PathBuf;

/// Module loader that caches loaded modules
#[derive(Debug)]
pub struct ModuleLoader {
    /// Base directory for module search (directory containing main .tla file)
    pub(super) base_dir: PathBuf,
    /// Additional search paths
    pub(super) search_paths: Vec<PathBuf>,
    /// Cache of loaded modules (module name -> loaded module)
    pub(super) cache: HashMap<String, LoadedModule>,
    /// Counter for file IDs
    pub(super) next_file_id: u32,
    /// Stack for detecting circular dependencies
    pub(super) loading_stack: Vec<String>,
}
