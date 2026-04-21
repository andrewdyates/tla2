// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error types and data structures for the module loader.

use std::path::PathBuf;

use crate::ast::Module;
use crate::span::FileId;
use crate::syntax::SyntaxNode;

/// Error during module loading
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum LoadError {
    /// Module file not found
    NotFound {
        module: String,
        search_paths: Vec<PathBuf>,
    },
    /// IO error reading file
    IoError { path: PathBuf, message: String },
    /// Parse error in module
    ParseError { path: PathBuf, errors: Vec<String> },
    /// Lower error in module
    LowerError { path: PathBuf, errors: Vec<String> },
    /// Circular dependency detected
    CircularDependency { chain: Vec<String> },
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::NotFound {
                module,
                search_paths,
            } => {
                write!(f, "Module '{module}' not found. Searched in:")?;
                for path in search_paths {
                    write!(f, "\n  - {}", path.display())?;
                }
                Ok(())
            }
            LoadError::IoError { path, message } => {
                write!(f, "Error reading {}: {}", path.display(), message)
            }
            LoadError::ParseError { path, errors } => {
                write!(f, "Parse errors in {}:", path.display())?;
                for err in errors {
                    write!(f, "\n  {err}")?;
                }
                Ok(())
            }
            LoadError::LowerError { path, errors } => {
                write!(f, "Lower errors in {}:", path.display())?;
                for err in errors {
                    write!(f, "\n  {err}")?;
                }
                Ok(())
            }
            LoadError::CircularDependency { chain } => {
                write!(
                    f,
                    "Circular module dependency detected: {}",
                    chain.join(" -> ")
                )
            }
        }
    }
}

impl std::error::Error for LoadError {}

/// Loaded module with metadata
#[derive(Debug, Clone)]
pub struct LoadedModule {
    /// The parsed and lowered module
    pub module: Module,
    /// The syntax tree (for SPECIFICATION resolution)
    pub syntax_tree: SyntaxNode,
    /// Path to the source file
    pub path: PathBuf,
    /// File ID for span tracking
    pub file_id: FileId,
}
