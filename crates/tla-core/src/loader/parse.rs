// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! File I/O, parsing, and lowering for module loading.

use std::path::Path;

use super::error::{LoadError, LoadedModule};
use super::ModuleLoader;
use crate::lower::{
    compute_contains_prime, compute_guards_depend_on_prime, compute_has_primed_param,
    compute_is_recursive, lower_all_modules,
};
use crate::span::FileId;
use crate::syntax::{parse_to_syntax_tree, SyntaxNode};

impl ModuleLoader {
    /// Load a module by name
    ///
    /// Returns the cached module if already loaded, otherwise searches for
    /// and parses the .tla file.
    ///
    /// Note: TLA+ "standard library" modules are usually provided by tools
    /// (e.g. SANY/TLC) rather than loaded from disk. However, some specs
    /// vendor community/stdlib modules as `.tla` files alongside the spec
    /// (or via `TLA_PATH`). For correctness, we allow explicit on-disk loads
    /// even when a module name appears in our stdlib registry.
    pub fn load(&mut self, name: &str) -> Result<&LoadedModule, LoadError> {
        // Check cache first
        if self.cache.contains_key(name) {
            return Ok(self.cache.get(name).expect("contains_key checked above"));
        }

        // Check for circular dependency
        if self.loading_stack.contains(&name.to_string()) {
            let mut chain = self.loading_stack.clone();
            chain.push(name.to_string());
            return Err(LoadError::CircularDependency { chain });
        }

        // Find the module file
        let path = self.find_module(name)?;

        // Load and parse the module
        self.loading_stack.push(name.to_string());
        let result = self.load_from_path(name, &path);
        self.loading_stack.pop();

        result?;

        Ok(self
            .cache
            .get(name)
            .expect("load_from_path inserts into cache"))
    }

    /// Load a module from a specific path
    fn load_from_path(&mut self, name: &str, path: &Path) -> Result<(), LoadError> {
        // Read the file
        let source = std::fs::read_to_string(path).map_err(|e| LoadError::IoError {
            path: path.to_path_buf(),
            message: e.to_string(),
        })?;

        // Parse
        let tree = parse_to_syntax_tree(&source);
        // Note: parse_to_syntax_tree doesn't return errors directly,
        // errors are in the green node. For now, we proceed.

        // Lower
        let file_id = FileId(self.next_file_id);
        self.next_file_id += 1;

        let result = lower_all_modules(file_id, &tree);
        if !result.errors.is_empty() {
            return Err(LoadError::LowerError {
                path: path.to_path_buf(),
                errors: result.errors.iter().map(|e| e.message.clone()).collect(),
            });
        }

        if result.modules.is_empty() {
            return Err(LoadError::LowerError {
                path: path.to_path_buf(),
                errors: vec!["No MODULE found in file".to_string()],
            });
        }

        // Cache all modules found in the file, including inline submodules.
        // This is required for specs that use `INSTANCE Inner` where `Inner` is
        // defined inside another module (e.g. diskpaxos/Synod.tla).
        let mut saw_requested = false;
        for mut module in result.modules {
            // Compute which operators contain primed variables (for prime-binding optimization)
            compute_contains_prime(&mut module);
            compute_guards_depend_on_prime(&mut module);
            compute_has_primed_param(&mut module);
            compute_is_recursive(&mut module);
            let module_name = module.name.node.clone();
            if module_name == name {
                saw_requested = true;
            }
            self.cache.insert(
                module_name,
                LoadedModule {
                    module,
                    syntax_tree: tree.clone(),
                    path: path.to_path_buf(),
                    file_id,
                },
            );
        }

        if !saw_requested {
            return Err(LoadError::LowerError {
                path: path.to_path_buf(),
                errors: vec![format!(
                    "File defines no module named '{}' (found different MODULE header)",
                    name
                )],
            });
        }

        Ok(())
    }

    /// Seed the cache with all modules found in a syntax tree.
    ///
    /// This is used to pre-populate the cache with inline modules from the main file.
    /// When a TLA+ file contains multiple MODULE definitions (inline submodules),
    /// those modules should be available for EXTENDS/INSTANCE resolution.
    ///
    /// Example: BufferedRandomAccessFile.tla contains inline modules Common and
    /// RandomAccessFile. When the main module does `EXTENDS Common`, we need
    /// Common to be in the cache before `load_extends` is called.
    pub fn seed_from_syntax_tree(&mut self, tree: &SyntaxNode, path: &Path) {
        let file_id = FileId(0); // Main file always has ID 0

        let result = lower_all_modules(file_id, tree);
        // Ignore errors here - main.rs already reported them during initial lowering

        for module in result.modules {
            let module_name = module.name.node.clone();
            // Don't overwrite existing entries (main module was already processed)
            self.cache
                .entry(module_name)
                .or_insert_with(|| LoadedModule {
                    module,
                    syntax_tree: tree.clone(),
                    path: path.to_path_buf(),
                    file_id,
                });
        }
    }
}
