// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LocalScope: scope tracking for bound variables during preprocessing.
//!
//! Extracted from enumerate.rs as part of #637 parent file decomposition.
//! Part of #3354 Slice 4: LET-binding inlining and substitute_let_names_in_ast
//! removed — those were only consumed by the compiled_guard module.

/// Tracks local variables in scope during preprocessing.
///
/// Used to compute stack depths for O(1) local variable lookup.
/// Variables are added when entering EXISTS bodies and the depth
/// is computed relative to the scope order.
#[derive(Debug, Clone, Default)]
pub struct LocalScope {
    /// Variable names in binding order (first bound = first element)
    /// These are quantifier-bound variables that become LocalVar at runtime.
    vars: Vec<String>,
}

impl LocalScope {
    /// Create an empty scope
    pub fn new() -> Self {
        LocalScope { vars: Vec::new() }
    }

    /// Create a new scope with an additional bound variable (for quantifiers)
    pub fn with_var(&self, name: &str) -> Self {
        let mut vars = self.vars.clone();
        vars.push(name.to_string());
        LocalScope { vars }
    }

    /// Get the depth of a local variable (for O(1) stack access).
    /// Returns None if the variable is not in scope.
    ///
    /// depth=0 means most recently bound (end of vars list)
    pub fn get_depth(&self, name: &str) -> Option<u8> {
        // IMPORTANT: Choose the *innermost* binding when names repeat due to shadowing
        // (e.g., nested quantifiers reusing the same variable name).
        self.vars
            .iter()
            .rev()
            .position(|var| var == name)
            .map(|depth| depth as u8)
    }
}
