// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stack of bound variable names during AST traversal.

/// Stack of bound variable names during AST traversal.
///
/// Used to track which names are in scope at any point during traversal.
/// Supports efficient scoping with mark/pop_to for nested binding constructs.
#[derive(Default, Debug)]
pub struct BoundNameStack {
    names: Vec<String>,
}

impl BoundNameStack {
    /// Create a new empty stack.
    pub fn new() -> Self {
        Self::default()
    }

    /// Check if a name is currently bound (in scope).
    pub fn contains(&self, name: &str) -> bool {
        self.names.iter().rev().any(|n| n == name)
    }

    /// Get the current stack depth (for mark/pop_to).
    pub fn mark(&self) -> usize {
        self.names.len()
    }

    /// Pop names back to a previous mark.
    pub fn pop_to(&mut self, mark: usize) {
        self.names.truncate(mark);
    }

    /// Push multiple names onto the stack.
    pub fn push_names(&mut self, names: impl IntoIterator<Item = String>) {
        self.names.extend(names);
    }

    /// Push a single name onto the stack.
    pub fn push(&mut self, name: String) {
        self.names.push(name);
    }
}
