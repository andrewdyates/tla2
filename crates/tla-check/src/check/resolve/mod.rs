// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Spec resolution: resolve Init/Next/fairness from config or SPECIFICATION operator.

mod scan;
mod specification;

#[cfg(test)]
mod tests;

use super::{CheckError, ResolvedSpec};
use crate::config::Config;
use crate::ConfigCheckError;
use specification::resolve_from_specification_multi;
use tla_core::SyntaxNode;

pub fn resolve_spec_from_config(
    config: &Config,
    syntax_tree: &SyntaxNode,
) -> Result<ResolvedSpec, CheckError> {
    resolve_spec_from_config_with_extends(config, syntax_tree, &[])
}

/// Resolve Init/Next from config, searching both main and extended module syntax trees.
///
/// This is useful when the SPECIFICATION operator is defined in an extended module.
pub fn resolve_spec_from_config_with_extends(
    config: &Config,
    syntax_tree: &SyntaxNode,
    extended_trees: &[&SyntaxNode],
) -> Result<ResolvedSpec, CheckError> {
    // If explicit INIT/NEXT provided, use them
    if let (Some(init), Some(next)) = (&config.init, &config.next) {
        return Ok(ResolvedSpec {
            init: init.clone(),
            next: next.clone(),
            next_node: None,          // Explicit INIT/NEXT are always operator names
            fairness: Vec::new(),     // No fairness when using explicit INIT/NEXT
            stuttering_allowed: true, // Default to stuttering allowed when using explicit INIT/NEXT
        });
    }

    // Try to extract from SPECIFICATION
    if let Some(spec_name) = &config.specification {
        return resolve_from_specification_multi(spec_name, syntax_tree, extended_trees);
    }

    // No way to determine Init/Next
    if config.init.is_none() {
        return Err(ConfigCheckError::MissingInit.into());
    }
    Err(ConfigCheckError::MissingNext.into())
}
