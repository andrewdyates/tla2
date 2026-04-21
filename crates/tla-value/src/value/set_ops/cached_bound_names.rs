// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;
use tla_core::ast::{BoundPattern, BoundVar};
use tla_core::name_intern::{intern_name, NameId};

#[derive(Clone)]
pub(super) enum CachedBoundNames {
    Simple(Arc<str>, NameId),
    Tuple(Arc<[(Arc<str>, NameId)]>),
}

impl CachedBoundNames {
    pub(super) fn from_bound(bound: &BoundVar) -> Self {
        match &bound.pattern {
            Some(BoundPattern::Tuple(vars)) => {
                let entries: Vec<(Arc<str>, NameId)> = vars
                    .iter()
                    .map(|var| {
                        let raw = var.node.as_str();
                        (Arc::from(raw), intern_name(raw))
                    })
                    .collect();
                Self::Tuple(Arc::from(entries))
            }
            Some(BoundPattern::Var(var)) => {
                let raw = var.node.as_str();
                Self::Simple(Arc::from(raw), intern_name(raw))
            }
            None => {
                let raw = bound.name.node.as_str();
                Self::Simple(Arc::from(raw), intern_name(raw))
            }
        }
    }
}
