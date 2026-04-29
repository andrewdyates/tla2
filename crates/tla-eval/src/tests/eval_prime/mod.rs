// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct unit tests for `eval_prime.rs`.
//!
//! Part of #2960: eval_prime.rs is 499 lines with 5 resolution tiers, 2 unsafe
//! blocks, and multiple bug-fix paths — yet it had zero direct unit tests.
//! These tests cover each tier and the `eval_unchanged` function.

pub(super) use super::*;
pub(super) use crate::cache::{enter_quantifier_hoist_scope, quantifier_hoist_store};
pub(super) use crate::clear_for_test_reset;
pub(super) use rustc_hash::FxHashSet;
pub(super) use std::rc::Rc;
pub(super) use tla_core::ast::{Expr, Substitution};
pub(super) use tla_core::name_intern::{intern_name, NameId};
pub(super) use tla_core::Spanned;

mod call_by_name;
mod fast_paths;
mod instance_subs;
mod next_state_fallbacks;
mod unchanged;
