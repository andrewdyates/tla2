// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Identifier expression evaluation (`Expr::Ident`).
//!
//! Split into child modules by resolution phase (#3442):
//! - `binding_chain`: BindingChain lookup with dep tracking and lazy thunks
//! - `resolve`: Main eval_ident function (fast path + slow path) and state/env lookup
//! - `instance_subst`: INSTANCE substitution handling with SUBST_CACHE

mod binding_chain;
mod instance_subst;
mod resolve;

pub(crate) use binding_chain::resolve_binding_chain;
pub(super) use resolve::eval_ident;
pub(crate) use resolve::fast_var_idx_lookup;
