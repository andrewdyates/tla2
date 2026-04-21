// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier instantiation tests - CEGQI, model-based instantiation,
//! deferred instantiations, unknown reasons

use crate::quantifier_manager::QuantifierManager;
use crate::{Executor, SolveResult, UnknownReason};
use z4_frontend::parse;

mod assuming;
mod cegqi;
mod deferred;
mod ematching;
mod refinement;
mod unknown_and_misc;
