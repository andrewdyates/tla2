// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Comparison helper functions for `Value` ordering and equality.

mod cross_type;
mod equality;
mod primitives;
mod same_type;
mod set_like;

pub(super) use cross_type::{cmp_cross_type, eq_cross_type};
pub(super) use equality::eq_same_type;
pub(super) use primitives::type_order;
pub(super) use same_type::cmp_same_type;
