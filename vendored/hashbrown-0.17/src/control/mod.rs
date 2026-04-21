// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod bitmask;
mod group;
mod tag;

use self::bitmask::BitMask;
pub(crate) use self::{
    bitmask::BitMaskIter,
    group::Group,
    tag::{Tag, TagSliceExt},
};
