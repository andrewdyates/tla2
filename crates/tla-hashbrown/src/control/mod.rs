// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
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
