// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "rayon")]
pub(crate) mod rayon;
#[cfg(feature = "serde")]
mod serde;
