// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod unsync_once_cell;
#[cfg(any(feature = "std", feature = "critical-section"))]
mod sync_once_cell;

mod unsync_lazy;
#[cfg(any(feature = "std", feature = "critical-section"))]
mod sync_lazy;

#[cfg(feature = "race")]
mod race;
#[cfg(all(feature = "race", feature = "alloc"))]
mod race_once_box;
