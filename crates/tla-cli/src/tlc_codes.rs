// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC numeric codes used by the Eclipse Toolbox in `-tool` mode.
//!
//! This is intentionally a small subset, expanded as needed. The values are
//! taken from `tlc2.output.MP` and `tlc2.output.EC` in the upstream TLC codebase.

/// TLC message classes / severities (MP.*).
pub(crate) mod mp {
    pub(crate) const NONE: i32 = 0;
    pub(crate) const ERROR: i32 = 1;
    pub(crate) const TLCBUG: i32 = 2;
    pub(crate) const WARNING: i32 = 3;
    pub(crate) const STATE: i32 = 4;
}

/// TLC message codes (EC.*).
pub(crate) mod ec {
    pub(crate) const GENERAL: i32 = 1000;

    pub(crate) const TLC_INVARIANT_VIOLATED_BEHAVIOR: i32 = 2110;
    pub(crate) const TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR: i32 = 2112;
    pub(crate) const TLC_TEMPORAL_PROPERTY_VIOLATED: i32 = 2116;
    pub(crate) const TLC_DEADLOCK_REACHED: i32 = 2114;

    pub(crate) const TLC_BEHAVIOR_UP_TO_THIS_POINT: i32 = 2121;

    pub(crate) const TLC_STARTING: i32 = 2185;
    pub(crate) const TLC_FINISHED: i32 = 2186;
    pub(crate) const TLC_MODE_MC: i32 = 2187;
    pub(crate) const TLC_COMPUTING_INIT: i32 = 2189;
    pub(crate) const TLC_INIT_GENERATED1: i32 = 2190;
    pub(crate) const TLC_SUCCESS: i32 = 2193;
    pub(crate) const TLC_SEARCH_DEPTH: i32 = 2194;
    pub(crate) const TLC_STATS: i32 = 2199;
    pub(crate) const TLC_PROGRESS_STATS: i32 = 2200;

    pub(crate) const TLC_STATE_PRINT2: i32 = 2217;
    pub(crate) const TLC_SANY_END: i32 = 2219;
    pub(crate) const TLC_SANY_START: i32 = 2220;

    pub(crate) const TLC_VERSION: i32 = 2262;
    pub(crate) const TLC_COUNTER_EXAMPLE: i32 = 2264;
}
