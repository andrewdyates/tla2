// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source from libpthread <https://github.com/apple-oss-distributions/libpthread/tree/main>

/// Directory: `pthread/`
///
/// Note that this module has a trailing underscore to avoid conflicting with its child `pthread`
/// module.
///
/// <https://github.com/apple-oss-distributions/libpthread/tree/main/include/pthread>
pub(crate) mod pthread_ {
}

pub(crate) mod sys;
