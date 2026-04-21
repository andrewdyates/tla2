// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! This directory maps to `bionic/libc/include` in the Android source.
//!
//! <https://cs.android.com/android/platform/superproject/main/+/main:bionic/libc/include/>

pub(crate) mod pthread;
pub(crate) mod sys;
pub(crate) mod unistd;
