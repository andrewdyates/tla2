// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use displaydoc::Display;

#[derive(Display)]
enum EmptyInside {}

static_assertions::assert_impl_all!(EmptyInside: core::fmt::Display);
