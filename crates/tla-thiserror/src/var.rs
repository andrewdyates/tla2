// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use core::fmt::{self, Pointer};

pub struct Var<'a, T: ?Sized>(pub &'a T);

impl<'a, T: Pointer + ?Sized> Pointer for Var<'a, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        Pointer::fmt(self.0, formatter)
    }
}
