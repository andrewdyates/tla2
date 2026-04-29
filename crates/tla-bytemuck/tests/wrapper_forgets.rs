// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use bytemuck::TransparentWrapper;

#[repr(transparent)]
struct Wrap(Box<u32>);

// SAFETY: it's #[repr(transparent)]
unsafe impl TransparentWrapper<Box<u32>> for Wrap {}

fn main() {
    let value = Box::new(5);
    // This used to duplicate the wrapped value, creating a double free :(
    Wrap::wrap(value);
}
