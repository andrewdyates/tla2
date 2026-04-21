// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Implementation for Fuchsia Zircon
use crate::Error;
use core::mem::MaybeUninit;

#[link(name = "zircon")]
extern "C" {
    fn zx_cprng_draw(buffer: *mut u8, length: usize);
}

pub fn getrandom_inner(dest: &mut [MaybeUninit<u8>]) -> Result<(), Error> {
    unsafe { zx_cprng_draw(dest.as_mut_ptr() as *mut u8, dest.len()) }
    Ok(())
}
