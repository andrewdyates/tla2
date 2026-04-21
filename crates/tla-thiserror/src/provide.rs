// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use core::error::{Error, Request};

#[doc(hidden)]
pub trait ThiserrorProvide: Sealed {
    fn thiserror_provide<'a>(&'a self, request: &mut Request<'a>);
}

impl<T> ThiserrorProvide for T
where
    T: Error + ?Sized,
{
    #[inline]
    fn thiserror_provide<'a>(&'a self, request: &mut Request<'a>) {
        self.provide(request);
    }
}

#[doc(hidden)]
pub trait Sealed {}
impl<T: Error + ?Sized> Sealed for T {}
