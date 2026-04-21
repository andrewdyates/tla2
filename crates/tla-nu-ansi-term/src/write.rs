// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use core::fmt;

pub trait AnyWrite {
    type Wstr: ?Sized;
    type Error;

    fn write_fmt(&mut self, fmt: fmt::Arguments) -> Result<(), Self::Error>;

    fn write_str(&mut self, s: &Self::Wstr) -> Result<(), Self::Error>;
}

impl<'a> AnyWrite for dyn fmt::Write + 'a {
    type Wstr = str;
    type Error = fmt::Error;

    fn write_fmt(&mut self, fmt: fmt::Arguments) -> Result<(), Self::Error> {
        fmt::Write::write_fmt(self, fmt)
    }

    fn write_str(&mut self, s: &Self::Wstr) -> Result<(), Self::Error> {
        fmt::Write::write_str(self, s)
    }
}

#[cfg(feature = "std")]
impl<'a> AnyWrite for dyn std::io::Write + 'a {
    type Wstr = [u8];
    type Error = std::io::Error;

    fn write_fmt(&mut self, fmt: fmt::Arguments) -> Result<(), Self::Error> {
        std::io::Write::write_fmt(self, fmt)
    }

    fn write_str(&mut self, s: &Self::Wstr) -> Result<(), Self::Error> {
        std::io::Write::write_all(self, s)
    }
}
