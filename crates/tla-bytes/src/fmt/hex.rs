// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use core::fmt::{Formatter, LowerHex, Result, UpperHex};

use super::BytesRef;
use crate::{Bytes, BytesMut};

impl LowerHex for BytesRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for &b in self.0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl UpperHex for BytesRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for &b in self.0 {
            write!(f, "{:02X}", b)?;
        }
        Ok(())
    }
}

fmt_impl!(LowerHex, Bytes);
fmt_impl!(LowerHex, BytesMut);
fmt_impl!(UpperHex, Bytes);
fmt_impl!(UpperHex, BytesMut);
