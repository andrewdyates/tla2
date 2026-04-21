// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Gracefully degrade styled output

mod strip;
mod wincon;

pub use strip::strip_bytes;
pub use strip::strip_str;
pub use strip::StripBytes;
pub use strip::StripBytesIter;
pub use strip::StripStr;
pub use strip::StripStrIter;
pub use strip::StrippedBytes;
pub use strip::StrippedStr;
pub use wincon::WinconBytes;
pub use wincon::WinconBytesIter;
