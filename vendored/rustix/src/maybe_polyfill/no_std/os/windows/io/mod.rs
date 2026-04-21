// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod raw;
mod socket;

pub use raw::{AsRawSocket, FromRawSocket, IntoRawSocket, RawSocket};
pub use socket::{AsSocket, BorrowedSocket, OwnedSocket};
