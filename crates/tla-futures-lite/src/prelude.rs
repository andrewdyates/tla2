// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Traits [`Future`], [`Stream`], [`AsyncRead`], [`AsyncWrite`], [`AsyncBufRead`],
//! [`AsyncSeek`], and their extensions.
//!
//! # Examples
//!
//! ```
//! use futures_lite::prelude::*;
//! ```

#[doc(no_inline)]
pub use crate::{
    future::{Future, FutureExt as _},
    stream::{Stream, StreamExt as _},
};

#[cfg(feature = "std")]
#[doc(no_inline)]
pub use crate::{
    io::{AsyncBufRead, AsyncBufReadExt as _},
    io::{AsyncRead, AsyncReadExt as _},
    io::{AsyncSeek, AsyncSeekExt as _},
    io::{AsyncWrite, AsyncWriteExt as _},
};
