// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/* Copyright 2016 The encode_unicode Developers
 *
 * Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
 * http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
 * http://opensource.org/licenses/MIT>, at your option. This file may not be
 * copied, modified, or distributed except according to those terms.
 */

/*!
Miscellaneous UTF-8 and UTF-16 types and methods.

# Optional features:
* `#![no_std]`-mode: There are a few differences:
  * `Error` doesn't exist, but `description()` is made available as an inherent impl.
  * `Extend`/`FromIterator`-implementations for `String`/`Vec<u8>`/`Vec<u16>` are missing.
  * There is no `io`, so `Utf8Iterator` and `Utf8CharSplitter` doesn't implement `Read`.

  This feature is enabled by setting `default-features=false` in `Cargo.toml`:
  `encode_unicode = {version="0.3.4", default-features=false}`
* Integration with the [ascii](https://tomprogrammer.github.io/rust-ascii/ascii/index.html) crate:
  Convert `Utf8Char` and `Utf16Char` to and from
  [ascii::`AsciiChar`](https://tomprogrammer.github.io/rust-ascii/ascii/enum.AsciiChar.html).

The minimum supported version of Rust is 1.15,
older versions might work now but can break with a minor update.

[crates.io page](https://crates.io/crates/encode_unicode)
[github repository](https://github.com/tormol/encode_unicode)

*/

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
// either `cargo clippy` doesn't see theese, or I get a warning when I build.
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]
#![cfg_attr(feature = "clippy", allow(derive_hash_xor_eq))] // tested
#![cfg_attr(feature = "clippy", allow(len_without_is_empty))] // UtfxChar is never empty
#![cfg_attr(feature = "clippy", allow(match_same_arms))] // looks better IMO
#![cfg_attr(feature = "clippy", allow(needless_return))] // `foo.bar(); foo` looks unfinished
#![cfg_attr(feature = "clippy", allow(redundant_closure))] // keep it explicit
#![cfg_attr(feature = "clippy", allow(redundant_closure_call))] // not redundant in macros
#![cfg_attr(feature = "clippy", allow(cast_lossless))] // too much noise (and too verbose)
                                                       // precedence: I prefer spaces to parentheses, but it's nice to recheck.

mod decoding_iterators;
mod errors;
mod traits;
mod utf16_char;
mod utf16_iterators;
mod utf8_char;
mod utf8_iterators;

pub use traits::{CharExt, IterExt, SliceExt, StrExt, U16UtfExt, U8UtfExt};
pub use utf16_char::Utf16Char;
pub use utf16_iterators::{iter_units, Utf16Iterator};
pub use utf8_char::Utf8Char;
pub use utf8_iterators::{iter_bytes, Utf8Iterator};

pub mod error {
    // keeping the public interface in one file
    //! Errors returned by various conversion methods in this crate.
    pub use errors::Utf16PairError;
    pub use errors::{EmptyStrError, FromStrError};
    pub use errors::{InvalidCodepoint, InvalidUtf8};
    pub use errors::{InvalidUtf16Array, InvalidUtf16Tuple, InvalidUtf8Array};
    pub use errors::{InvalidUtf16FirstUnit, InvalidUtf8FirstByte};
    pub use errors::{InvalidUtf16Slice, InvalidUtf8Slice};
}

pub mod iterator {
    //! Iterator types that you should rarely need to name
    pub use decoding_iterators::{Utf16CharDecoder, Utf16CharMerger};
    pub use decoding_iterators::{Utf8CharDecoder, Utf8CharMerger};
    pub use utf16_iterators::{Utf16CharIndices, Utf16CharSplitter, Utf16Chars, Utf16Iterator};
    pub use utf8_iterators::{Utf8CharIndices, Utf8CharSplitter, Utf8Chars, Utf8Iterator};
}
