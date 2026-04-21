use core::fmt;
use core::fmt::Display;
use core::mem;
use core::result;

use super::escape;

/// The error type returned by [`Quote::escape`].
///
/// This type is used similarly to [`fmt::Error`] in the standard library.
///
/// [`Quote::escape`]: super::Quote::escape
#[derive(Debug, Eq, PartialEq)]
pub struct Error(pub(super) fmt::Error);

impl Display for Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// The type returned by [`Quote::escape`].
///
/// This type is used similarly to [`fmt::Result`] in the standard library.
///
/// [`Quote::escape`]: super::Quote::escape
pub type Result = result::Result<(), Error>;

/// The type passed between calls to [`Quote::escape`].
///
/// All methods of this struct are defined to ensure that strings are quoted
/// uniformly. However, it is usually sufficient to pass this struct to the
/// [`Quote::escape`] implementation of another type.
///
/// # Safety
///
/// Although this type is annotated with `#[repr(transparent)]`, the inner
/// representation is not stable. Transmuting between this type and any other
/// causes immediate undefined behavior.
///
/// [`Quote::escape`]: super::Quote::escape
#[repr(transparent)]
pub struct Formatter<'a>(pub(super) fmt::Formatter<'a>);

impl<'a> Formatter<'a> {
    pub(super) fn new<'b>(f: &'b mut fmt::Formatter<'a>) -> &'b mut Self {
        // SAFETY: This struct has a layout that makes this operation safe.
        unsafe { mem::transmute(f) }
    }

    /// Provides an implementation of [`Quote::escape`] for a UTF-16 string
    /// iterator.
    ///
    /// The iterator does not need to contain valid UTF-16, since invalid
    /// sequences will be escaped.
    ///
    /// [`Quote::escape`]: super::Quote::escape
    #[inline]
    pub fn escape_utf16<I>(&mut self, iter: I) -> Result
    where
        I: IntoIterator<Item = u16>,
    {
        escape::escape_utf16(iter, &mut self.0).map_err(Error)
    }
}

#[cfg(feature = "std")]
mod std {
    use std::error;

    use super::Error;

    impl error::Error for Error {}
}
