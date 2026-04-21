use core::ffi::CStr;
use core::fmt;
use core::fmt::Write as _;

use super::Error;
use super::Formatter;
use super::Result;
use super::QUOTE;

#[derive(Debug)]
pub struct Display<T>(T);

impl<T> fmt::Display for Display<&T>
where
    T: Quote + ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_char(QUOTE)?;

        self.0.escape(Formatter::new(f)).map_err(|x| x.0)?;

        f.write_char(QUOTE)
    }
}

/// The trait used to quote strings.
pub trait Quote {
    /// Escapes a string using the format described in the [the module-level
    /// documentation][format], without the surrounding quotes.
    ///
    /// This method is only used to provide new implementations of this trait.
    ///
    /// # Errors
    ///
    /// Similarly to [`Display::fmt`], this method should fail if and only if
    /// the formatter returns an error. Since quoting is an infallible
    /// operation, these failures will only result from inability to write to
    /// the underlying stream.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniquote::Quote;
    ///
    /// struct Strings<'a>(&'a str, &'a str);
    ///
    /// impl Quote for Strings<'_> {
    ///     fn escape(&self, f: &mut uniquote::Formatter<'_>) -> uniquote::Result {
    ///         self.0.escape(f)?;
    ///         ','.escape(f)?;
    ///         self.1.escape(f)
    ///     }
    /// }
    ///
    /// assert_eq!(r#""foo,bar""#, Strings("foo", "bar").quote().to_string());
    /// ```
    ///
    /// [`Display::fmt`]: fmt::Display::fmt
    /// [format]: super#format
    fn escape(&self, f: &mut Formatter<'_>) -> Result;

    /// Quotes a string using the format described in the [the module-level
    /// documentation][format].
    ///
    /// The returned struct will implement [`Display`]. It can be output using
    /// a formatting macro or converted to a string by calling
    /// [`ToString::to_string`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::env;
    /// # use std::io;
    ///
    /// use uniquote::Quote;
    ///
    /// # #[cfg(feature = "std")]
    /// println!("{}", env::current_exe()?.quote());
    /// #
    /// # Ok::<_, io::Error>(())
    /// ```
    ///
    /// [`Display`]: fmt::Display
    /// [format]: super#format
    #[inline]
    #[must_use]
    fn quote(&self) -> Display<&Self> {
        Display(self)
    }
}

macro_rules! r#impl {
    ( $($type:ty),+ ) => {
        $(
            impl Quote for $type {
                #[inline]
                fn escape(&self, f: &mut Formatter<'_>) -> $crate::Result {
                    use super::escape::Escape;

                    Escape::escape(self, &mut f.0).map_err(Error)
                }
            }
        )+
    };
}
r#impl!(char, str, [u8]);

impl<const N: usize> Quote for [u8; N] {
    #[inline]
    fn escape(&self, f: &mut Formatter<'_>) -> Result {
        self[..].escape(f)
    }
}

#[cfg(feature = "alloc")]
macro_rules! impl_with_deref {
    ( $($type:ty),+ ) => {
        $(
            impl $crate::Quote for $type {
                #[inline]
                fn escape(
                    &self,
                    f: &mut $crate::Formatter<'_>
                ) -> $crate::Result {
                    (**self).escape(f)
                }
            }
        )+
    };
}

impl Quote for CStr {
    #[inline]
    fn escape(&self, f: &mut Formatter<'_>) -> Result {
        self.to_bytes().escape(f)
    }
}

#[cfg(feature = "alloc")]
mod alloc {
    use alloc::ffi::CString;
    use alloc::string::String;
    use alloc::vec::Vec;

    impl_with_deref!(CString, String, Vec<u8>);
}

#[cfg(feature = "std")]
mod std {
    #[cfg(any(
        all(target_vendor = "fortanix", target_env = "sgx"),
        target_os = "hermit",
        target_os = "solid_asp3",
        target_os = "wasi",
        unix,
        windows,
    ))]
    mod os_str {
        use std::ffi::OsStr;
        use std::ffi::OsString;
        use std::path::Path;
        use std::path::PathBuf;

        use crate::Formatter;
        use crate::Result;

        use super::super::Quote;

        impl Quote for OsStr {
            #[inline]
            fn escape(&self, f: &mut Formatter<'_>) -> Result {
                #[cfg(windows)]
                {
                    use std::os::windows::ffi::OsStrExt;

                    f.escape_utf16(self.encode_wide())
                }
                #[cfg(not(windows))]
                {
                    #[cfg(all(
                        target_vendor = "fortanix",
                        target_env = "sgx",
                    ))]
                    use std::os::fortanix_sgx as os;
                    #[cfg(target_os = "solid_asp3")]
                    use std::os::solid as os;
                    #[cfg(any(target_os = "hermit", unix))]
                    use std::os::unix as os;
                    #[cfg(target_os = "wasi")]
                    use std::os::wasi as os;

                    use os::ffi::OsStrExt;

                    self.as_bytes().escape(f)
                }
            }
        }

        impl Quote for Path {
            #[inline]
            fn escape(&self, f: &mut Formatter<'_>) -> Result {
                self.as_os_str().escape(f)
            }
        }

        impl_with_deref!(OsString, PathBuf);
    }
}
