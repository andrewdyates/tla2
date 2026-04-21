use core::char::CharTryFromError;
use core::char::DecodeUtf16Error;
use core::convert::TryFrom;
use core::convert::TryInto;

#[derive(Clone, Copy)]
pub(super) struct CodePoint(u32);

impl From<char> for CodePoint {
    fn from(value: char) -> Self {
        Self(value.into())
    }
}

impl From<DecodeUtf16Error> for CodePoint {
    fn from(value: DecodeUtf16Error) -> Self {
        Self(value.unpaired_surrogate().into())
    }
}

impl From<CodePoint> for u32 {
    fn from(value: CodePoint) -> Self {
        value.0
    }
}

impl TryFrom<CodePoint> for char {
    type Error = CharTryFromError;

    fn try_from(value: CodePoint) -> Result<Self, Self::Error> {
        value.0.try_into()
    }
}
