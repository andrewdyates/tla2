use core::char;
use core::convert::TryFrom;
use core::fmt;
use core::fmt::Formatter;
use core::fmt::Write as _;
use core::str;

use super::END_ESCAPE;
use super::QUOTE;
use super::START_ESCAPE;

mod code_point;
use code_point::CodePoint;

mod tables;
use tables::UNPRINTABLE;

fn table_contains(table: &[(u32, u32)], code_point: CodePoint) -> bool {
    let code_point = code_point.into();
    table
        .binary_search_by_key(&code_point, |&(x, _)| x)
        .err()
        .map(|index| {
            index
                .checked_sub(1)
                .map(|x| code_point <= table[x].1)
                .unwrap_or(false)
        })
        .unwrap_or(true)
}

fn is_printable(ch: char) -> bool {
    // ASCII is very common, so it should be optimized.
    (' '..='~').contains(&ch)
        || (!ch.is_ascii() && !table_contains(UNPRINTABLE, ch.into()))
}

enum EscapedCodePoint {
    Hex(CodePoint),
    Literal(char),
    Quote(),
    Repeated(char),
    Sequence(&'static str),
}

impl EscapedCodePoint {
    fn format(self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(ch) => return f.write_char(ch),
            Self::Repeated(ch) => {
                for _ in 0..2 {
                    f.write_char(ch)?;
                }
                return Ok(());
            }
            _ => {}
        }

        f.write_char(START_ESCAPE)?;

        if matches!(self, Self::Quote()) {
            f.write_char(QUOTE)?;
        } else {
            f.write_char('~')?;

            match self {
                Self::Hex(code_point) => {
                    write!(f, "u{:x}", u32::from(code_point))?;
                }
                Self::Sequence(sequence) => f.write_str(sequence)?,
                _ => unreachable!(),
            }
        }

        f.write_char(END_ESCAPE)
    }
}

impl From<u8> for EscapedCodePoint {
    fn from(value: u8) -> Self {
        char::from(value).into()
    }
}

impl From<char> for EscapedCodePoint {
    fn from(value: char) -> Self {
        match value {
            '\t' => Self::Sequence("t"),
            '\n' => Self::Sequence("n"),
            '\r' => Self::Sequence("r"),

            QUOTE => Self::Quote(),
            END_ESCAPE | START_ESCAPE => Self::Repeated(value),

            _ if is_printable(value) => Self::Literal(value),
            _ => Self::Hex(value.into()),
        }
    }
}

impl From<CodePoint> for EscapedCodePoint {
    fn from(value: CodePoint) -> Self {
        // Upon error, [value] is known to be a surrogate, so it is
        // unprintable.
        char::try_from(value)
            .map(Into::into)
            .unwrap_or(Self::Hex(value))
    }
}

pub(super) trait Escape {
    fn escape(&self, f: &mut Formatter<'_>) -> fmt::Result;
}

impl Escape for char {
    fn escape(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.encode_utf8(&mut [0; 4]).escape(f)
    }
}

impl Escape for str {
    fn escape(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // [str] can be written more efficiently than multiple [char] values,
        // since it is already encoded as UTF-8 bytes. The [Debug]
        // implementation for [str] uses the same optimization.
        let mut escaped_index = 0;
        macro_rules! push_literal {
            ( $index:expr ) => {
                let index = $index;
                if index != escaped_index {
                    f.write_str(&self[escaped_index..index])?;
                }
            };
        }

        let mut escaped = false;
        for (i, ch) in self.char_indices() {
            if escaped {
                escaped_index = i;
            }

            let code_point = ch.into();
            escaped = !matches!(code_point, EscapedCodePoint::Literal(_));
            if escaped {
                push_literal!(i);
                code_point.format(f)?;
            }
        }
        if !escaped {
            push_literal!(self.len());
        }

        Ok(())
    }
}

impl Escape for [u8] {
    fn escape(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut string = self;
        while !string.is_empty() {
            let mut invalid = &b""[..];
            let valid = str::from_utf8(string).unwrap_or_else(|error| {
                let (valid, string) = string.split_at(error.valid_up_to());

                let invalid_length =
                    error.error_len().unwrap_or_else(|| string.len());
                invalid = &string[..invalid_length];

                // SAFETY: This slice was validated to be UTF-8.
                unsafe { str::from_utf8_unchecked(valid) }
            });

            valid.escape(f)?;
            string = &string[valid.len()..];

            for &byte in invalid {
                EscapedCodePoint::from(byte).format(f)?;
            }
            string = &string[invalid.len()..];
        }
        Ok(())
    }
}

pub(super) fn escape_utf16<I>(iter: I, f: &mut Formatter<'_>) -> fmt::Result
where
    I: IntoIterator<Item = u16>,
{
    for ch in char::decode_utf16(iter) {
        ch.map(EscapedCodePoint::from)
            .unwrap_or_else(|x| CodePoint::from(x).into())
            .format(f)?;
    }
    Ok(())
}
