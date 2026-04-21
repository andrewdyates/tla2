// Copyright 2026 Andrew Yates
// LEB128 (Little Endian Base 128) unsigned integer decoder.
// Used by binary DRAT and LRAT proof formats.

use crate::error::ParseError;

/// Read a LEB128-encoded unsigned integer as `u64` from `data` starting at `pos`.
/// Returns `(value, new_pos)`.
pub fn read_u64(data: &[u8], mut pos: usize) -> Result<(u64, usize), ParseError> {
    let start = pos;
    let mut value: u64 = 0;
    let mut shift: u32 = 0;
    loop {
        if pos >= data.len() {
            return Err(ParseError::UnexpectedEof { position: pos });
        }
        let byte = data[pos];
        pos += 1;
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Ok((value, pos));
        }
        shift += 7;
        if shift >= 64 {
            return Err(ParseError::Leb128Overflow { position: start });
        }
    }
}

/// Read a LEB128-encoded unsigned integer as `u32` from `data` starting at `pos`.
/// Returns `(value, new_pos)`.
pub fn read_u32(data: &[u8], mut pos: usize) -> Result<(u32, usize), ParseError> {
    let start = pos;
    let mut value: u32 = 0;
    let mut shift: u32 = 0;
    loop {
        if pos >= data.len() {
            return Err(ParseError::UnexpectedEof { position: pos });
        }
        let byte = data[pos];
        pos += 1;
        value |= u32::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Ok((value, pos));
        }
        shift += 7;
        if shift >= 32 {
            return Err(ParseError::Leb128Overflow { position: start });
        }
    }
}

#[cfg(test)]
#[path = "leb128_tests.rs"]
mod tests;
