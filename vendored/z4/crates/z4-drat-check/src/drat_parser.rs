// Copyright 2026 Andrew Yates
// DRAT proof parser supporting both text and binary formats.

use crate::error::DratParseError;
use crate::literal::Literal;

/// A single proof step: addition or deletion of a clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStep {
    Add(Vec<Literal>),
    Delete(Vec<Literal>),
}

/// Detect whether proof data is in binary or text DRAT format.
///
/// Binary DRAT uses 'a' (0x61) for additions and 'd' (0x64) for deletions,
/// followed by LEB128-encoded literals. Text DRAT uses decimal integers.
///
/// Heuristic: 'a' as first non-whitespace byte is unambiguously binary (text
/// never starts with 'a'). 'd' is ambiguous — text deletions also start with
/// 'd'. Disambiguate by checking the next byte: text has a space after 'd',
/// while binary has LEB128 data (high bit set or small non-space value).
pub fn is_binary_drat(data: &[u8]) -> bool {
    let mut i = 0;
    // Skip leading whitespace
    while i < data.len() {
        if data[i] == b' ' || data[i] == b'\n' || data[i] == b'\r' || data[i] == b'\t' {
            i += 1;
            continue;
        }
        break;
    }
    if i >= data.len() {
        return false;
    }
    // 'a' (0x61) is unambiguously binary — text never starts with 'a'
    if data[i] == 0x61 {
        return true;
    }
    // 'd' (0x64) is ambiguous. In text format, 'd' is always followed by a
    // space (e.g., "d 1 -2 0"). In binary format, 'd' is followed by LEB128
    // data. Check the next byte: if it's a space, it's text; otherwise binary.
    if data[i] == 0x64 {
        if i + 1 < data.len() {
            return data[i + 1] != b' ';
        }
        // 'd' alone at end of file — treat as text (empty deletion line)
        return false;
    }
    false
}

/// Parse a text-format DRAT proof.
///
/// Format:
/// - `lit1 lit2 ... 0` — addition (RUP)
/// - `d lit1 lit2 ... 0` — deletion
pub fn parse_text_drat(data: &[u8]) -> Result<Vec<ProofStep>, DratParseError> {
    let text = std::str::from_utf8(data).map_err(|e| DratParseError::InvalidUtf8 {
        detail: e.to_string(),
    })?;
    let mut steps = Vec::new();

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        let (is_delete, tokens_str) = if let Some(rest) = trimmed.strip_prefix('d') {
            (true, rest.trim_start())
        } else {
            (false, trimmed)
        };
        let mut lits = Vec::new();
        for token in tokens_str.split_whitespace() {
            let val: i32 = token.parse().map_err(|e| DratParseError::InvalidLiteral {
                detail: format!("bad literal '{token}': {e}"),
            })?;
            if val == 0 {
                break;
            }
            lits.push(Literal::from_dimacs(val));
        }
        if is_delete {
            steps.push(ProofStep::Delete(lits));
        } else {
            steps.push(ProofStep::Add(lits));
        }
    }
    Ok(steps)
}

/// Parse a binary-format DRAT proof.
///
/// Binary format:
/// - Byte 'a' (0x61): addition, followed by LEB128 literals, terminated by 0
/// - Byte 'd' (0x64): deletion, followed by LEB128 literals, terminated by 0
///
/// Literal encoding: positive var v → 2*(v+1), negative → 2*(v+1)+1,
/// then LEB128 variable-length encoding.
pub fn parse_binary_drat(data: &[u8]) -> Result<Vec<ProofStep>, DratParseError> {
    let mut steps = Vec::new();
    let mut pos = 0;

    while pos < data.len() {
        let marker = data[pos];
        pos += 1;
        let is_delete = match marker {
            0x61 => false, // 'a'
            0x64 => true,  // 'd'
            _ => {
                return Err(DratParseError::InvalidBinary {
                    offset: pos - 1,
                    detail: format!("unexpected marker byte 0x{marker:02x}"),
                })
            }
        };

        let mut lits = Vec::new();
        loop {
            let (val, new_pos) = read_leb128(data, pos)?;
            pos = new_pos;
            if val == 0 {
                break;
            }
            // Decode: val = 2*(var+1) + sign, where sign=0 means positive, 1 means negative
            let var_plus_one = val >> 1;
            if var_plus_one == 0 {
                return Err(DratParseError::InvalidLiteral {
                    detail: format!("invalid literal encoding: value {val}"),
                });
            }
            let var_idx = var_plus_one - 1;
            let var_i32 = i32::try_from(var_idx).map_err(|_| DratParseError::InvalidLiteral {
                detail: format!("binary DRAT variable {var_idx} exceeds i32 range"),
            })?;
            let dimacs = if val & 1 == 0 {
                var_i32 + 1
            } else {
                -(var_i32 + 1)
            };
            lits.push(Literal::from_dimacs(dimacs));
        }

        if is_delete {
            steps.push(ProofStep::Delete(lits));
        } else {
            steps.push(ProofStep::Add(lits));
        }
    }
    Ok(steps)
}

/// Read a LEB128 unsigned integer from `data` starting at `pos`.
/// Delegates to z4-proof-common.
fn read_leb128(data: &[u8], pos: usize) -> Result<(u32, usize), DratParseError> {
    z4_proof_common::leb128::read_u32(data, pos).map_err(DratParseError::from)
}

/// Parse a DRAT proof, auto-detecting text vs binary format.
pub fn parse_drat(data: &[u8]) -> Result<Vec<ProofStep>, DratParseError> {
    if is_binary_drat(data) {
        parse_binary_drat(data)
    } else {
        parse_text_drat(data)
    }
}

#[cfg(test)]
#[path = "drat_parser_tests.rs"]
mod tests;
