// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// AIGER parser for both ASCII (.aag) and binary (.aig) formats.
//
// Supports the extended HWMCC header: `aig M I L O A [B C J F]`
// where B=bad, C=constraints, J=justice, F=fairness.
//
// Reference: "The AIGER And-Inverter Graph (AIG) Format Version 20071012"
// by Armin Biere, Johannes Kepler University.

use std::path::Path;

use crate::error::AigerError;
use crate::types::*;

// ---------------------------------------------------------------------------
// Header parsing (shared between ASCII and binary)
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct AigerHeader {
    is_binary: bool,
    maxvar: u64,
    num_inputs: u64,
    num_latches: u64,
    num_outputs: u64,
    num_ands: u64,
    num_bad: u64,
    num_constraints: u64,
    num_justice: u64,
    num_fairness: u64,
}

fn parse_header(line: &str) -> Result<AigerHeader, AigerError> {
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.len() < 6 {
        return Err(AigerError::InvalidHeader(
            "header must have at least 6 fields: aag/aig M I L O A".into(),
        ));
    }

    let is_binary = match parts[0] {
        "aag" => false,
        "aig" => true,
        other => {
            return Err(AigerError::InvalidHeader(format!(
                "expected 'aag' or 'aig', got '{other}'"
            )));
        }
    };

    let parse_u64 = |s: &str, name: &str| -> Result<u64, AigerError> {
        s.parse::<u64>()
            .map_err(|_| AigerError::InvalidHeader(format!("invalid {name}: '{s}'")))
    };

    let maxvar = parse_u64(parts[1], "M (maxvar)")?;
    let num_inputs = parse_u64(parts[2], "I (inputs)")?;
    let num_latches = parse_u64(parts[3], "L (latches)")?;
    let num_outputs = parse_u64(parts[4], "O (outputs)")?;
    let num_ands = parse_u64(parts[5], "A (ands)")?;
    let num_bad = if parts.len() > 6 {
        parse_u64(parts[6], "B (bad)")?
    } else {
        0
    };
    let num_constraints = if parts.len() > 7 {
        parse_u64(parts[7], "C (constraints)")?
    } else {
        0
    };
    let num_justice = if parts.len() > 8 {
        parse_u64(parts[8], "J (justice)")?
    } else {
        0
    };
    let num_fairness = if parts.len() > 9 {
        parse_u64(parts[9], "F (fairness)")?
    } else {
        0
    };

    Ok(AigerHeader {
        is_binary,
        maxvar,
        num_inputs,
        num_latches,
        num_outputs,
        num_ands,
        num_bad,
        num_constraints,
        num_justice,
        num_fairness,
    })
}

// ---------------------------------------------------------------------------
// Binary delta encoding
// ---------------------------------------------------------------------------

fn decode_delta(data: &[u8], pos: &mut usize) -> Result<u64, AigerError> {
    let mut result: u64 = 0;
    let mut shift: u32 = 0;
    loop {
        if *pos >= data.len() {
            return Err(AigerError::UnexpectedEof);
        }
        let byte = data[*pos];
        *pos += 1;
        result |= ((byte & 0x7f) as u64) << shift;
        if byte & 0x80 == 0 {
            return Ok(result);
        }
        shift += 7;
        if shift > 63 {
            return Err(AigerError::InvalidHeader("delta encoding overflow".into()));
        }
    }
}

// ---------------------------------------------------------------------------
// Parsing helpers
// ---------------------------------------------------------------------------

fn parse_lit_str(s: &str, line: usize) -> Result<Literal, AigerError> {
    s.trim().parse::<u64>().map_err(|_| AigerError::Parse {
        line,
        message: format!("invalid literal: '{}'", s.trim()),
    })
}

fn parse_symbols(
    text: &str,
    inputs: &mut [AigerSymbol],
    latches: &mut [AigerLatch],
    outputs: &mut [AigerSymbol],
    bad: &mut [AigerSymbol],
    fairness: &mut [AigerSymbol],
    comments: &mut Vec<String>,
) {
    let mut in_comments = false;
    for line in text.lines() {
        let line = line.trim_end();
        if in_comments {
            comments.push(line.to_string());
            continue;
        }
        if line == "c" {
            in_comments = true;
            continue;
        }
        // Symbol table: [ilobf]<pos> <name>
        let (prefix, rest) = if line.len() >= 2 {
            (line.as_bytes()[0], &line[1..])
        } else {
            continue;
        };
        if let Some((pos_str, name)) = rest.split_once(' ') {
            if let Ok(idx) = pos_str.parse::<usize>() {
                match prefix {
                    b'i' if idx < inputs.len() => inputs[idx].name = Some(name.to_string()),
                    b'l' if idx < latches.len() => latches[idx].name = Some(name.to_string()),
                    b'o' if idx < outputs.len() => outputs[idx].name = Some(name.to_string()),
                    b'b' if idx < bad.len() => bad[idx].name = Some(name.to_string()),
                    b'f' if idx < fairness.len() => fairness[idx].name = Some(name.to_string()),
                    _ => {}
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// ASCII parser (.aag)
// ---------------------------------------------------------------------------

/// Parse an AIGER file in ASCII format (.aag).
pub fn parse_aag(source: &str) -> Result<AigerCircuit, AigerError> {
    let all_lines: Vec<&str> = source.lines().collect();
    if all_lines.is_empty() {
        return Err(AigerError::InvalidHeader("empty file".into()));
    }

    let header = parse_header(all_lines[0])?;
    if header.is_binary {
        return Err(AigerError::InvalidHeader(
            "expected ASCII format (aag), got binary (aig)".into(),
        ));
    }

    let mut idx = 1usize; // Current line index (0-based, 0 = header)

    let take_line = |idx: &mut usize| -> Result<&str, AigerError> {
        if *idx >= all_lines.len() {
            return Err(AigerError::Parse {
                line: *idx + 1,
                message: "unexpected end of file".into(),
            });
        }
        let line = all_lines[*idx];
        *idx += 1;
        Ok(line)
    };

    // Inputs
    let mut inputs = Vec::with_capacity(header.num_inputs as usize);
    for _ in 0..header.num_inputs {
        let ln = idx + 1;
        let lit = parse_lit_str(take_line(&mut idx)?, ln)?;
        inputs.push(AigerSymbol { lit, name: None });
    }

    // Latches
    let mut latches = Vec::with_capacity(header.num_latches as usize);
    for _ in 0..header.num_latches {
        let ln = idx + 1;
        let line = take_line(&mut idx)?;
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 2 {
            return Err(AigerError::Parse {
                line: ln,
                message: "latch needs at least 2 fields: lit next".into(),
            });
        }
        let lit = parse_lit_str(parts[0], ln)?;
        let next = parse_lit_str(parts[1], ln)?;
        let reset = if parts.len() > 2 {
            parse_lit_str(parts[2], ln)?
        } else {
            0
        };
        latches.push(AigerLatch {
            lit,
            next,
            reset,
            name: None,
        });
    }

    // Outputs
    let mut outputs = Vec::with_capacity(header.num_outputs as usize);
    for _ in 0..header.num_outputs {
        let ln = idx + 1;
        let lit = parse_lit_str(take_line(&mut idx)?, ln)?;
        outputs.push(AigerSymbol { lit, name: None });
    }

    // Bad properties
    let mut bad = Vec::with_capacity(header.num_bad as usize);
    for _ in 0..header.num_bad {
        let ln = idx + 1;
        let lit = parse_lit_str(take_line(&mut idx)?, ln)?;
        bad.push(AigerSymbol { lit, name: None });
    }

    // Constraints
    let mut constraints = Vec::with_capacity(header.num_constraints as usize);
    for _ in 0..header.num_constraints {
        let ln = idx + 1;
        let lit = parse_lit_str(take_line(&mut idx)?, ln)?;
        constraints.push(AigerSymbol { lit, name: None });
    }

    // Justice
    let mut justice = Vec::with_capacity(header.num_justice as usize);
    for _ in 0..header.num_justice {
        let ln = idx + 1;
        let count = parse_lit_str(take_line(&mut idx)?, ln)? as usize;
        let mut lits = Vec::with_capacity(count);
        for _ in 0..count {
            let ln2 = idx + 1;
            let lit = parse_lit_str(take_line(&mut idx)?, ln2)?;
            lits.push(lit);
        }
        justice.push(AigerJustice { lits });
    }

    // Fairness
    let mut fairness = Vec::with_capacity(header.num_fairness as usize);
    for _ in 0..header.num_fairness {
        let ln = idx + 1;
        let lit = parse_lit_str(take_line(&mut idx)?, ln)?;
        fairness.push(AigerSymbol { lit, name: None });
    }

    // AND gates
    let mut ands = Vec::with_capacity(header.num_ands as usize);
    for _ in 0..header.num_ands {
        let ln = idx + 1;
        let line = take_line(&mut idx)?;
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 3 {
            return Err(AigerError::Parse {
                line: ln,
                message: "AND gate needs 3 fields: lhs rhs0 rhs1".into(),
            });
        }
        let lhs = parse_lit_str(parts[0], ln)?;
        let rhs0 = parse_lit_str(parts[1], ln)?;
        let rhs1 = parse_lit_str(parts[2], ln)?;
        ands.push(AigerAnd { lhs, rhs0, rhs1 });
    }

    // Symbol table and comments from remaining lines
    let mut comments = Vec::new();
    let remaining = all_lines[idx..].join("\n");
    parse_symbols(
        &remaining,
        &mut inputs,
        &mut latches,
        &mut outputs,
        &mut bad,
        &mut fairness,
        &mut comments,
    );

    Ok(AigerCircuit {
        maxvar: header.maxvar,
        inputs,
        latches,
        outputs,
        ands,
        bad,
        constraints,
        justice,
        fairness,
        comments,
    })
}

// ---------------------------------------------------------------------------
// Binary parser (.aig)
// ---------------------------------------------------------------------------

/// Parse an AIGER file in binary format (.aig).
pub fn parse_aig(data: &[u8]) -> Result<AigerCircuit, AigerError> {
    let header_end = data
        .iter()
        .position(|&b| b == b'\n')
        .ok_or(AigerError::InvalidHeader("no newline after header".into()))?;

    let header_str = std::str::from_utf8(&data[..header_end])
        .map_err(|_| AigerError::InvalidHeader("header is not valid UTF-8".into()))?;
    let header = parse_header(header_str)?;
    if !header.is_binary {
        return Err(AigerError::InvalidHeader(
            "expected binary format (aig), got ASCII (aag)".into(),
        ));
    }

    let mut pos = header_end + 1;

    // Read one ASCII line from the byte stream
    let read_line = |data: &[u8], pos: &mut usize| -> Result<String, AigerError> {
        let start = *pos;
        while *pos < data.len() && data[*pos] != b'\n' {
            *pos += 1;
        }
        if *pos >= data.len() && *pos == start {
            return Err(AigerError::UnexpectedEof);
        }
        let line = std::str::from_utf8(&data[start..*pos])
            .map_err(|_| AigerError::Parse {
                line: 0,
                message: "non-UTF-8 in ASCII section".into(),
            })?
            .to_string();
        if *pos < data.len() {
            *pos += 1; // Skip newline
        }
        Ok(line)
    };

    // Inputs are implicit in binary format
    let mut inputs = Vec::with_capacity(header.num_inputs as usize);
    for i in 0..header.num_inputs {
        inputs.push(AigerSymbol {
            lit: aiger_var2lit(i + 1),
            name: None,
        });
    }

    // Latches: one line per latch
    let mut latches = Vec::with_capacity(header.num_latches as usize);
    for i in 0..header.num_latches {
        let line = read_line(data, &mut pos)?;
        let parts: Vec<&str> = line.split_whitespace().collect();
        let next = parse_lit_str(parts[0], 0)?;
        let reset = if parts.len() > 1 {
            parse_lit_str(parts[1], 0)?
        } else {
            0
        };
        let lit = aiger_var2lit(header.num_inputs + i + 1);
        latches.push(AigerLatch {
            lit,
            next,
            reset,
            name: None,
        });
    }

    // Outputs
    let mut outputs = Vec::with_capacity(header.num_outputs as usize);
    for _ in 0..header.num_outputs {
        let line = read_line(data, &mut pos)?;
        outputs.push(AigerSymbol {
            lit: parse_lit_str(&line, 0)?,
            name: None,
        });
    }

    // Bad
    let mut bad = Vec::with_capacity(header.num_bad as usize);
    for _ in 0..header.num_bad {
        let line = read_line(data, &mut pos)?;
        bad.push(AigerSymbol {
            lit: parse_lit_str(&line, 0)?,
            name: None,
        });
    }

    // Constraints
    let mut constraints = Vec::with_capacity(header.num_constraints as usize);
    for _ in 0..header.num_constraints {
        let line = read_line(data, &mut pos)?;
        constraints.push(AigerSymbol {
            lit: parse_lit_str(&line, 0)?,
            name: None,
        });
    }

    // Justice
    let mut justice = Vec::with_capacity(header.num_justice as usize);
    for _ in 0..header.num_justice {
        let count_line = read_line(data, &mut pos)?;
        let count = parse_lit_str(&count_line, 0)? as usize;
        let mut lits = Vec::with_capacity(count);
        for _ in 0..count {
            let jline = read_line(data, &mut pos)?;
            lits.push(parse_lit_str(&jline, 0)?);
        }
        justice.push(AigerJustice { lits });
    }

    // Fairness
    let mut fairness = Vec::with_capacity(header.num_fairness as usize);
    for _ in 0..header.num_fairness {
        let line = read_line(data, &mut pos)?;
        fairness.push(AigerSymbol {
            lit: parse_lit_str(&line, 0)?,
            name: None,
        });
    }

    // AND gates: binary delta encoding
    let mut ands = Vec::with_capacity(header.num_ands as usize);
    for i in 0..header.num_ands {
        let lhs = aiger_var2lit(header.num_inputs + header.num_latches + i + 1);
        let delta0 = decode_delta(data, &mut pos)?;
        let delta1 = decode_delta(data, &mut pos)?;
        let rhs0 = lhs - delta0;
        let rhs1 = rhs0 - delta1;
        ands.push(AigerAnd { lhs, rhs0, rhs1 });
    }

    // Symbol table and comments
    let mut comments = Vec::new();
    if pos < data.len() {
        if let Ok(remaining) = std::str::from_utf8(&data[pos..]) {
            parse_symbols(
                remaining,
                &mut inputs,
                &mut latches,
                &mut outputs,
                &mut bad,
                &mut fairness,
                &mut comments,
            );
        }
    }

    Ok(AigerCircuit {
        maxvar: header.maxvar,
        inputs,
        latches,
        outputs,
        ands,
        bad,
        constraints,
        justice,
        fairness,
        comments,
    })
}

// ---------------------------------------------------------------------------
// Auto-detect format from file
// ---------------------------------------------------------------------------

/// Parse an AIGER file, auto-detecting ASCII (.aag) vs binary (.aig) format.
pub fn parse_file(path: &Path) -> Result<AigerCircuit, AigerError> {
    let data = std::fs::read(path)?;
    if data.len() < 3 {
        return Err(AigerError::InvalidHeader("file too short".into()));
    }
    if data.starts_with(b"aag") {
        let source = std::str::from_utf8(&data)
            .map_err(|_| AigerError::InvalidHeader("ASCII AIGER file is not valid UTF-8".into()))?;
        parse_aag(source)
    } else if data.starts_with(b"aig") {
        parse_aig(&data)
    } else {
        Err(AigerError::InvalidHeader(
            "file does not start with 'aag' or 'aig'".into(),
        ))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_circuit() {
        let c = parse_aag("aag 0 0 0 0 0\n").unwrap();
        assert_eq!(c.maxvar, 0);
        assert!(c.inputs.is_empty());
        assert!(c.ands.is_empty());
    }

    #[test]
    fn test_constant_false() {
        let c = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        assert_eq!(c.outputs[0].lit, 0);
    }

    #[test]
    fn test_constant_true() {
        let c = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        assert_eq!(c.outputs[0].lit, 1);
    }

    #[test]
    fn test_buffer() {
        let c = parse_aag("aag 1 1 0 1 0\n2\n2\n").unwrap();
        assert_eq!(c.inputs[0].lit, 2);
        assert_eq!(c.outputs[0].lit, 2);
    }

    #[test]
    fn test_inverter() {
        let c = parse_aag("aag 1 1 0 1 0\n2\n3\n").unwrap();
        assert_eq!(c.outputs[0].lit, 3);
        assert!(aiger_is_negated(3));
    }

    #[test]
    fn test_and_gate() {
        let c = parse_aag("aag 3 2 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        assert_eq!(c.ands.len(), 1);
        assert_eq!(
            c.ands[0],
            AigerAnd {
                lhs: 6,
                rhs0: 2,
                rhs1: 4
            }
        );
    }

    #[test]
    fn test_half_adder_with_symbols() {
        let src = "aag 7 2 0 2 3\n2\n4\n6\n12\n6 13 15\n12 2 4\n14 3 5\ni0 x\ni1 y\no0 s\no1 c\nc\nhalf adder\n";
        let c = parse_aag(src).unwrap();
        assert_eq!(c.inputs.len(), 2);
        assert_eq!(c.outputs.len(), 2);
        assert_eq!(c.ands.len(), 3);
        assert_eq!(c.inputs[0].name.as_deref(), Some("x"));
        assert_eq!(c.inputs[1].name.as_deref(), Some("y"));
        assert_eq!(c.outputs[0].name.as_deref(), Some("s"));
        assert_eq!(c.outputs[1].name.as_deref(), Some("c"));
        assert_eq!(c.comments, vec!["half adder"]);
    }

    #[test]
    fn test_toggle_flip_flop() {
        let c = parse_aag("aag 1 0 1 2 0\n2 3\n2\n3\n").unwrap();
        assert_eq!(c.latches.len(), 1);
        assert_eq!(c.latches[0].lit, 2);
        assert_eq!(c.latches[0].next, 3);
    }

    #[test]
    fn test_latch_with_reset() {
        let c = parse_aag("aag 1 0 1 1 0\n2 3 1\n2\n").unwrap();
        assert_eq!(c.latches[0].reset, 1);
    }

    #[test]
    fn test_extended_bad() {
        let c = parse_aag("aag 3 2 1 0 0 1 0 0 0\n2\n4\n6 7\n6\n").unwrap();
        assert_eq!(c.bad.len(), 1);
        assert_eq!(c.bad[0].lit, 6);
    }

    #[test]
    fn test_binary_delta_decode() {
        let mut p = 0;
        assert_eq!(decode_delta(&[0x00], &mut p).unwrap(), 0);
        p = 0;
        assert_eq!(decode_delta(&[0x01], &mut p).unwrap(), 1);
        p = 0;
        assert_eq!(decode_delta(&[0x7f], &mut p).unwrap(), 127);
        p = 0;
        assert_eq!(decode_delta(&[0x80, 0x01], &mut p).unwrap(), 128);
        p = 0;
        assert_eq!(decode_delta(&[0x82, 0x02], &mut p).unwrap(), 258);
    }

    #[test]
    fn test_binary_and_gate() {
        // aig 3 2 0 1 1: two inputs, one output, one AND
        // AND: var3(lit6) = lit4 AND lit2, delta0=6-4=2, delta1=4-2=2
        let mut data = Vec::new();
        data.extend_from_slice(b"aig 3 2 0 1 1\n");
        data.extend_from_slice(b"6\n"); // output
        data.push(0x02); // delta0
        data.push(0x02); // delta1
        let c = parse_aig(&data).unwrap();
        assert_eq!(c.inputs.len(), 2);
        assert_eq!(c.ands.len(), 1);
        assert_eq!(
            c.ands[0],
            AigerAnd {
                lhs: 6,
                rhs0: 4,
                rhs1: 2
            }
        );
    }

    #[test]
    fn test_binary_with_latch() {
        let mut data = Vec::new();
        data.extend_from_slice(b"aig 1 0 1 2 0\n");
        data.extend_from_slice(b"3\n"); // latch next=3
        data.extend_from_slice(b"2\n"); // output 0
        data.extend_from_slice(b"3\n"); // output 1
        let c = parse_aig(&data).unwrap();
        assert_eq!(c.latches.len(), 1);
        assert_eq!(c.latches[0].lit, 2);
        assert_eq!(c.latches[0].next, 3);
        assert_eq!(c.outputs.len(), 2);
    }

    #[test]
    fn test_literal_helpers() {
        assert_eq!(aiger_var(6), 3);
        assert!(!aiger_is_negated(2));
        assert!(aiger_is_negated(3));
        assert_eq!(aiger_not(2), 3);
        assert_eq!(aiger_strip(3), 2);
        assert_eq!(aiger_var2lit(3), 6);
    }
}
