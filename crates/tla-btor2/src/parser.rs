// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates
// BTOR2 text format parser.
//
// Parses the line-oriented BTOR2 format (Niemetz, Preiner, Wolf, Biere; CAV 2018).
// Each non-comment line defines a node: `<id> <opcode> [<sort>] [<args>...] [<symbol>]`.
//
// Public API:
//   `parse(input)` — parse from a string
//   `parse_file(path)` — parse from a file path
//
// After parsing, all cross-references are validated: every referenced node ID
// must be defined, and every sort reference must point to a `sort` node.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::error::Btor2Error;
use crate::types::{Btor2Line, Btor2Node, Btor2Program, Btor2Sort};

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Parse a BTOR2 source string into a [`Btor2Program`].
///
/// Parses all lines, builds index structures, and validates that every
/// referenced node ID exists and every sort reference points to a `sort` node.
pub fn parse(input: &str) -> Result<Btor2Program, Btor2Error> {
    let mut lines = Vec::new();
    let mut defined_ids: HashMap<i64, usize> = HashMap::new();
    let mut sort_ids: HashSet<i64> = HashSet::new();
    let mut sorts: HashMap<i64, Btor2Sort> = HashMap::new();
    let mut bad_properties = Vec::new();
    let mut constraints = Vec::new();
    let mut fairness = Vec::new();
    let mut justice = Vec::new();
    let mut num_inputs = 0usize;
    let mut num_states = 0usize;

    for (line_idx, raw_line) in input.lines().enumerate() {
        let line_num = line_idx + 1;

        // Strip inline comments: everything from ';' onward is a comment.
        // This handles both full-line comments ("; comment") and inline
        // comments ("2 input 1 ap_clk ; path/to/source.v:42").
        let without_comment = match raw_line.find(';') {
            Some(pos) => &raw_line[..pos],
            None => raw_line,
        };
        let trimmed = without_comment.trim();

        // Skip blank lines (including comment-only lines).
        if trimmed.is_empty() {
            continue;
        }

        let tokens: Vec<&str> = trimmed.split_whitespace().collect();
        if tokens.len() < 2 {
            return Err(Btor2Error::ParseError {
                line: line_num,
                message: format!("expected at least <id> <opcode>, got: {trimmed}"),
            });
        }

        let id: i64 = tokens[0].parse().map_err(|_| Btor2Error::ParseError {
            line: line_num,
            message: format!("invalid node id: {}", tokens[0]),
        })?;

        if id <= 0 {
            return Err(Btor2Error::ParseError {
                line: line_num,
                message: format!("node id must be positive, got: {id}"),
            });
        }

        // Check for duplicate IDs.
        if defined_ids.contains_key(&id) {
            return Err(Btor2Error::DuplicateId {
                line: line_num,
                node_id: id,
            });
        }

        let opcode = tokens[1];
        let btor_line = parse_line(id, opcode, &tokens, line_num)?;

        // Index sorts.
        match &btor_line.node {
            Btor2Node::SortBitVec(w) => {
                sorts.insert(id, Btor2Sort::BitVec(*w));
                sort_ids.insert(id);
            }
            Btor2Node::SortArray(idx_sid, elem_sid) => {
                let idx_sort = sorts.get(idx_sid).ok_or(Btor2Error::InvalidSort {
                    line: line_num,
                    sort_id: *idx_sid,
                })?;
                let elem_sort = sorts.get(elem_sid).ok_or(Btor2Error::InvalidSort {
                    line: line_num,
                    sort_id: *elem_sid,
                })?;
                sorts.insert(
                    id,
                    Btor2Sort::Array {
                        index: Box::new(idx_sort.clone()),
                        element: Box::new(elem_sort.clone()),
                    },
                );
                sort_ids.insert(id);
            }
            _ => {}
        }

        // Index properties.
        match &btor_line.node {
            Btor2Node::Bad(_) => bad_properties.push(id),
            Btor2Node::Constraint(_) => constraints.push(id),
            Btor2Node::Fair(_) => fairness.push(id),
            Btor2Node::Justice(conds) => justice.push(conds.clone()),
            Btor2Node::Input(_, _) => num_inputs += 1,
            Btor2Node::State(_, _) => num_states += 1,
            _ => {}
        }

        defined_ids.insert(id, lines.len());
        lines.push(btor_line);
    }

    let program = Btor2Program {
        lines,
        sorts,
        num_inputs,
        num_states,
        bad_properties,
        constraints,
        fairness,
        justice,
    };

    // Validate all cross-references.
    validate(&program, &defined_ids, &sort_ids)?;

    Ok(program)
}

/// Parse a BTOR2 program from a file path.
///
/// Reads the file contents and delegates to [`parse`].
pub fn parse_file(path: &Path) -> Result<Btor2Program, Btor2Error> {
    let contents = std::fs::read_to_string(path)?;
    parse(&contents)
}

/// Alias for [`parse`] — provided for backward compatibility.
pub fn parse_btor2(input: &str) -> Result<Btor2Program, Btor2Error> {
    parse(input)
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

/// Validate all cross-references in a parsed program.
///
/// Checks that:
/// 1. Every argument node ID (absolute value) references a defined node.
/// 2. Every `sort_id` field references a node that is actually a sort.
fn validate(
    program: &Btor2Program,
    defined_ids: &HashMap<i64, usize>,
    sort_ids: &HashSet<i64>,
) -> Result<(), Btor2Error> {
    for (line_idx, line) in program.lines.iter().enumerate() {
        let line_num = line_idx + 1;

        // Validate argument references: each arg (by absolute value) must be defined.
        for &arg in &line.args {
            let abs_id = arg.unsigned_abs() as i64;
            if !defined_ids.contains_key(&abs_id) {
                return Err(Btor2Error::UndefinedNode {
                    line: line_num,
                    node_id: abs_id,
                });
            }
        }

        // Validate sort_id references: must point to a sort node (except for
        // sort definitions themselves and unsorted nodes like properties).
        let sort_id = line.sort_id;
        if sort_id != 0 && !matches_sort_node(&line.node) {
            if !defined_ids.contains_key(&sort_id) {
                return Err(Btor2Error::UndefinedNode {
                    line: line_num,
                    node_id: sort_id,
                });
            }
            if !sort_ids.contains(&sort_id) {
                return Err(Btor2Error::NotASort {
                    line: line_num,
                    node_id: sort_id,
                });
            }
        }

        // Validate array sort sub-references.
        if let Btor2Node::SortArray(idx_sid, elem_sid) = &line.node {
            if !sort_ids.contains(idx_sid) {
                return Err(Btor2Error::NotASort {
                    line: line_num,
                    node_id: *idx_sid,
                });
            }
            if !sort_ids.contains(elem_sid) {
                return Err(Btor2Error::NotASort {
                    line: line_num,
                    node_id: *elem_sid,
                });
            }
        }
    }

    Ok(())
}

/// Returns `true` if the node is a sort definition (sort_id == self id).
fn matches_sort_node(node: &Btor2Node) -> bool {
    matches!(node, Btor2Node::SortBitVec(_) | Btor2Node::SortArray(_, _))
}

// ---------------------------------------------------------------------------
// Line-level parsing
// ---------------------------------------------------------------------------

/// Parse a single BTOR2 line from its tokens.
fn parse_line(
    id: i64,
    opcode: &str,
    tokens: &[&str],
    line_num: usize,
) -> Result<Btor2Line, Btor2Error> {
    match opcode {
        // -- Sorts -----------------------------------------------------------
        "sort" => parse_sort(id, tokens, line_num),

        // -- Constants -------------------------------------------------------
        "const" => parse_const(id, tokens, line_num),
        "constd" => parse_constd(id, tokens, line_num),
        "consth" => parse_consth(id, tokens, line_num),
        "zero" => parse_nullary_with_sort(id, tokens, line_num, Btor2Node::Zero),
        "one" => parse_nullary_with_sort(id, tokens, line_num, Btor2Node::One),
        "ones" => parse_nullary_with_sort(id, tokens, line_num, Btor2Node::Ones),

        // -- State / Input ---------------------------------------------------
        "state" => parse_state(id, tokens, line_num),
        "input" => parse_input(id, tokens, line_num),

        // -- Init / Next -----------------------------------------------------
        "init" => {
            parse_ternary_sorted(id, tokens, line_num, |sid, a, b| Btor2Node::Init(sid, a, b))
        }
        "next" => {
            parse_ternary_sorted(id, tokens, line_num, |sid, a, b| Btor2Node::Next(sid, a, b))
        }

        // -- Properties ------------------------------------------------------
        "bad" => parse_unary_unsorted(id, tokens, line_num, Btor2Node::Bad),
        "constraint" => parse_unary_unsorted(id, tokens, line_num, Btor2Node::Constraint),
        "fair" => parse_unary_unsorted(id, tokens, line_num, Btor2Node::Fair),
        "justice" => parse_justice(id, tokens, line_num),
        "output" => parse_unary_unsorted(id, tokens, line_num, Btor2Node::Output),

        // -- Unary ops -------------------------------------------------------
        "not" => parse_unary_sorted(id, tokens, line_num, Btor2Node::Not),
        "neg" => parse_unary_sorted(id, tokens, line_num, Btor2Node::Neg),
        "inc" => parse_unary_sorted(id, tokens, line_num, Btor2Node::Inc),
        "dec" => parse_unary_sorted(id, tokens, line_num, Btor2Node::Dec),
        "redand" => parse_unary_sorted(id, tokens, line_num, Btor2Node::Redand),
        "redor" => parse_unary_sorted(id, tokens, line_num, Btor2Node::Redor),
        "redxor" => parse_unary_sorted(id, tokens, line_num, Btor2Node::Redxor),

        // -- Binary ops ------------------------------------------------------
        "add" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Add),
        "sub" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Sub),
        "mul" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Mul),
        "udiv" => parse_binary_sorted(id, tokens, line_num, Btor2Node::UDiv),
        "sdiv" => parse_binary_sorted(id, tokens, line_num, Btor2Node::SDiv),
        "urem" => parse_binary_sorted(id, tokens, line_num, Btor2Node::URem),
        "srem" => parse_binary_sorted(id, tokens, line_num, Btor2Node::SRem),
        "smod" => parse_binary_sorted(id, tokens, line_num, Btor2Node::SMod),
        "and" => parse_binary_sorted(id, tokens, line_num, Btor2Node::And),
        "or" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Or),
        "xor" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Xor),
        "nand" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Nand),
        "nor" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Nor),
        "xnor" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Xnor),
        "sll" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Sll),
        "srl" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Srl),
        "sra" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Sra),
        "rol" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Rol),
        "ror" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Ror),
        "eq" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Eq),
        "neq" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Neq),
        "ugt" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Ugt),
        "ugte" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Ugte),
        "ult" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Ult),
        "ulte" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Ulte),
        "sgt" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Sgt),
        "sgte" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Sgte),
        "slt" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Slt),
        "slte" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Slte),
        "concat" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Concat),
        "iff" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Iff),
        "implies" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Implies),

        // -- Overflow detection ----------------------------------------------
        "saddo" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Saddo),
        "sdivo" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Sdivo),
        "smulo" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Smulo),
        "ssubo" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Ssubo),
        "uaddo" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Uaddo),
        "umulo" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Umulo),
        "usubo" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Usubo),

        // -- Indexed ops -----------------------------------------------------
        "slice" => parse_slice(id, tokens, line_num),
        "uext" => parse_extend(id, tokens, line_num, true),
        "sext" => parse_extend(id, tokens, line_num, false),

        // -- Ternary ops -----------------------------------------------------
        "ite" => parse_ternary(id, tokens, line_num, Btor2Node::Ite),
        "write" => parse_ternary(id, tokens, line_num, Btor2Node::Write),

        // -- Array ops -------------------------------------------------------
        "read" => parse_binary_sorted(id, tokens, line_num, Btor2Node::Read),

        _ => Err(Btor2Error::ParseError {
            line: line_num,
            message: format!("unknown opcode: {opcode}"),
        }),
    }
}

// ---------------------------------------------------------------------------
// Parsing helpers
// ---------------------------------------------------------------------------

fn parse_i64(s: &str, line_num: usize, desc: &str) -> Result<i64, Btor2Error> {
    s.parse().map_err(|_| Btor2Error::ParseError {
        line: line_num,
        message: format!("invalid {desc}: {s}"),
    })
}

fn parse_u32(s: &str, line_num: usize, desc: &str) -> Result<u32, Btor2Error> {
    s.parse().map_err(|_| Btor2Error::ParseError {
        line: line_num,
        message: format!("invalid {desc}: {s}"),
    })
}

fn expect_min_tokens(
    tokens: &[&str],
    min: usize,
    line_num: usize,
    opcode: &str,
) -> Result<(), Btor2Error> {
    if tokens.len() < min {
        return Err(Btor2Error::ParseError {
            line: line_num,
            message: format!(
                "{opcode} requires at least {min} tokens, got {}",
                tokens.len()
            ),
        });
    }
    Ok(())
}

fn parse_sort(id: i64, tokens: &[&str], line_num: usize) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 3, line_num, "sort")?;
    match tokens[2] {
        "bitvec" => {
            expect_min_tokens(tokens, 4, line_num, "sort bitvec")?;
            let width = parse_u32(tokens[3], line_num, "bitvec width")?;
            if width == 0 {
                return Err(Btor2Error::ParseError {
                    line: line_num,
                    message: "bitvec width must be >= 1".to_string(),
                });
            }
            Ok(Btor2Line {
                id,
                sort_id: id,
                node: Btor2Node::SortBitVec(width),
                args: vec![],
            })
        }
        "array" => {
            expect_min_tokens(tokens, 5, line_num, "sort array")?;
            let idx_sid = parse_i64(tokens[3], line_num, "array index sort id")?;
            let elem_sid = parse_i64(tokens[4], line_num, "array element sort id")?;
            Ok(Btor2Line {
                id,
                sort_id: id,
                node: Btor2Node::SortArray(idx_sid, elem_sid),
                args: vec![],
            })
        }
        other => Err(Btor2Error::ParseError {
            line: line_num,
            message: format!("unknown sort kind: {other}"),
        }),
    }
}

fn parse_const(id: i64, tokens: &[&str], line_num: usize) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 4, line_num, "const")?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let value = tokens[3];
    // Validate binary string.
    if !value.chars().all(|c| c == '0' || c == '1') {
        return Err(Btor2Error::ParseError {
            line: line_num,
            message: format!("const value must be binary, got: {value}"),
        });
    }
    Ok(Btor2Line {
        id,
        sort_id,
        node: Btor2Node::Const(value.to_string()),
        args: vec![],
    })
}

fn parse_constd(id: i64, tokens: &[&str], line_num: usize) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 4, line_num, "constd")?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let value = tokens[3];
    // Validate decimal string (may start with `-`).
    let digits = value.strip_prefix('-').unwrap_or(value);
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return Err(Btor2Error::ParseError {
            line: line_num,
            message: format!("constd value must be decimal integer, got: {value}"),
        });
    }
    Ok(Btor2Line {
        id,
        sort_id,
        node: Btor2Node::ConstD(value.to_string()),
        args: vec![],
    })
}

fn parse_consth(id: i64, tokens: &[&str], line_num: usize) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 4, line_num, "consth")?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let value = tokens[3];
    if !value.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(Btor2Error::ParseError {
            line: line_num,
            message: format!("consth value must be hexadecimal, got: {value}"),
        });
    }
    Ok(Btor2Line {
        id,
        sort_id,
        node: Btor2Node::ConstH(value.to_string()),
        args: vec![],
    })
}

fn parse_nullary_with_sort(
    id: i64,
    tokens: &[&str],
    line_num: usize,
    node: Btor2Node,
) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 3, line_num, tokens[1])?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    Ok(Btor2Line {
        id,
        sort_id,
        node,
        args: vec![],
    })
}

fn parse_state(id: i64, tokens: &[&str], line_num: usize) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 3, line_num, "state")?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let symbol = tokens.get(3).map(|s| (*s).to_string());
    Ok(Btor2Line {
        id,
        sort_id,
        node: Btor2Node::State(sort_id, symbol),
        args: vec![],
    })
}

fn parse_input(id: i64, tokens: &[&str], line_num: usize) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 3, line_num, "input")?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let symbol = tokens.get(3).map(|s| (*s).to_string());
    Ok(Btor2Line {
        id,
        sort_id,
        node: Btor2Node::Input(sort_id, symbol),
        args: vec![],
    })
}

/// Parse `<id> <op> <sort> <arg1> <arg2>` (sorted ternary with sort + 2 args).
fn parse_ternary_sorted(
    id: i64,
    tokens: &[&str],
    line_num: usize,
    make_node: fn(i64, i64, i64) -> Btor2Node,
) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 5, line_num, tokens[1])?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let a = parse_i64(tokens[3], line_num, "arg1")?;
    let b = parse_i64(tokens[4], line_num, "arg2")?;
    Ok(Btor2Line {
        id,
        sort_id,
        node: make_node(sort_id, a, b),
        args: vec![a, b],
    })
}

/// Parse `<id> <op> <cond>` (unsorted unary — properties like bad/constraint/fair/output).
fn parse_unary_unsorted(
    id: i64,
    tokens: &[&str],
    line_num: usize,
    make_node: fn(i64) -> Btor2Node,
) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 3, line_num, tokens[1])?;
    let arg = parse_i64(tokens[2], line_num, "arg")?;
    Ok(Btor2Line {
        id,
        sort_id: 0, // Properties have no sort.
        node: make_node(arg),
        args: vec![arg],
    })
}

/// Parse `<id> <op> <sort> <arg>` (sorted unary).
fn parse_unary_sorted(
    id: i64,
    tokens: &[&str],
    line_num: usize,
    node: Btor2Node,
) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 4, line_num, tokens[1])?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let arg = parse_i64(tokens[3], line_num, "arg")?;
    Ok(Btor2Line {
        id,
        sort_id,
        node,
        args: vec![arg],
    })
}

/// Parse `<id> <op> <sort> <arg1> <arg2>` (sorted binary).
fn parse_binary_sorted(
    id: i64,
    tokens: &[&str],
    line_num: usize,
    node: Btor2Node,
) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 5, line_num, tokens[1])?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let a = parse_i64(tokens[3], line_num, "arg1")?;
    let b = parse_i64(tokens[4], line_num, "arg2")?;
    Ok(Btor2Line {
        id,
        sort_id,
        node,
        args: vec![a, b],
    })
}

/// Parse `<id> ite <sort> <cond> <then> <else>` (ternary).
fn parse_ternary(
    id: i64,
    tokens: &[&str],
    line_num: usize,
    node: Btor2Node,
) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 6, line_num, tokens[1])?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let a = parse_i64(tokens[3], line_num, "arg1")?;
    let b = parse_i64(tokens[4], line_num, "arg2")?;
    let c = parse_i64(tokens[5], line_num, "arg3")?;
    Ok(Btor2Line {
        id,
        sort_id,
        node,
        args: vec![a, b, c],
    })
}

/// Parse `<id> slice <sort> <arg> <upper> <lower>`.
fn parse_slice(id: i64, tokens: &[&str], line_num: usize) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 6, line_num, "slice")?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let arg = parse_i64(tokens[3], line_num, "arg")?;
    let upper = parse_u32(tokens[4], line_num, "upper")?;
    let lower = parse_u32(tokens[5], line_num, "lower")?;
    if lower > upper {
        return Err(Btor2Error::ParseError {
            line: line_num,
            message: format!("slice lower ({lower}) > upper ({upper})"),
        });
    }
    Ok(Btor2Line {
        id,
        sort_id,
        node: Btor2Node::Slice(upper, lower),
        args: vec![arg],
    })
}

/// Parse `<id> uext/sext <sort> <arg> <width>`.
fn parse_extend(
    id: i64,
    tokens: &[&str],
    line_num: usize,
    unsigned: bool,
) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 5, line_num, if unsigned { "uext" } else { "sext" })?;
    let sort_id = parse_i64(tokens[2], line_num, "sort id")?;
    let arg = parse_i64(tokens[3], line_num, "arg")?;
    let width = parse_u32(tokens[4], line_num, "extend width")?;
    let node = if unsigned {
        Btor2Node::Uext(width)
    } else {
        Btor2Node::Sext(width)
    };
    Ok(Btor2Line {
        id,
        sort_id,
        node,
        args: vec![arg],
    })
}

/// Parse `<id> justice <n> <cond_1> ... <cond_n>`.
fn parse_justice(id: i64, tokens: &[&str], line_num: usize) -> Result<Btor2Line, Btor2Error> {
    expect_min_tokens(tokens, 3, line_num, "justice")?;
    let n: usize = tokens[2].parse().map_err(|_| Btor2Error::ParseError {
        line: line_num,
        message: format!("invalid justice condition count: {}", tokens[2]),
    })?;
    if tokens.len() < 3 + n {
        return Err(Btor2Error::InvalidArgCount {
            line: line_num,
            op: "justice".to_string(),
            expected: n,
            got: tokens.len() - 3,
        });
    }
    let mut conds = Vec::with_capacity(n);
    for i in 0..n {
        conds.push(parse_i64(tokens[3 + i], line_num, "justice condition")?);
    }
    Ok(Btor2Line {
        id,
        sort_id: 0,
        node: Btor2Node::Justice(conds.clone()),
        args: conds,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_counter() {
        let input = r#"
1 sort bitvec 8
2 zero 1
3 state 1 count
4 init 1 3 2
5 one 1
6 add 1 3 5
7 next 1 3 6
8 ones 1
9 eq 1 3 8
10 bad 9
"#;
        let prog = parse(input).expect("should parse");
        assert_eq!(prog.num_states, 1);
        assert_eq!(prog.num_inputs, 0);
        assert_eq!(prog.bad_properties.len(), 1);
        assert_eq!(prog.bad_properties[0], 10);
        assert!(matches!(prog.sorts[&1], Btor2Sort::BitVec(8)));
    }

    #[test]
    fn test_parse_comments_and_blanks() {
        let input = "; comment\n\n1 sort bitvec 1\n; another comment\n";
        let prog = parse(input).expect("should parse");
        assert_eq!(prog.lines.len(), 1);
    }

    #[test]
    fn test_parse_array_sort() {
        let input = "1 sort bitvec 32\n2 sort bitvec 8\n3 sort array 1 2\n";
        let prog = parse(input).expect("should parse");
        assert!(matches!(prog.sorts[&3], Btor2Sort::Array { .. }));
    }

    #[test]
    fn test_parse_negated_args() {
        let input = "\
1 sort bitvec 1
2 input 1 a
3 input 1 b
4 and 1 -2 -3
";
        let prog = parse(input).expect("should parse");
        let line4 = &prog.lines[3];
        assert_eq!(line4.args, vec![-2, -3]);
    }

    #[test]
    fn test_parse_full_sample_from_spec() {
        // The sample from the task description.
        let input = "\
; Comment
1 sort bitvec 1
2 sort bitvec 8
3 sort bitvec 32
4 sort array 2 3
5 zero 2
6 state 2 v_choosing_0
7 init 2 6 5
8 input 1 clk
9 constd 3 1
10 ite 3 8 9 9
11 add 3 10 9
12 ulte 1 11 9
13 and 1 -8 -12
14 bad 13
15 next 2 6 5
16 read 3 4 5
17 write 4 4 5 9
";
        let prog = parse(input).expect("should parse");
        assert_eq!(prog.lines.len(), 17);
        assert_eq!(prog.bad_properties, vec![14]);
        assert_eq!(prog.num_inputs, 1);
        assert_eq!(prog.num_states, 1);
        assert_eq!(prog.constraints.len(), 0);
    }

    #[test]
    fn test_parse_justice() {
        let input = "\
1 sort bitvec 1
2 input 1 a
3 input 1 b
4 justice 2 2 3
";
        let prog = parse(input).expect("should parse");
        assert_eq!(prog.justice.len(), 1);
        assert_eq!(prog.justice[0], vec![2, 3]);
    }

    #[test]
    fn test_parse_fair_and_output() {
        let input = "\
1 sort bitvec 1
2 input 1 x
3 fair 2
4 output 2
";
        let prog = parse(input).expect("should parse");
        assert_eq!(prog.fairness, vec![3]);
        let out_line = &prog.lines[3];
        assert!(matches!(out_line.node, Btor2Node::Output(2)));
    }

    #[test]
    fn test_parse_constd_negative() {
        let input = "\
1 sort bitvec 8
2 constd 1 -5
";
        let prog = parse(input).expect("should parse");
        assert!(matches!(&prog.lines[1].node, Btor2Node::ConstD(v) if v == "-5"));
    }

    #[test]
    fn test_parse_const_binary_validation() {
        let input = "1 sort bitvec 4\n2 const 1 abcd\n";
        let err = parse(input).unwrap_err();
        assert!(matches!(err, Btor2Error::ParseError { .. }));
    }

    #[test]
    fn test_parse_consth_validation() {
        let input = "1 sort bitvec 8\n2 consth 1 ff\n";
        let prog = parse(input).expect("should parse");
        assert!(matches!(&prog.lines[1].node, Btor2Node::ConstH(v) if v == "ff"));
    }

    #[test]
    fn test_parse_consth_invalid() {
        let input = "1 sort bitvec 8\n2 consth 1 xyz\n";
        let err = parse(input).unwrap_err();
        assert!(matches!(err, Btor2Error::ParseError { .. }));
    }

    #[test]
    fn test_error_duplicate_id() {
        let input = "1 sort bitvec 1\n1 sort bitvec 8\n";
        let err = parse(input).unwrap_err();
        assert!(
            matches!(err, Btor2Error::DuplicateId { node_id: 1, .. }),
            "expected DuplicateId, got: {err}"
        );
    }

    #[test]
    fn test_error_undefined_node() {
        let input = "1 sort bitvec 1\n2 not 1 99\n";
        let err = parse(input).unwrap_err();
        assert!(
            matches!(err, Btor2Error::UndefinedNode { node_id: 99, .. }),
            "expected UndefinedNode(99), got: {err}"
        );
    }

    #[test]
    fn test_error_not_a_sort() {
        // Node 2 is an input, not a sort — using it as a sort_id should fail.
        let input = "1 sort bitvec 1\n2 input 1 x\n3 zero 2\n";
        let err = parse(input).unwrap_err();
        assert!(
            matches!(err, Btor2Error::NotASort { node_id: 2, .. }),
            "expected NotASort(2), got: {err}"
        );
    }

    #[test]
    fn test_error_unknown_opcode() {
        let input = "1 foobar 2\n";
        let err = parse(input).unwrap_err();
        assert!(matches!(err, Btor2Error::ParseError { .. }));
    }

    #[test]
    fn test_error_zero_node_id() {
        let input = "0 sort bitvec 1\n";
        let err = parse(input).unwrap_err();
        assert!(matches!(err, Btor2Error::ParseError { .. }));
    }

    #[test]
    fn test_error_zero_bitvec_width() {
        let input = "1 sort bitvec 0\n";
        let err = parse(input).unwrap_err();
        assert!(matches!(err, Btor2Error::ParseError { .. }));
    }

    #[test]
    fn test_error_slice_bounds() {
        let input = "\
1 sort bitvec 8
2 sort bitvec 4
3 input 1 x
4 slice 2 3 2 5
";
        let err = parse(input).unwrap_err();
        assert!(matches!(err, Btor2Error::ParseError { .. }));
    }

    #[test]
    fn test_parse_all_unary_ops() {
        let ops = ["not", "inc", "dec", "neg", "redand", "redor", "redxor"];
        for op in &ops {
            let input = format!("1 sort bitvec 8\n2 input 1 x\n3 {op} 1 2\n");
            let prog = parse(&input).unwrap_or_else(|e| panic!("failed on {op}: {e}"));
            assert_eq!(prog.lines.len(), 3, "{op} should produce 3 lines");
        }
    }

    #[test]
    fn test_parse_all_binary_ops() {
        let ops = [
            "add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "smod", "and", "or", "xor",
            "nand", "nor", "xnor", "sll", "srl", "sra", "rol", "ror", "eq", "neq", "ugt", "ugte",
            "ult", "ulte", "sgt", "sgte", "slt", "slte", "concat", "iff", "implies", "saddo",
            "sdivo", "smulo", "ssubo", "uaddo", "umulo", "usubo",
        ];
        for op in &ops {
            let input = format!("1 sort bitvec 8\n2 input 1 a\n3 input 1 b\n4 {op} 1 2 3\n");
            let prog = parse(&input).unwrap_or_else(|e| panic!("failed on {op}: {e}"));
            assert_eq!(prog.lines.len(), 4, "{op} should produce 4 lines");
        }
    }

    #[test]
    fn test_parse_slice_and_extend() {
        let input = "\
1 sort bitvec 8
2 sort bitvec 4
3 sort bitvec 16
4 input 1 x
5 slice 2 4 3 0
6 uext 3 4 8
7 sext 3 4 8
";
        let prog = parse(input).expect("should parse");
        assert!(matches!(prog.lines[4].node, Btor2Node::Slice(3, 0)));
        assert!(matches!(prog.lines[5].node, Btor2Node::Uext(8)));
        assert!(matches!(prog.lines[6].node, Btor2Node::Sext(8)));
    }

    #[test]
    fn test_parse_ite() {
        let input = "\
1 sort bitvec 1
2 sort bitvec 8
3 input 1 cond
4 input 2 a
5 input 2 b
6 ite 2 3 4 5
";
        let prog = parse(input).expect("should parse");
        let ite = &prog.lines[5];
        assert!(matches!(ite.node, Btor2Node::Ite));
        assert_eq!(ite.args, vec![3, 4, 5]);
    }

    #[test]
    fn test_parse_array_read_write() {
        let input = "\
1 sort bitvec 8
2 sort bitvec 32
3 sort array 1 2
4 input 3 mem
5 input 1 addr
6 read 2 4 5
7 constd 2 42
8 write 3 4 5 7
";
        let prog = parse(input).expect("should parse");
        let read_line = &prog.lines[5];
        assert!(matches!(read_line.node, Btor2Node::Read));
        assert_eq!(read_line.args, vec![4, 5]);
        let write_line = &prog.lines[7];
        assert!(matches!(write_line.node, Btor2Node::Write));
        assert_eq!(write_line.args, vec![4, 5, 7]);
    }

    #[test]
    fn test_parse_empty_input() {
        let prog = parse("").expect("should parse empty input");
        assert!(prog.lines.is_empty());
    }

    #[test]
    fn test_parse_file_not_found() {
        let result = parse_file(Path::new("/nonexistent/file.btor2"));
        assert!(matches!(result, Err(Btor2Error::Io(_))));
    }

    #[test]
    fn test_error_undefined_sort_in_array() {
        // Array sort references non-existent sort.
        let input = "1 sort bitvec 8\n2 sort array 1 99\n";
        let err = parse(input).unwrap_err();
        assert!(
            matches!(err, Btor2Error::InvalidSort { sort_id: 99, .. }),
            "expected InvalidSort(99), got: {err}"
        );
    }

    #[test]
    fn test_parse_constraint() {
        let input = "\
1 sort bitvec 1
2 input 1 x
3 constraint 2
";
        let prog = parse(input).expect("should parse");
        assert_eq!(prog.constraints, vec![3]);
    }

    #[test]
    fn test_validation_negated_arg_reference() {
        // `-2` should validate against node id 2.
        let input = "\
1 sort bitvec 1
2 input 1 x
3 not 1 -2
";
        let prog = parse(input).expect("negated ref should validate");
        assert_eq!(prog.lines[2].args, vec![-2]);
    }

    #[test]
    fn test_validation_negated_undefined() {
        // `-99` should fail: node 99 is not defined.
        let input = "\
1 sort bitvec 1
2 not 1 -99
";
        let err = parse(input).unwrap_err();
        assert!(
            matches!(err, Btor2Error::UndefinedNode { node_id: 99, .. }),
            "expected UndefinedNode(99), got: {err}"
        );
    }
}
