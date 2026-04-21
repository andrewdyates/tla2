// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binary SAT decision trace for deterministic replay.
//!
//! The format is append-only and intentionally compact so traces stay small on
//! long runs. A replay session consumes the same event stream and fails at the
//! first divergence.

use std::fs::File;
use std::io::{self, BufReader, BufWriter, Read, Write};

const MAGIC: &[u8; 8] = b"Z4DTRC1\0";
const VERSION: u8 = 1;

const TAG_DECIDE: u8 = 1;
const TAG_PROPAGATE: u8 = 2;
const TAG_CONFLICT: u8 = 3;
const TAG_LEARN: u8 = 4;
const TAG_RESTART: u8 = 5;
const TAG_REDUCE: u8 = 6;
const TAG_INPROCESS: u8 = 7;
const TAG_RESULT: u8 = 8;

/// Final solve outcome recorded in the trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SolveOutcome {
    Sat,
    Unsat,
    Unknown,
}

impl SolveOutcome {
    fn to_u8(self) -> u8 {
        match self {
            Self::Sat => 0,
            Self::Unsat => 1,
            Self::Unknown => 2,
        }
    }

    fn from_u8(raw: u8) -> io::Result<Self> {
        match raw {
            0 => Ok(Self::Sat),
            1 => Ok(Self::Unsat),
            2 => Ok(Self::Unknown),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("unknown solve outcome tag: {raw}"),
            )),
        }
    }
}

/// Compact deterministic replay event stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TraceEvent {
    /// Decision literal chosen by the branching heuristic (DIMACS encoding).
    Decide { lit_dimacs: i32 },
    /// Propagated literal with the reason clause ID.
    Propagate { lit_dimacs: i32, clause_id: u64 },
    /// Conflict clause ID produced by propagation.
    Conflict { clause_id: u64 },
    /// Learned clause insertion with assigned clause ID.
    Learn { clause_id: u64 },
    /// Restart transition.
    Restart,
    /// Clause IDs removed by `reduce_db`.
    Reduce { clause_ids: Vec<u64> },
    /// Inprocessing pass marker (stable numeric code).
    Inprocess { pass_code: u8 },
    /// Final solve outcome.
    Result { outcome: SolveOutcome },
}

impl TraceEvent {
    fn write_to<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            Self::Decide { lit_dimacs } => {
                write_u8(writer, TAG_DECIDE)?;
                write_i32(writer, *lit_dimacs)
            }
            Self::Propagate {
                lit_dimacs,
                clause_id,
            } => {
                write_u8(writer, TAG_PROPAGATE)?;
                write_i32(writer, *lit_dimacs)?;
                write_u64(writer, *clause_id)
            }
            Self::Conflict { clause_id } => {
                write_u8(writer, TAG_CONFLICT)?;
                write_u64(writer, *clause_id)
            }
            Self::Learn { clause_id } => {
                write_u8(writer, TAG_LEARN)?;
                write_u64(writer, *clause_id)
            }
            Self::Restart => write_u8(writer, TAG_RESTART),
            Self::Reduce { clause_ids } => {
                write_u8(writer, TAG_REDUCE)?;
                write_u32(writer, clause_ids.len() as u32)?;
                for &clause_id in clause_ids {
                    write_u64(writer, clause_id)?;
                }
                Ok(())
            }
            Self::Inprocess { pass_code } => {
                write_u8(writer, TAG_INPROCESS)?;
                write_u8(writer, *pass_code)
            }
            Self::Result { outcome } => {
                write_u8(writer, TAG_RESULT)?;
                write_u8(writer, outcome.to_u8())
            }
        }
    }

    fn read_from<R: Read>(reader: &mut R) -> io::Result<Option<Self>> {
        let mut tag = [0u8; 1];
        let read = reader.read(&mut tag)?;
        if read == 0 {
            return Ok(None);
        }

        let event = match tag[0] {
            TAG_DECIDE => Self::Decide {
                lit_dimacs: read_i32(reader)?,
            },
            TAG_PROPAGATE => Self::Propagate {
                lit_dimacs: read_i32(reader)?,
                clause_id: read_u64(reader)?,
            },
            TAG_CONFLICT => Self::Conflict {
                clause_id: read_u64(reader)?,
            },
            TAG_LEARN => Self::Learn {
                clause_id: read_u64(reader)?,
            },
            TAG_RESTART => Self::Restart,
            TAG_REDUCE => {
                let count = read_u32(reader)? as usize;
                let mut clause_ids = Vec::with_capacity(count);
                for _ in 0..count {
                    clause_ids.push(read_u64(reader)?);
                }
                Self::Reduce { clause_ids }
            }
            TAG_INPROCESS => Self::Inprocess {
                pass_code: read_u8(reader)?,
            },
            TAG_RESULT => Self::Result {
                outcome: SolveOutcome::from_u8(read_u8(reader)?)?,
            },
            other => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("unknown event tag: {other}"),
                ))
            }
        };

        Ok(Some(event))
    }
}

/// Write-side binary trace sink.
pub(crate) struct DecisionTraceWriter {
    writer: BufWriter<File>,
    event_count: u64,
}

impl DecisionTraceWriter {
    /// Create and initialize a trace file.
    pub(crate) fn new(path: &str) -> io::Result<Self> {
        let file = File::create(path)?;
        let mut writer = BufWriter::new(file);
        writer.write_all(MAGIC)?;
        write_u8(&mut writer, VERSION)?;
        writer.flush()?;
        Ok(Self {
            writer,
            event_count: 0,
        })
    }

    /// Append one event to the trace.
    pub(crate) fn write_event(&mut self, event: &TraceEvent) -> io::Result<()> {
        event.write_to(&mut self.writer)?;
        self.event_count += 1;
        if self.event_count.is_multiple_of(1024) {
            self.writer.flush()?;
        }
        Ok(())
    }

    /// Flush and return the number of events written.
    pub(crate) fn finish(&mut self) -> io::Result<u64> {
        self.writer.flush()?;
        Ok(self.event_count)
    }
}

/// Read a full binary trace from disk.
pub(crate) fn read_trace(path: &str) -> io::Result<Vec<TraceEvent>> {
    let file = File::open(path)?;
    let mut reader = BufReader::new(file);

    let mut magic = [0u8; 8];
    reader.read_exact(&mut magic)?;
    if &magic != MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "decision trace magic mismatch",
        ));
    }

    let version = read_u8(&mut reader)?;
    if version != VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("unsupported decision trace version: {version}"),
        ));
    }

    let mut events = Vec::new();
    while let Some(event) = TraceEvent::read_from(&mut reader)? {
        events.push(event);
    }
    Ok(events)
}

/// Replay mismatch with exact stream position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReplayMismatch {
    pub(crate) position: usize,
    pub(crate) expected: Option<TraceEvent>,
    pub(crate) actual: Option<TraceEvent>,
}

impl ReplayMismatch {
    /// Human-readable mismatch summary for panic/error messages.
    pub(crate) fn describe(&self) -> String {
        format!(
            "decision trace divergence at event {}: expected {:?}, actual {:?}",
            self.position, self.expected, self.actual
        )
    }
}

/// Replay state that validates the observed event stream.
pub(crate) struct ReplayTrace {
    events: Vec<TraceEvent>,
    cursor: usize,
}

impl ReplayTrace {
    /// Load replay events from a binary trace file.
    pub(crate) fn from_file(path: &str) -> io::Result<Self> {
        Ok(Self {
            events: read_trace(path)?,
            cursor: 0,
        })
    }

    /// Validate the next observed event.
    pub(crate) fn expect(&mut self, event: &TraceEvent) -> Result<(), ReplayMismatch> {
        let expected = self.events.get(self.cursor).cloned();
        match expected {
            Some(exp) if exp == *event => {
                self.cursor += 1;
                Ok(())
            }
            other => Err(ReplayMismatch {
                position: self.cursor,
                expected: other,
                actual: Some(event.clone()),
            }),
        }
    }

    /// Validate that the full replay stream was consumed.
    pub(crate) fn finish(&self) -> Result<(), ReplayMismatch> {
        if self.cursor == self.events.len() {
            Ok(())
        } else {
            Err(ReplayMismatch {
                position: self.cursor,
                expected: self.events.get(self.cursor).cloned(),
                actual: None,
            })
        }
    }
}

/// Resolve recording path from environment.
///
/// Activation:
/// - `Z4_DECISION_TRACE_FILE=<path>`
pub(crate) fn decision_trace_path_from_env() -> Option<String> {
    std::env::var("Z4_DECISION_TRACE_FILE")
        .ok()
        .map(|path| path.trim().to_string())
        .filter(|path| !path.is_empty())
}

/// Resolve replay path from environment.
///
/// Activation:
/// - `Z4_REPLAY_TRACE_FILE=<path>`
pub(crate) fn replay_trace_path_from_env() -> Option<String> {
    std::env::var("Z4_REPLAY_TRACE_FILE")
        .ok()
        .map(|path| path.trim().to_string())
        .filter(|path| !path.is_empty())
}

#[inline]
fn write_u8<W: Write>(writer: &mut W, value: u8) -> io::Result<()> {
    writer.write_all(&[value])
}

#[inline]
fn write_u32<W: Write>(writer: &mut W, value: u32) -> io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}

#[inline]
fn write_u64<W: Write>(writer: &mut W, value: u64) -> io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}

#[inline]
fn write_i32<W: Write>(writer: &mut W, value: i32) -> io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}

#[inline]
fn read_u8<R: Read>(reader: &mut R) -> io::Result<u8> {
    let mut bytes = [0u8; 1];
    reader.read_exact(&mut bytes)?;
    Ok(bytes[0])
}

#[inline]
fn read_u32<R: Read>(reader: &mut R) -> io::Result<u32> {
    let mut bytes = [0u8; 4];
    reader.read_exact(&mut bytes)?;
    Ok(u32::from_le_bytes(bytes))
}

#[inline]
fn read_u64<R: Read>(reader: &mut R) -> io::Result<u64> {
    let mut bytes = [0u8; 8];
    reader.read_exact(&mut bytes)?;
    Ok(u64::from_le_bytes(bytes))
}

#[inline]
fn read_i32<R: Read>(reader: &mut R) -> io::Result<i32> {
    let mut bytes = [0u8; 4];
    reader.read_exact(&mut bytes)?;
    Ok(i32::from_le_bytes(bytes))
}

#[cfg(test)]
#[path = "decision_trace_tests.rs"]
mod tests;
