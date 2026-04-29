// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pooled disk lookup sessions for [`DiskFingerprintSet`].
//!
//! Each session holds a persistent [`File`] handle and a reusable page buffer,
//! eliminating per-lookup `File::open` + `metadata` + `Vec` allocation overhead.
//!
//! Sessions track a reader epoch. After eviction publishes a new disk file
//! (atomic rename), the pool epoch advances and stale sessions lazily reopen
//! their file handle on next checkout.
//!
//! Part of #2371 (S1): matches TLC's `DiskFPSet` per-worker reader pattern.

use std::io::{self, BufReader, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use super::disk_search::{FINGERPRINT_BYTES, PAGE_SIZE};

/// A reusable disk read session: persistent file handle + page buffer.
pub(crate) struct DiskLookupSession {
    reader: BufReader<std::fs::File>,
    buf: Vec<u8>,
    epoch: u64,
}

impl DiskLookupSession {
    /// Open a new session against `disk_path` at the given epoch.
    fn open(disk_path: &Path, epoch: u64) -> io::Result<Self> {
        let file = std::fs::File::open(disk_path)?;
        Ok(Self {
            reader: BufReader::new(file),
            buf: vec![0u8; PAGE_SIZE],
            epoch,
        })
    }

    /// Read one disk page (or aligned tail) into the reusable buffer.
    ///
    /// Returns a slice of the internal buffer containing the page data.
    /// The slice length is always a multiple of `FINGERPRINT_BYTES`.
    pub(crate) fn read_page_exact(&mut self, page: usize, file_len: u64) -> io::Result<&[u8]> {
        let page_offset = (page as u64).checked_mul(PAGE_SIZE as u64).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("disk page index {} overflows byte offset", page),
            )
        })?;

        if page_offset >= file_len {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                format!(
                    "disk page {} starts at byte {} beyond file length {}",
                    page, page_offset, file_len
                ),
            ));
        }

        let expected_u64 = (file_len - page_offset).min(PAGE_SIZE as u64);
        let expected = usize::try_from(expected_u64).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "disk page {} expected byte count {} does not fit in usize",
                    page, expected_u64
                ),
            )
        })?;

        if expected % FINGERPRINT_BYTES != 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "disk page {} has {} bytes, not divisible by {}",
                    page, expected, FINGERPRINT_BYTES
                ),
            ));
        }

        self.reader.seek(SeekFrom::Start(page_offset))?;
        self.reader.read_exact(&mut self.buf[..expected])?;
        Ok(&self.buf[..expected])
    }
}

/// Pool of reusable [`DiskLookupSession`]s.
///
/// Workers check out a session, perform the disk read, and return it.
/// The mutex is only held during checkout/return (not during I/O).
///
/// After eviction publish, `advance_epoch()` increments the pool epoch.
/// Stale sessions (epoch mismatch) lazily reopen their file handle.
pub(crate) struct DiskLookupPool {
    sessions: parking_lot::Mutex<Vec<DiskLookupSession>>,
    epoch: AtomicU64,
    disk_path: PathBuf,
}

impl DiskLookupPool {
    /// Create a new empty pool for the given disk path.
    pub(crate) fn new(disk_path: PathBuf) -> Self {
        Self {
            sessions: parking_lot::Mutex::new(Vec::new()),
            epoch: AtomicU64::new(0),
            disk_path,
        }
    }

    /// Check out a session from the pool.
    ///
    /// Returns a pooled session if available and epoch-current, or opens a new
    /// one. Stale sessions are discarded (file handle points to old file).
    pub(crate) fn checkout(&self) -> io::Result<DiskLookupSession> {
        let current_epoch = self.epoch.load(Ordering::Acquire);

        // Try to reuse a pooled session.
        if let Some(session) = self.sessions.lock().pop() {
            if session.epoch == current_epoch {
                return Ok(session);
            }
            // Stale session — drop it, open fresh.
        }

        DiskLookupSession::open(&self.disk_path, current_epoch)
    }

    /// Return a session to the pool for reuse.
    ///
    /// Stale sessions (epoch mismatch) are silently dropped.
    pub(crate) fn return_session(&self, session: DiskLookupSession) {
        let current_epoch = self.epoch.load(Ordering::Acquire);
        if session.epoch == current_epoch {
            self.sessions.lock().push(session);
        }
        // else: stale, drop it
    }

    /// Advance the pool epoch after eviction publish.
    ///
    /// All currently checked-out sessions with the old epoch will be discarded
    /// on return. Pooled sessions are cleared eagerly.
    pub(crate) fn advance_epoch(&self) {
        self.epoch.fetch_add(1, Ordering::Release);
        // Clear stale pooled sessions so they don't accumulate.
        self.sessions.lock().clear();
    }
}
