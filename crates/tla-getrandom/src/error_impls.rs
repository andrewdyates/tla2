// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

extern crate std;

use crate::Error;
use std::io;

impl From<Error> for io::Error {
    fn from(err: Error) -> Self {
        match err.raw_os_error() {
            Some(errno) => io::Error::from_raw_os_error(errno),
            None => io::Error::new(io::ErrorKind::Other, err),
        }
    }
}

impl std::error::Error for Error {}
