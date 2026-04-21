// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/// A simple binary sum type.
///
/// This is occasionally useful in an ad hoc fashion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Either<Left, Right> {
    Left(Left),
    Right(Right),
}
