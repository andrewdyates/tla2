// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for checkpoint save/load, value serialization, and binary I/O.

mod binary_corruption;
mod save_load;
mod serialization;
mod unsupported_values;

use super::*;
use num_bigint::BigInt;
use std::sync::Arc;
use tempfile::tempdir;

use crate::value::Value;
