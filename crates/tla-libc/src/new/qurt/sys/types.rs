// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Header: `sys/types.h`
//!
//! Note: Basic types are defined at the crate root level for qurt.
//! This module provides sys/types.h specific functions and constants.

use super::super::*;
use crate::prelude::*;

pub type cpu_set_t = c_uint;
