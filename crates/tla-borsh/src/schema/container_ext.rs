// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use super::{BorshSchemaContainer, Declaration, Definition, Fields};

pub use max_size::Error as SchemaMaxSerializedSizeError;
use max_size::{is_zero_size, ZeroSizeError};
pub use validate::Error as SchemaContainerValidateError;

mod max_size;
mod validate;
