// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::error::Error;

#[test]
fn should_work() -> Result<(), Box<dyn Error + Send + Sync + 'static>> {
    Ok(())
}
