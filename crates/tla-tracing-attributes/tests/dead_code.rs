// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use tracing_attributes::instrument;

#[deny(unfulfilled_lint_expectations)]
#[expect(dead_code)]
#[instrument]
fn unused() {}

#[expect(dead_code)]
#[instrument]
async fn unused_async() {}
