// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[rustversion::nightly(stable)]
struct S;

#[rustversion::any(nightly(stable))]
struct S;

fn main() {}
