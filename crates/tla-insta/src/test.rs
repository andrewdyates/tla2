// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[test]
fn test_embedded_test() {
    assert_snapshot!("embedded", "Just a string");
}
