// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn test_embedded_test() {
    assert_snapshot!("embedded", "Just a string");
}
