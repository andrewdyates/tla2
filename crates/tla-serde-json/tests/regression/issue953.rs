// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use serde_json::Value;

#[test]
fn test() {
    let x1 = serde_json::from_str::<Value>("18446744073709551615.");
    assert!(x1.is_err());
    let x2 = serde_json::from_str::<Value>("18446744073709551616.");
    assert!(x2.is_err());
}
