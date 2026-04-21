// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#![cfg(feature = "arbitrary_precision")]

#[test]
fn test() {
    let float = 5.55f32;
    let value = serde_json::to_value(float).unwrap();
    let json = serde_json::to_string(&value).unwrap();

    // If the f32 were cast to f64 by Value before serialization, then this
    // would incorrectly serialize as 5.550000190734863.
    assert_eq!(json, "5.55");
}
