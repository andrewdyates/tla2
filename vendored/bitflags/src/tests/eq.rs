// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn cases() {
    assert_eq!(TestFlags::empty(), TestFlags::empty());
    assert_eq!(TestFlags::all(), TestFlags::all());

    assert!(TestFlags::from_bits_retain(1) < TestFlags::from_bits_retain(2));
    assert!(TestFlags::from_bits_retain(2) > TestFlags::from_bits_retain(1));
}
