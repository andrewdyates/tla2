// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_product_sign() {
    assert_eq!(product_sign(&[1, 1]), 1);
    assert_eq!(product_sign(&[1, -1]), -1);
    assert_eq!(product_sign(&[-1, 1]), -1);
    assert_eq!(product_sign(&[-1, -1]), 1);
    assert_eq!(product_sign(&[1, 0]), 0);
    assert_eq!(product_sign(&[0, -1]), 0);
    assert_eq!(product_sign(&[-1, -1, -1]), -1);
    assert_eq!(product_sign(&[-1, -1, 1]), 1);
}
