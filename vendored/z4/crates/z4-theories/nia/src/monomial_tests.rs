// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use z4_core::term::TermId;

#[test]
fn test_monomial_binary() {
    let x = TermId(1);
    let y = TermId(2);
    let aux = TermId(100);
    let mon = Monomial::new(vec![x, y], aux);

    assert!(mon.is_binary());
    assert!(!mon.is_square());
    assert_eq!(mon.x(), Some(x));
    assert_eq!(mon.y(), Some(y));
}

#[test]
fn test_monomial_square() {
    let x = TermId(1);
    let aux = TermId(100);
    let mon = Monomial::new(vec![x, x], aux);

    assert!(mon.is_binary());
    assert!(mon.is_square());
    assert_eq!(mon.x(), Some(x));
    assert_eq!(mon.y(), Some(x));
}
