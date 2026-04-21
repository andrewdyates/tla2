// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{chc_sort_to_core, core_sort_to_chc_lossy, core_sort_to_chc_strict};
use crate::expr::ChcSort;
use z4_core::Sort;

#[test]
fn lossy_core_sort_conversion_preserves_legacy_fallbacks() {
    assert_eq!(
        core_sort_to_chc_lossy(&Sort::String),
        ChcSort::Uninterpreted("String".to_string())
    );
    assert_eq!(
        core_sort_to_chc_lossy(&Sort::FloatingPoint(8, 24)),
        ChcSort::Uninterpreted("FloatingPoint_8_24".to_string())
    );
}

#[test]
fn strict_core_sort_conversion_rejects_unsupported_sorts() {
    assert_eq!(core_sort_to_chc_strict(&Sort::String), None);
    assert_eq!(
        core_sort_to_chc_strict(&Sort::Uninterpreted("U".to_string())),
        None
    );
}

#[test]
fn chc_to_core_roundtrip_on_supported_sorts() {
    let sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::BitVec(8)));
    assert_eq!(core_sort_to_chc_lossy(&chc_sort_to_core(&sort)), sort);
}
