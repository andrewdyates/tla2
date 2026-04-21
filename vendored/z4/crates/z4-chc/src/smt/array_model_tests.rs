// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_array_interp_to_smt_value_preserves_symbolic_entries_6289() {
    let interp = z4_arrays::ArrayInterpretation {
        default: Some("@arr33".to_string()),
        stores: vec![("__au_k0_(_ BitVec 32)".to_string(), "@arr34".to_string())],
        index_sort: None,
        element_sort: None,
    };
    let bv32 = Sort::BitVec(z4_core::BitVecSort { width: 32 });

    assert_eq!(
        SmtContext::array_interp_to_smt_value(&interp, &bv32, &bv32),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Opaque("@arr33".to_string())),
            entries: vec![(
                SmtValue::Opaque("__au_k0".to_string()),
                SmtValue::Opaque("@arr34".to_string()),
            )],
        }
    );
}
