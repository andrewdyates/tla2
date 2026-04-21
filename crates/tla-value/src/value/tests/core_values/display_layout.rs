// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Display formatting and type layout baseline tests.
//!
//! Includes the #3285 compact-value size guard, isolated from constructor
//! and set-op tests to reduce merge pressure on the live throughput lane.

use super::super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_display() {
    assert_eq!(format!("{}", Value::bool(true)), "TRUE");
    assert_eq!(format!("{}", Value::int(42)), "42");
    assert_eq!(format!("{}", Value::string("hi")), "\"hi\"");
    assert_eq!(
        format!("{}", Value::set([Value::int(1), Value::int(2)])),
        "{1, 2}"
    );
    assert_eq!(
        format!("{}", Value::seq([Value::int(1), Value::int(2)])),
        "<<1, 2>>"
    );
}

/// Size probe for #3285 compact-value design: measure the current baseline
/// sizes of Value and its compound subtypes after the #3445 Arc-wrap shrink.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3285_value_type_sizes_baseline() {
    use std::mem::size_of;

    let value_size = size_of::<Value>();
    let sorted_set_size = size_of::<crate::value::SortedSet>();
    let record_value_size = size_of::<crate::value::RecordValue>();
    let record_set_value_size = size_of::<crate::value::RecordSetValue>();
    let tuple_set_value_size = size_of::<crate::value::TupleSetValue>();
    let subset_value_size = size_of::<crate::value::SubsetValue>();
    let func_set_value_size = size_of::<crate::value::FuncSetValue>();
    let set_cup_value_size = size_of::<crate::value::SetCupValue>();
    let set_cap_value_size = size_of::<crate::value::SetCapValue>();
    let set_diff_value_size = size_of::<crate::value::SetDiffValue>();
    let k_subset_value_size = size_of::<crate::value::KSubsetValue>();
    let seq_set_value_size = size_of::<crate::value::SeqSetValue>();
    let union_value_size = size_of::<crate::value::UnionValue>();
    let func_value_size = size_of::<crate::value::FuncValue>();
    let int_interval_func_size = size_of::<crate::value::IntIntervalFunc>();
    let seq_value_size = size_of::<crate::value::SeqValue>();

    println!("=== #3285 Value Type Size Baseline ===");
    println!("Value:            {} bytes", value_size);
    println!("SortedSet:        {} bytes", sorted_set_size);
    println!("RecordValue:      {} bytes", record_value_size);
    println!("RecordSetValue:   {} bytes", record_set_value_size);
    println!("TupleSetValue:    {} bytes", tuple_set_value_size);
    println!("SubsetValue:      {} bytes", subset_value_size);
    println!("FuncSetValue:     {} bytes", func_set_value_size);
    println!("SetCupValue:      {} bytes", set_cup_value_size);
    println!("SetCapValue:      {} bytes", set_cap_value_size);
    println!("SetDiffValue:     {} bytes", set_diff_value_size);
    println!("KSubsetValue:     {} bytes", k_subset_value_size);
    println!("SeqSetValue:      {} bytes", seq_set_value_size);
    println!("UnionValue:       {} bytes", union_value_size);
    println!("FuncValue:        {} bytes", func_value_size);
    println!("IntIntervalFunc:  {} bytes", int_interval_func_size);
    println!("SeqValue:         {} bytes", seq_value_size);

    // Post-#3445 Arc-wrap baseline.
    // Value now stores the width-driving Set / RecordSet / TupleSet variants
    // behind Arc so scalar values no longer pay the 56-byte inline stride.
    assert_eq!(
        value_size, 24,
        "Value size changed from post-#3445 Arc-wrap baseline"
    );
    // SortedSet grew from 48 to 56 when lazy dedup-len cache (AtomicUsize) was
    // added to avoid forcing O(n log n) normalization on len() calls.
    // Still behind Arc in Value::Set(Arc<SortedSet>), so Value size unaffected.
    assert_eq!(
        sorted_set_size, 56,
        "SortedSet size changed from lazy-dedup-len baseline"
    );
    assert_eq!(
        record_value_size, 16,
        "RecordValue size changed from post-FP64-removal baseline"
    );
    // RecordSetValue grew from 24 to 40 when #3792 added check_order: Box<[Arc<str>]> (16 bytes).
    // Still behind Arc in Value::RecordSet(Arc<RecordSetValue>), so Value size unaffected.
    assert_eq!(
        record_set_value_size, 40,
        "RecordSetValue size changed from post-#3792 check_order baseline"
    );
    assert_eq!(
        tuple_set_value_size, 24,
        "TupleSetValue size changed from pre-#3445 Arc-wrap baseline"
    );
    assert_eq!(
        subset_value_size, 8,
        "SubsetValue size changed from pre-#3445 width-driver audit baseline"
    );
    assert_eq!(
        func_set_value_size, 16,
        "FuncSetValue size changed from pre-#3445 width-driver audit baseline"
    );
    assert_eq!(
        set_cup_value_size, 16,
        "SetCupValue size changed from pre-#3445 width-driver audit baseline"
    );
    assert_eq!(
        set_cap_value_size, 16,
        "SetCapValue size changed from pre-#3445 width-driver audit baseline"
    );
    assert_eq!(
        set_diff_value_size, 16,
        "SetDiffValue size changed from pre-#3445 width-driver audit baseline"
    );
    assert_eq!(
        k_subset_value_size, 16,
        "KSubsetValue size changed from pre-#3445 width-driver audit baseline"
    );
    assert_eq!(
        seq_set_value_size, 8,
        "SeqSetValue size changed from pre-#3445 width-driver audit baseline"
    );
    assert_eq!(
        union_value_size, 8,
        "UnionValue size changed from pre-#3445 width-driver audit baseline"
    );
    // Split-array FuncValue (Part of #3337, #3371): domain: Arc<[Value]> (16) +
    // values: Arc<Vec<Value>> (8) + overrides: Option<Box<Vec<...>>> (8) +
    // additive_fp: AtomicU64 (8) + tlc_normalized: OnceLock<Arc<[usize]>> (24) = 64.
    // Overrides field added in #3371 (lazy EXCEPT overlay).
    assert_eq!(
        func_value_size, 64,
        "FuncValue size changed from lazy-overlay baseline"
    );
    assert_eq!(
        int_interval_func_size, 32,
        "IntIntervalFunc size changed from post-FP64-removal baseline"
    );
    assert_eq!(
        seq_value_size, 96,
        "SeqValue size changed from post-FP64-removal baseline"
    );
}
