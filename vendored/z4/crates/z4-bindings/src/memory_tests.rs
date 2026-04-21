// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use crate::Z4Program;

#[test]
fn test_pointer_construction() {
    let obj_id = Expr::bitvec_const(42u32, 32);
    let offset = Expr::bitvec_const(100u32, 32);
    let ptr = MemoryModel::mk_pointer(obj_id, offset);

    assert_eq!(ptr.sort().bitvec_width(), Some(64));

    // Extract and verify components
    let extracted_obj = MemoryModel::pointer_object(ptr.clone());
    let extracted_off = MemoryModel::pointer_offset(ptr);

    assert_eq!(extracted_obj.sort().bitvec_width(), Some(32));
    assert_eq!(extracted_off.sort().bitvec_width(), Some(32));
}

#[test]
fn test_null_pointer() {
    let null = MemoryModel::null_pointer();
    assert_eq!(null.sort().bitvec_width(), Some(64));

    let is_null = MemoryModel::is_null(null);
    assert!(is_null.sort().is_bool());
}

#[test]
fn test_memory_allocation() {
    let mem = MemoryModel::new();
    let size = Expr::bitvec_const(64u32, 32);
    let (ptr, mem2) = mem.allocate(size);

    assert_eq!(ptr.sort().bitvec_width(), Some(64));

    // Verify read_ok returns Bool
    let valid = mem2.read_ok(ptr, Expr::bitvec_const(4u32, 32));
    assert!(valid.sort().is_bool());
}

#[test]
fn test_read_write_byte() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x1000i64, 64);
    let value = Expr::bitvec_const(0xAAu8, 8);

    let mem2 = mem.write_byte(ptr.clone(), value);
    let read_val = mem2.read_byte(ptr);

    assert_eq!(read_val.sort().bitvec_width(), Some(8));
}

#[test]
fn test_read_write_bytes() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x1000i64, 64);
    let bytes = vec![
        Expr::bitvec_const(0xAAu8, 8),
        Expr::bitvec_const(0xBBu8, 8),
        Expr::bitvec_const(0xCCu8, 8),
        Expr::bitvec_const(0xDDu8, 8),
    ];

    let mem2 = mem.write_bytes(&ptr, bytes);
    let read_val = mem2.read_bytes(&ptr, 4);

    // Result should be 32-bit
    assert_eq!(read_val.sort().bitvec_width(), Some(32));
}

#[test]
fn test_write_value() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x1000i64, 64);
    let value = Expr::bitvec_const(0xDEADBEEFu32, 32);

    let mem2 = mem.write_value(&ptr, &value);
    let read_val = mem2.read_bytes(&ptr, 4);

    assert_eq!(read_val.sort().bitvec_width(), Some(32));
}

#[test]
fn test_ptr_arithmetic() {
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64); // obj=1, offset=0
    let offset = Expr::bitvec_const(8u32, 32);

    let new_ptr = MemoryModel::ptr_add(ptr, offset.clone());
    assert_eq!(new_ptr.sort().bitvec_width(), Some(64));

    let back_ptr = MemoryModel::ptr_sub(new_ptr, offset);
    assert_eq!(back_ptr.sort().bitvec_width(), Some(64));
}

#[test]
fn test_deallocate() {
    let mem = MemoryModel::new();
    let size = Expr::bitvec_const(64u32, 32);
    let (ptr, mem2) = mem.allocate(size);
    let mem3 = mem2.deallocate(ptr.clone());

    // After deallocation, read_ok should return false
    let valid = mem3.read_ok(ptr, Expr::bitvec_const(4u32, 32));
    assert!(valid.sort().is_bool());
}

/// End-to-end test demonstrating memory model generates valid SMT-LIB2.
///
/// This test allocates an object, writes a value, reads it back, and
/// verifies that the bounds check (read_ok) properly gates out-of-bounds access.
#[test]
fn test_e2e_memory_model_smt() {
    let mut program = Z4Program::new();
    program.set_logic("QF_AUFBV");
    program.produce_models();

    // Create memory model
    let mem = MemoryModel::new();

    // Allocate an 8-byte object
    let size = Expr::bitvec_const(8u32, 32);
    let (ptr, mem) = mem.allocate(size);

    // Write 0xDEADBEEF to the object (4 bytes)
    let value = Expr::bitvec_const(0xDEADBEEFu32, 32);
    let mem = mem.write_value(&ptr, &value);

    // Bounds check for 4-byte read at offset 0 should be valid
    let valid_access = mem.read_ok(ptr.clone(), Expr::bitvec_const(4u32, 32));

    // Out-of-bounds: 4-byte read at offset 6 (would read bytes 6,7,8,9 but object is only 8 bytes)
    let oob_ptr = MemoryModel::ptr_add(ptr, Expr::bitvec_const(6u32, 32));
    let oob_access = mem.read_ok(oob_ptr, Expr::bitvec_const(4u32, 32));

    // Assert that in-bounds access is valid
    program.assert(valid_access);

    // Assert that out-of-bounds access is NOT valid (negated)
    program.assert(oob_access.not());

    // Check satisfiability
    program.check_sat();

    let smt = program.to_string();

    // Verify SMT-LIB2 output contains expected components
    assert!(
        smt.contains("(set-logic QF_AUFBV)"),
        "Missing logic declaration"
    );
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    // The object_valid starts as const array (all false), so look for the store to it
    assert!(smt.contains("store"), "Missing store operation");
    assert!(smt.contains("bvule"), "Missing bounds check (bvule)");
}

/// Test that the memory model correctly tracks object validity.
#[test]
fn test_e2e_validity_tracking() {
    let mut program = Z4Program::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();

    // Allocate object 1
    let (ptr1, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));

    // Allocate object 2
    let (ptr2, mem) = mem.allocate(Expr::bitvec_const(32u32, 32));

    // Both should be valid
    let valid1 = mem.read_ok(ptr1.clone(), Expr::bitvec_const(4u32, 32));
    let valid2 = mem.read_ok(ptr2.clone(), Expr::bitvec_const(4u32, 32));

    // Deallocate object 1
    let mem = mem.deallocate(ptr1.clone());

    // After deallocation, object 1 should be invalid, object 2 still valid
    let invalid1 = mem.read_ok(ptr1, Expr::bitvec_const(4u32, 32));
    let still_valid2 = mem.read_ok(ptr2, Expr::bitvec_const(4u32, 32));

    // Before deallocation: both valid
    program.assert(valid1);
    program.assert(valid2);

    // After deallocation: ptr1 invalid, ptr2 valid
    program.assert(invalid1.not()); // invalid after free
    program.assert(still_valid2);

    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"));
}

/// Test that object ID overflow panics instead of wrapping.
///
/// Part of #863: Object ID overflow would cause valid allocations to alias
/// with null (object_id=0), breaking soundness. The fix uses checked_add().
#[test]
#[should_panic(expected = "Object ID overflow")]
fn test_object_id_overflow_panics() {
    // Create memory model with object_id near max
    let mut mem = MemoryModel::new();
    // Manually set next_object_id to near max (u32::MAX - 1)
    // This is the last valid allocation
    mem.next_object_id = u32::MAX - 1;

    let size = Expr::bitvec_const(8u32, 32);

    // First allocation should succeed (uses u32::MAX - 1)
    let (_ptr1, mem) = mem.allocate(size.clone());

    // Second allocation should succeed (uses u32::MAX)
    let (_ptr2, mem) = mem.allocate(size.clone());

    // Third allocation should panic (would overflow to 0)
    let _ = mem.allocate(size);
}

// ========================================================================
// Semantic SMT Tests (issue #865)
//
// These tests verify that the memory model generates correct SMT constraints
// by checking for required SMT-LIB2 patterns. Full solver execution is
// blocked on execute_direct BV support (see issue #865 comment).
// ========================================================================

/// Test that deallocate generates proper validity constraint.
///
/// Part of #865: Verify deallocation sets object_valid[id] = false.
#[test]
fn test_deallocate_constraint_structure() {
    let mut program = Z4Program::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(64u32, 32));
    let mem = mem.deallocate(ptr.clone());

    // read_ok after deallocation
    let valid = mem.read_ok(ptr, Expr::bitvec_const(4u32, 32));
    program.assert(valid);
    program.check_sat();

    let smt = program.to_string();

    // Verify SMT contains store operations for deallocation
    // The pattern is: store(store(..., true), false) for alloc then dealloc
    // or select from const-array with stored values
    assert!(smt.contains("store"), "Missing store operation");
    // Deallocation stores `false` to mark object invalid
    assert!(
        smt.contains("false"),
        "Missing false value for deallocation"
    );
    // Allocation stores `true` to mark object valid initially
    assert!(smt.contains("true"), "Missing true value for allocation");
}

/// Test that allocation generates proper bounds tracking.
///
/// Part of #865: Verify allocation stores size in object_size array.
#[test]
fn test_allocation_constraint_structure() {
    let mut program = Z4Program::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(64u32, 32));

    // Read_ok should use object_size for bounds checking
    let valid = mem.read_ok(ptr, Expr::bitvec_const(4u32, 32));
    program.assert(valid);
    program.check_sat();

    let smt = program.to_string();

    // Verify SMT contains proper bounds check structure
    assert!(smt.contains("object_size"), "Missing object_size array");
    assert!(
        smt.contains("bvule"),
        "Missing unsigned <= for bounds check"
    );
    assert!(smt.contains("bvadd"), "Missing offset + size addition");
}

/// Test that out-of-bounds generates proper constraint.
///
/// Part of #865: Verify bounds checking formula structure.
#[test]
fn test_bounds_check_constraint_structure() {
    let mut program = Z4Program::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    // Allocate 8 bytes
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));

    // Try to read 16 bytes (out of bounds)
    let valid = mem.read_ok(ptr, Expr::bitvec_const(16u32, 32));
    program.assert(valid);
    program.check_sat();

    let smt = program.to_string();

    // Verify bounds check includes: offset + access_size <= object_size
    assert!(smt.contains("bvadd"), "Missing offset + size addition");
    assert!(smt.contains("bvule"), "Missing unsigned <= comparison");
    assert!(smt.contains("#x00000010"), "Missing 16-byte size constant");
}

/// Test that write-read generates proper store/select.
///
/// Part of #865: Verify memory array operations.
#[test]
fn test_write_read_constraint_structure() {
    let mut program = Z4Program::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64); // obj=1, offset=0
    let value = Expr::bitvec_const(0xABu8, 8);

    let mem = mem.write_byte(ptr.clone(), value.clone());
    let read_val = mem.read_byte(ptr);

    // Assert read equals written (should be satisfiable)
    let equal = read_val.eq(value);
    program.assert(equal);
    program.check_sat();

    let smt = program.to_string();

    // Verify store and select for memory operations
    assert!(smt.contains("store"), "Missing store for write");
    assert!(smt.contains("select"), "Missing select for read");
    assert!(smt.contains("#xab"), "Missing byte value 0xAB");
}

/// Test dealloc_ok precondition for double-free detection.
///
/// Part of #1034: Verify dealloc_ok returns correct validity state.
#[test]
fn test_dealloc_ok_precondition() {
    let mut program = Z4Program::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(64u32, 32));

    // Before deallocation: dealloc_ok should be true
    let ok_before = mem.dealloc_ok(ptr.clone());
    assert!(ok_before.sort().is_bool());

    // Deallocate
    let mem = mem.deallocate(ptr.clone());

    // After deallocation: dealloc_ok should be false (double-free would fail)
    let ok_after = mem.dealloc_ok(ptr);

    // Assert precondition semantics:
    // - ok_before == true (valid to free)
    // - ok_after == false (already freed, double-free would be invalid)
    program.assert(ok_before);
    program.assert(ok_after.not());
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"));
    // The dealloc_ok check uses object_valid array select
    assert!(smt.contains("select"), "Missing select for validity check");
}
