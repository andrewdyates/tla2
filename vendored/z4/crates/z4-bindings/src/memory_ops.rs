// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Memory read/write operations and allocation for [`MemoryModel`].
//!
//! Extracted from `memory.rs` for code health (#5970).

use crate::expr::Expr;
use crate::memory::{MemoryModel, OBJECT_ID_WIDTH, OFFSET_WIDTH, POINTER_WIDTH};

impl MemoryModel {
    // ===== Memory Operations =====

    /// Read a single byte from memory at the given pointer.
    ///
    /// Returns a BitVec(8) expression representing the byte value.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(8)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn read_byte(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "read_byte ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        self.mem.clone().select(ptr)
    }

    /// Read multiple bytes from memory starting at the given pointer.
    ///
    /// Returns a BitVec expression of width `n * 8` bits in little-endian order.
    /// The first byte (at `ptr`) is in the least significant position.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: n > 0
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(n * 8)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `n` is 0.
    #[must_use]
    pub fn read_bytes(&self, ptr: &Expr, n: usize) -> Expr {
        assert!(n > 0, "read_bytes requires n > 0");
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "read_bytes ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        // Read bytes in little-endian order: byte[0] is LSB
        let mut bytes = Vec::with_capacity(n);
        for i in 0..n {
            let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
            let addr = ptr.clone().bvadd(offset);
            bytes.push(self.read_byte(addr));
        }

        // Concatenate: most significant byte first in concat
        // For little-endian: bytes[n-1] || bytes[n-2] || ... || bytes[0]
        let mut result = bytes
            .pop()
            .expect("bytes vec should have at least one element since n > 0");
        while let Some(byte) = bytes.pop() {
            result = result.concat(byte);
        }
        result
    }

    /// Write a single byte to memory at the given pointer.
    ///
    /// Returns a new MemoryModel with the updated memory state.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: value.sort().is_bitvec() && value.sort().bitvec_width() == Some(8)
    /// ENSURES: result.mem == self.mem.store(ptr, value)
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `value` is not BitVec(8).
    #[must_use]
    pub fn write_byte(self, ptr: Expr, value: Expr) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_byte ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            value.sort().is_bitvec() && value.sort().bitvec_width() == Some(8),
            "write_byte value requires BitVec(8), got {:?}",
            value.sort()
        );

        Self {
            mem: self.mem.store(ptr, value),
            ..self
        }
    }

    /// Write multiple bytes to memory starting at the given pointer.
    ///
    /// Bytes are written in little-endian order: `bytes[0]` goes to `ptr`,
    /// `bytes[1]` goes to `ptr + 1`, etc.
    ///
    /// Returns a new MemoryModel with the updated memory state.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: forall i in 0..bytes.len(): `bytes[i].sort().bitvec_width() == Some(8)`
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or any byte is not BitVec(8).
    #[must_use]
    pub fn write_bytes(self, ptr: &Expr, bytes: Vec<Expr>) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_bytes ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        let mut model = self;
        for (i, byte) in bytes.into_iter().enumerate() {
            assert!(
                byte.sort().is_bitvec() && byte.sort().bitvec_width() == Some(8),
                "write_bytes byte[{}] requires BitVec(8), got {:?}",
                i,
                byte.sort()
            );
            let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
            let addr = ptr.clone().bvadd(offset);
            model = model.write_byte(addr, byte);
        }
        model
    }

    /// Write a value of the given bit-width to memory in little-endian order.
    ///
    /// Extracts bytes from the value and writes them to consecutive addresses.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to write to (BitVec64)
    /// * `value` - Value to write (must have width divisible by 8)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: value.sort().is_bitvec()
    /// REQUIRES: value.sort().bitvec_width().unwrap() % 8 == 0
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or value width is not divisible by 8.
    #[must_use]
    pub fn write_value(self, ptr: &Expr, value: &Expr) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_value ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        let width = value
            .sort()
            .bitvec_width()
            .expect("write_value value requires BitVec sort");
        assert!(
            width.is_multiple_of(8),
            "write_value width must be divisible by 8"
        );

        let n_bytes = (width / 8) as usize;
        let mut bytes = Vec::with_capacity(n_bytes);

        // Extract bytes in little-endian order
        for i in 0..n_bytes {
            let low = (i * 8) as u32;
            let high = low + 7;
            bytes.push(value.clone().extract(high, low));
        }

        self.write_bytes(ptr, bytes)
    }

    // ===== Allocation =====

    /// Allocate a new object of the given size.
    ///
    /// Returns a tuple of:
    /// - Pointer to the new object (with offset = 0)
    /// - Updated MemoryModel with the allocation recorded
    ///
    /// # Arguments
    /// * `size` - Size of the object in bytes (BitVec32)
    ///
    /// REQUIRES: size.sort().is_bitvec() && size.sort().bitvec_width() == Some(32)
    /// REQUIRES: self.next_object_id < u32::MAX (no overflow)
    /// ENSURES: result.0.sort().bitvec_width() == Some(64) (pointer)
    /// ENSURES: pointer_offset(result.0) == 0
    /// ENSURES: `result.1.object_valid[new_object_id] == true`
    /// ENSURES: `result.1.object_size[new_object_id] == size`
    /// ENSURES: result.1.next_object_id == self.next_object_id + 1
    ///
    /// # Panics
    /// - Panics if `size` is not BitVec(32).
    /// - Panics if object ID counter overflows (>4 billion allocations).
    ///   Object ID 0 is reserved for null, so overflow would create aliasing.
    #[must_use]
    pub fn allocate(mut self, size: Expr) -> (Expr, Self) {
        assert!(
            size.sort().is_bitvec() && size.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
            "allocate size requires BitVec(32), got {:?}",
            size.sort()
        );

        let object_id = Expr::bitvec_const(self.next_object_id, OBJECT_ID_WIDTH);
        self.next_object_id = self
            .next_object_id
            .checked_add(1)
            .expect("Object ID overflow: too many allocations (>4 billion)");

        // Update object_valid[object_id] = true
        let new_valid = self.object_valid.store(object_id.clone(), Expr::true_());

        // Update object_size[object_id] = size
        let new_size = self.object_size.store(object_id.clone(), size);

        let ptr = Self::mk_pointer(object_id, Expr::bitvec_const(0u32, OFFSET_WIDTH));

        (
            ptr,
            Self {
                object_valid: new_valid,
                object_size: new_size,
                ..self
            },
        )
    }

    /// Check if a pointer can be validly deallocated.
    ///
    /// Returns a boolean expression that is true if the object is currently
    /// allocated and not yet freed. This should be asserted before calling
    /// `deallocate` to detect double-free errors.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to the object (BitVec64)
    ///
    /// # Returns
    /// Boolean expression: `object_valid[object_id] == true`
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result == self.object_valid[pointer_object(ptr)]
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn dealloc_ok(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "dealloc_ok ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        let object_id = Self::pointer_object(ptr);
        // Object must be currently valid (allocated and not yet freed)
        self.object_valid.clone().select(object_id)
    }

    /// Deallocate an object.
    ///
    /// Marks the object as invalid. Future accesses to this object will fail
    /// the `read_ok`/`write_ok` check.
    ///
    /// Returns a new MemoryModel with the deallocation recorded.
    ///
    /// # Double-Free Detection
    ///
    /// This operation is idempotent: deallocating an already-freed object
    /// simply sets `object_valid[id] = false` again. To detect double-free
    /// errors, callers should assert `dealloc_ok(ptr)` before calling this
    /// method:
    ///
    /// ```rust,no_run
    /// use z4_bindings::{Expr, MemoryModel};
    ///
    /// # let mem: MemoryModel = todo!();
    /// # let ptr: Expr = todo!();
    /// let valid = mem.dealloc_ok(ptr.clone());
    /// // Assert `valid` in verification constraints.
    /// let mem2 = mem.deallocate(ptr);
    /// # drop((valid, mem2));
    /// ```
    ///
    /// See #1034 for design rationale.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to the object to deallocate (BitVec64)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.object_valid[pointer_object(ptr)] == false
    /// ENSURES: result.object_size == self.object_size
    /// ENSURES: result.mem == self.mem
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn deallocate(self, ptr: Expr) -> Self {
        let object_id = Self::pointer_object(ptr);

        // Update object_valid[object_id] = false
        let new_valid = self.object_valid.store(object_id, Expr::false_());

        Self {
            object_valid: new_valid,
            ..self
        }
    }
}
