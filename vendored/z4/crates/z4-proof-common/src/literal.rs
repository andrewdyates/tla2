// Copyright 2026 Andrew Yates
// Standalone literal/variable types for SAT proof checkers.
// Encoding: positive = 2*var, negative = 2*var + 1. Zero-indexed internally.

/// A variable identifier (0-indexed internally).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable(u32);

impl Variable {
    /// Create a new variable from a raw 0-indexed identifier.
    #[inline]
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw 0-indexed identifier.
    #[inline]
    pub fn id(self) -> u32 {
        self.0
    }

    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A literal (variable with polarity).
///
/// Encoded as: positive = 2*var, negative = 2*var + 1.
/// This compact encoding allows direct indexing into watch/assignment arrays.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Literal(u32);

impl Literal {
    /// Maximum variable index that can be represented without overflow.
    /// Variable indices >= 2^31 would cause the `<< 1` encoding to overflow u32.
    pub const MAX_VAR: u32 = (1 << 31) - 1;

    /// Create a positive literal for the given variable.
    #[inline]
    pub fn positive(var: Variable) -> Self {
        assert!(
            var.0 <= Self::MAX_VAR,
            "variable {} exceeds Literal::MAX_VAR",
            var.0
        );
        Self(var.0 << 1)
    }

    /// Create a negative literal for the given variable.
    #[inline]
    pub fn negative(var: Variable) -> Self {
        assert!(
            var.0 <= Self::MAX_VAR,
            "variable {} exceeds Literal::MAX_VAR",
            var.0
        );
        Self((var.0 << 1) | 1)
    }

    /// Get the underlying variable.
    #[inline]
    pub fn variable(self) -> Variable {
        Variable(self.0 >> 1)
    }

    /// True if this literal has positive polarity.
    #[inline]
    pub fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Get the negation of this literal.
    #[inline]
    pub fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }

    /// Index into watch/assignment arrays (2 entries per variable).
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Create a literal from a raw index (inverse of `index()`).
    ///
    /// The index encodes both variable and polarity: `positive = 2*var`,
    /// `negative = 2*var + 1`. This enables zero-cost conversion between
    /// literal types that use the same encoding scheme.
    #[inline]
    pub fn from_index(idx: usize) -> Self {
        Self(idx as u32)
    }

    /// Create a literal from a DIMACS-style signed integer.
    ///
    /// DIMACS variables are 1-indexed. `from_dimacs(3)` → positive literal for
    /// internal variable 2. `from_dimacs(-1)` → negative literal for variable 0.
    #[inline]
    pub fn from_dimacs(dimacs: i32) -> Self {
        assert_ne!(dimacs, 0, "DIMACS literal 0 is a clause terminator");
        let var = Variable(dimacs.unsigned_abs() - 1);
        if dimacs > 0 {
            Self::positive(var)
        } else {
            Self::negative(var)
        }
    }

    /// Convert to DIMACS signed integer (inverse of `from_dimacs`).
    ///
    /// Panics if the variable ID exceeds `i32::MAX - 1` (2_147_483_646),
    /// which would cause the 1-indexed DIMACS representation to overflow.
    /// Use [`to_dimacs_i64`] or the `Display` impl for extension variables
    /// that may exceed this range.
    #[inline]
    pub fn to_dimacs(self) -> i32 {
        let raw = self.variable().id();
        let var_1indexed = i32::try_from(raw)
            .ok()
            .and_then(|v| v.checked_add(1))
            .expect("variable ID too large for DIMACS i32 representation");
        if self.is_positive() {
            var_1indexed
        } else {
            -var_1indexed
        }
    }

    /// Convert to DIMACS signed integer as `i64` (never panics).
    ///
    /// Extension variables in LRAT proofs (extended resolution) can have
    /// variable IDs up to `u32::MAX >> 1`, which exceeds `i32::MAX - 1`.
    /// This method uses `i64` arithmetic to avoid overflow on any valid
    /// literal. Prefer this in diagnostic/error paths where panicking would
    /// mask the real error (#5327).
    #[inline]
    pub fn to_dimacs_i64(self) -> i64 {
        let var_1indexed = i64::from(self.variable().id()) + 1;
        if self.is_positive() {
            var_1indexed
        } else {
            -var_1indexed
        }
    }
}

impl std::fmt::Display for Literal {
    /// Format as DIMACS signed integer. Uses `i64` internally to handle
    /// extension variables that exceed `i32::MAX` (#5327).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_dimacs_i64())
    }
}

#[cfg(test)]
#[path = "literal_tests.rs"]
mod tests;
