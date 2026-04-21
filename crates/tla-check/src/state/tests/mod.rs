// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! State tests — split from monolithic tests.rs (1,396 lines, 50 tests)
//!
//! Split into 6 themed files — Part of #2779

use super::value_hash::hash_value;
use super::*;
use crate::value::{
    FuncSetValue, FuncValue, IntervalValue, MVPerm, RecordSetValue, SetPredValue, SubsetValue,
    TupleSetValue,
};
use crate::var_index::VarIndex;
use num_bigint::{BigInt, ToBigInt};
use num_traits::ToPrimitive;
use tla_core::{FNV_OFFSET, FNV_PRIME};

mod array_state;
mod basics;
mod canonical_fingerprint;
mod conversions;
mod hash_consistency;
mod hashing;
mod helpers;
mod symmetry;
mod worker_value_hash;
