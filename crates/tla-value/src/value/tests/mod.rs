// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value type tests, split by domain from the original monolithic tests.rs.
//! Part of #1371: oversized test module decomposition.

mod compose_perm_tests;
mod core_values;
mod dedup_fingerprint_tests;
mod equivalence;
mod fingerprint_tests;
mod funcset_domain_tests;
mod hashing_tests;
mod interval_domain_tests;
mod ksubset_union;
mod lazy_sets;
mod ordering_tests;
mod record_except_tests;
mod seq_except_tests;
mod seq_flat_view_tests;
mod set_ops_tests;
mod setpred_contract_tests;
mod tlc_cmp_tests;
