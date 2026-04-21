// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Benchmark: z4 library API vs subprocess for flatzinc-smt integration.
// This module evaluates whether linking z4 as a library crate can replace
// the current subprocess approach, measuring latency for check-sat round trips.

#[allow(deprecated)]
#[cfg(test)]
#[path = "z4_library_bench_tests.rs"]
mod tests;
