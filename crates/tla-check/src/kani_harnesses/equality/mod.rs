// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value/state equality harnesses: reflexivity, symmetry, type discrimination,
//! clone (P2, P3, P5, P6, P15, P24, P25, P50, P55).

#[cfg(kani)]
mod kani_proofs;

#[cfg(test)]
mod tests;
