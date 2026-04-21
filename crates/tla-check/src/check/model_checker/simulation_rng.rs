// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Simple RNG for reproducible simulation randomness.

use std::time::{SystemTime, UNIX_EPOCH};

/// A simple linear congruential generator for reproducible randomness
pub(super) struct SimpleRng {
    state: u64,
}

impl SimpleRng {
    pub(super) fn entropy_seed() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(42)
    }

    pub(super) fn new(seed: u64) -> Self {
        SimpleRng {
            state: seed.wrapping_add(1),
        }
    }

    fn next_u64(&mut self) -> u64 {
        // LCG parameters from Numerical Recipes
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.state
    }

    pub(super) fn next_usize(&mut self, bound: usize) -> usize {
        if bound == 0 {
            return 0;
        }
        (self.next_u64() % (bound as u64)) as usize
    }

    /// Generate a random prime for stride, matching TLC's RandomGenerator.nextPrime().
    /// Part of #3316: used for prime-stride action iteration in single-action evaluation.
    pub(super) fn next_prime(&mut self) -> usize {
        let mut p = (self.next_u64() % 65536) as usize;
        if p <= 1 {
            p = 2;
        }
        while !is_prime(p) {
            p += 1;
        }
        p
    }
}

fn is_prime(n: usize) -> bool {
    if n < 2 {
        return false;
    }
    if n < 4 {
        return true;
    }
    if n % 2 == 0 || n % 3 == 0 {
        return false;
    }
    let mut i = 5;
    while i * i <= n {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_rng_deterministic_sequence() {
        let mut rng1 = SimpleRng::new(42);
        let mut rng2 = SimpleRng::new(42);

        let seq1: Vec<u64> = (0..10).map(|_| rng1.next_u64()).collect();
        let seq2: Vec<u64> = (0..10).map(|_| rng2.next_u64()).collect();
        assert_eq!(seq1, seq2, "Same seed should produce identical sequences");
    }

    #[test]
    fn test_simple_rng_different_seeds_differ() {
        let mut rng1 = SimpleRng::new(1);
        let mut rng2 = SimpleRng::new(2);

        let v1 = rng1.next_u64();
        let v2 = rng2.next_u64();
        assert_ne!(
            v1, v2,
            "Different seeds should produce different first values"
        );
    }

    #[test]
    fn test_simple_rng_next_usize_bound_zero() {
        let mut rng = SimpleRng::new(99);
        assert_eq!(rng.next_usize(0), 0, "bound=0 should return 0");
    }

    #[test]
    fn test_simple_rng_next_usize_bound_one() {
        let mut rng = SimpleRng::new(99);
        for _ in 0..20 {
            assert_eq!(rng.next_usize(1), 0, "bound=1 should always return 0");
        }
    }

    #[test]
    fn test_simple_rng_next_usize_in_range() {
        let mut rng = SimpleRng::new(12345);
        let bound = 10;
        for _ in 0..100 {
            let val = rng.next_usize(bound);
            assert!(
                val < bound,
                "next_usize({}) returned {}, expected < {}",
                bound,
                val,
                bound
            );
        }
    }

    #[test]
    fn test_simple_rng_seed_zero_works() {
        let mut rng = SimpleRng::new(0);
        let v = rng.next_u64();
        assert_ne!(v, 0, "Seed 0 should not produce degenerate zero sequence");
    }
}
