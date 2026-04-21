// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_traits::FromPrimitive;

fn rat(n: i64) -> BigRational {
    BigRational::from_i64(n).unwrap()
}

#[test]
fn test_tangent_plane() {
    // At point (2, 3), tangent plane is T(x,y) = 2*y + 3*x - 6
    let a = rat(2);
    let b = rat(3);

    // At the point itself: T(2,3) = 2*3 + 3*2 - 6 = 6 + 6 - 6 = 6 = 2*3
    assert_eq!(tangent_plane(&a, &b, &a, &b), rat(6));

    // At (3, 3): T = 2*3 + 3*3 - 6 = 6 + 9 - 6 = 9
    // Actual: 3*3 = 9, so tangent is exact on this line
    assert_eq!(tangent_plane(&a, &b, &rat(3), &rat(3)), rat(9));

    // At (1, 1): T = 2*1 + 3*1 - 6 = 2 + 3 - 6 = -1
    // Actual: 1*1 = 1 > -1, so tangent underestimates here
    assert_eq!(tangent_plane(&a, &b, &rat(1), &rat(1)), rat(-1));
}

#[test]
fn test_is_underestimate() {
    let a = rat(2);
    let b = rat(3);

    // First quadrant from (2,3): both dx, dy positive -> underestimate
    assert!(is_underestimate(&a, &b, &rat(3), &rat(4)));

    // Third quadrant from (2,3): both dx, dy negative -> underestimate
    assert!(is_underestimate(&a, &b, &rat(1), &rat(2)));

    // Second quadrant: dx < 0, dy > 0 -> overestimate
    assert!(!is_underestimate(&a, &b, &rat(1), &rat(4)));

    // Fourth quadrant: dx > 0, dy < 0 -> overestimate
    assert!(!is_underestimate(&a, &b, &rat(3), &rat(2)));
}
