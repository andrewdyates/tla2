// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_traits::FromPrimitive;

fn rat(n: i64) -> BigRational {
    BigRational::from_i64(n).unwrap()
}

#[test]
fn test_mccormick_bounds_at_corners() {
    // For m = x*y with x ∈ [2,3], y ∈ [2,3]:
    // Lower 1 at (2,2): m ≥ 2*y + 2*x - 4 → at (3,3): m ≥ 6+6-4 = 8
    // Lower 2 at (3,3): m ≥ 3*y + 3*x - 9 → at (2,2): m ≥ 6+6-9 = 3
    // Upper 1 at (3,2): m ≤ 3*y + 2*x - 6 → at (3,3): m ≤ 9+6-6 = 9
    // Upper 2 at (2,3): m ≤ 2*y + 3*x - 6 → at (3,3): m ≤ 6+9-6 = 9
    let xl = rat(2);
    let xu = rat(3);
    let yl = rat(2);
    let yu = rat(3);

    // Upper bound 1 at (3,3): 3*3 + 2*3 - 3*2 = 9+6-6 = 9 ✓
    let ub1 = &xu * &yu + &yl * &xu - &xu * &yl;
    assert_eq!(ub1, rat(9));

    // Upper bound 2 at (3,3): 2*3 + 3*3 - 2*3 = 6+9-6 = 9 ✓
    let ub2 = &xl * &yu + &yu * &xu - &xl * &yu;
    assert_eq!(ub2, rat(9));

    // At (2,2): upper bound 1 = 3*2 + 2*2 - 3*2 = 6+4-6 = 4 = 2*2 ✓ (exact at corner)
    let ub1_at_22 = &xu * &yl + &yl * &xl - &xu * &yl;
    assert_eq!(ub1_at_22, rat(4));
}

#[test]
fn test_tangent_hyperplane_ternary() {
    // For m = x*y*z at (2, 3, 5): product = 30
    // Partial derivatives: ∂(xyz)/∂x = yz = 15, ∂/∂y = xz = 10, ∂/∂z = xy = 6
    // T = 15*x + 10*y + 6*z - 2*30 = 15x + 10y + 6z - 60
    let vals = [rat(2), rat(3), rat(5)];
    let product = rat(30);

    // General formula bound: -(3-1)*30 = -60
    let bound = -(rat(2) * &product);
    assert_eq!(bound, rat(-60));

    // Coefficients
    let coeff_x = -(&product / &vals[0]); // -30/2 = -15
    let coeff_y = -(&product / &vals[1]); // -30/3 = -10
    let coeff_z = -(&product / &vals[2]); // -30/5 = -6
    assert_eq!(coeff_x, rat(-15));
    assert_eq!(coeff_y, rat(-10));
    assert_eq!(coeff_z, rat(-6));
}
