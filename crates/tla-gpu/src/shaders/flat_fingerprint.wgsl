// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// GPU compute shader for batch flat-state fingerprinting.
//
// Implements the XOR-accumulator algorithm from flat_fingerprint.rs:
//   for each slot i in state:
//     lo = splitmix64_mix(salt[i] ^ value_as_u64)
//     hi = splitmix64_mix(rotate_left_32(salt[i]) ^ value_as_u64)
//     contribution = (hi, lo)   // 128-bit: hi in upper 64, lo in lower 64
//     fp ^= contribution
//
// Each invocation computes one state's 128-bit fingerprint from the flat i64
// buffer. The output is 4 consecutive u32 per state (lo_lo, lo_hi, hi_lo, hi_hi).
//
// WGSL lacks native u64/i64. We emulate using vec2<u32> where .x = low, .y = high.
//
// Part of #3956: GPU Phase 1 — Metal compute shader for batch state fingerprinting.

struct Params {
    slots_per_state: u32,
    num_states: u32,
    _pad0: u32,
    _pad1: u32,
}

// States: flattened array of i64 values as pairs of u32 (lo, hi).
// Layout: [state0_slot0_lo, state0_slot0_hi, state0_slot1_lo, ...]
@group(0) @binding(0) var<storage, read> states: array<u32>;

// Per-slot salts as pairs of u32 (lo, hi). Length = slots_per_state.
@group(0) @binding(1) var<storage, read> salts: array<u32>;

// Output 128-bit fingerprints: 4 x u32 per state.
// Layout: [fp0_lo_lo, fp0_lo_hi, fp0_hi_lo, fp0_hi_hi, fp1_lo_lo, ...]
@group(0) @binding(2) var<storage, read_write> fingerprints: array<u32>;

@group(0) @binding(3) var<uniform> params: Params;

// ============================================================================
// 64-bit arithmetic helpers using vec2<u32> (.x = low, .y = high)
// ============================================================================

fn xor64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    return vec2<u32>(a.x ^ b.x, a.y ^ b.y);
}

fn add64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let lo = a.x + b.x;
    let carry = select(0u, 1u, lo < a.x);
    let hi = a.y + b.y + carry;
    return vec2<u32>(lo, hi);
}

// 64-bit wrapping multiply: returns lower 64 bits of a * b.
fn mul64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let a_lo_lo = a.x & 0xFFFFu;
    let a_lo_hi = a.x >> 16u;
    let b_lo_lo = b.x & 0xFFFFu;
    let b_lo_hi = b.x >> 16u;

    let p0 = a_lo_lo * b_lo_lo;
    let p1 = a_lo_lo * b_lo_hi;
    let p2 = a_lo_hi * b_lo_lo;
    let p3 = a_lo_hi * b_lo_hi;

    let mid = p1 + p2;
    let mid_carry = select(0u, 1u, mid < p1);

    let lo_with_mid = p0 + (mid << 16u);
    let lo_carry = select(0u, 1u, lo_with_mid < p0);

    let result_lo = lo_with_mid;
    let result_hi = p3 + (mid >> 16u) + (mid_carry << 16u) + lo_carry;

    let cross = a.x * b.y + a.y * b.x;
    return vec2<u32>(result_lo, result_hi + cross);
}

// 64-bit right shift by n bits (0 < n < 32).
fn shr64(v: vec2<u32>, n: u32) -> vec2<u32> {
    let lo = (v.x >> n) | (v.y << (32u - n));
    let hi = v.y >> n;
    return vec2<u32>(lo, hi);
}

// 64-bit rotate left by 32 bits = swap lo and hi halves.
fn rotl64_32(v: vec2<u32>) -> vec2<u32> {
    return vec2<u32>(v.y, v.x);
}

// ============================================================================
// SplitMix64 constants
// ============================================================================

// 0x9E3779B97F4A7C15
const SM_ADD_LO: u32 = 0x7F4A7C15u;
const SM_ADD_HI: u32 = 0x9E3779B9u;

// 0xBF58476D1CE4E5B9
const SM_MUL1_LO: u32 = 0x1CE4E5B9u;
const SM_MUL1_HI: u32 = 0xBF58476Du;

// 0x94D049BB133111EB
const SM_MUL2_LO: u32 = 0x133111EBu;
const SM_MUL2_HI: u32 = 0x94D049BBu;

// ============================================================================
// splitmix64_mix: finalizer / bit mixer
// ============================================================================

fn splitmix64_mix(x_in: vec2<u32>) -> vec2<u32> {
    // x = x.wrapping_add(0x9E3779B97F4A7C15)
    var x = add64(x_in, vec2<u32>(SM_ADD_LO, SM_ADD_HI));

    // x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9)
    x = xor64(x, shr64(x, 30u));
    x = mul64(x, vec2<u32>(SM_MUL1_LO, SM_MUL1_HI));

    // x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB)
    x = xor64(x, shr64(x, 27u));
    x = mul64(x, vec2<u32>(SM_MUL2_LO, SM_MUL2_HI));

    // x ^ (x >> 31)
    x = xor64(x, shr64(x, 31u));

    return x;
}

// ============================================================================
// Main compute shader
// ============================================================================

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let state_idx = gid.x;
    if state_idx >= params.num_states {
        return;
    }

    let sps = params.slots_per_state;
    let state_base = state_idx * sps * 2u;

    // Accumulate 128-bit fingerprint as two vec2<u32>: fp_lo (lower 64), fp_hi (upper 64)
    var fp_lo = vec2<u32>(0u, 0u);
    var fp_hi = vec2<u32>(0u, 0u);

    for (var s = 0u; s < sps; s = s + 1u) {
        // Read i64 value as (lo, hi) u32 pair
        let val = vec2<u32>(states[state_base + s * 2u], states[state_base + s * 2u + 1u]);

        // Read salt as (lo, hi) u32 pair
        let salt = vec2<u32>(salts[s * 2u], salts[s * 2u + 1u]);

        // mixed_lo = splitmix64_mix(salt ^ value_bits)
        let mixed_lo = splitmix64_mix(xor64(salt, val));

        // mixed_hi = splitmix64_mix(rotate_left_32(salt) ^ value_bits)
        let rotated_salt = rotl64_32(salt);
        let mixed_hi = splitmix64_mix(xor64(rotated_salt, val));

        // fp ^= contribution: fp_lo ^= mixed_lo, fp_hi ^= mixed_hi
        fp_lo = xor64(fp_lo, mixed_lo);
        fp_hi = xor64(fp_hi, mixed_hi);
    }

    // Write 128-bit fingerprint: 4 consecutive u32
    let out_base = state_idx * 4u;
    fingerprints[out_base] = fp_lo.x;       // lo_lo
    fingerprints[out_base + 1u] = fp_lo.y;  // lo_hi
    fingerprints[out_base + 2u] = fp_hi.x;  // hi_lo
    fingerprints[out_base + 3u] = fp_hi.y;  // hi_hi
}
