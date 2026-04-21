// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// GPU compute shader for batch state fingerprinting.
//
// Computes one fingerprint per state using the same algorithm as the CPU
// reference in tla-check/src/state/value_hash_state.rs:
//
//   for each variable i:
//     vfp = compact_value_fp(state[i])
//     contribution = salt[i] * (vfp + 1)   // wrapping multiply
//     combined ^= contribution
//   finalize: combined *= FNV_PRIME; combined ^= combined >> 33; combined *= FNV_PRIME
//
// WGSL lacks native u64. We emulate 64-bit integers using vec2<u32> where
// .x = low 32 bits, .y = high 32 bits.

struct Params {
    num_vars: u32,
    num_states: u32,
    fnv_prime_lo: u32,
    fnv_prime_hi: u32,
}

// States: flattened array of CompactValue bits as pairs of u32 (lo, hi).
// Layout: [state0_var0_lo, state0_var0_hi, state0_var1_lo, state0_var1_hi, ...]
@group(0) @binding(0) var<storage, read> states: array<u32>;

// Per-variable salts as pairs of u32 (lo, hi).
@group(0) @binding(1) var<storage, read> salts: array<u32>;

// Output fingerprints as pairs of u32 (lo, hi).
@group(0) @binding(2) var<storage, read_write> fingerprints: array<u32>;

@group(0) @binding(3) var<uniform> params: Params;

// ============================================================================
// 64-bit arithmetic helpers using vec2<u32> (lo, hi)
// ============================================================================

// 64-bit XOR
fn xor64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    return vec2<u32>(a.x ^ b.x, a.y ^ b.y);
}

// 64-bit addition with carry
fn add64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let lo = a.x + b.x;
    // Carry: if lo < a.x, there was overflow
    let carry = select(0u, 1u, lo < a.x);
    let hi = a.y + b.y + carry;
    return vec2<u32>(lo, hi);
}

// 64-bit wrapping multiply (full 64-bit result of a * b, discarding upper 64 bits)
// Uses the identity: (a_hi * 2^32 + a_lo) * (b_hi * 2^32 + b_lo)
//   = a_lo * b_lo + (a_lo * b_hi + a_hi * b_lo) * 2^32  (mod 2^64)
fn mul64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    // a_lo * b_lo: need full 64-bit result
    // Split each 32-bit value into two 16-bit halves to avoid overflow
    let a_lo_lo = a.x & 0xFFFFu;
    let a_lo_hi = a.x >> 16u;
    let b_lo_lo = b.x & 0xFFFFu;
    let b_lo_hi = b.x >> 16u;

    // Partial products for a.x * b.x
    let p0 = a_lo_lo * b_lo_lo;                    // bits [31:0]
    let p1 = a_lo_lo * b_lo_hi;                    // bits [47:16]
    let p2 = a_lo_hi * b_lo_lo;                    // bits [47:16]
    let p3 = a_lo_hi * b_lo_hi;                    // bits [63:32]

    // Combine: result_lo = p0 + (p1 + p2) << 16, result_hi = p3 + carries
    let mid = p1 + p2;  // May overflow, but we handle it
    let mid_carry = select(0u, 1u, mid < p1);  // Overflow from p1 + p2

    let lo_with_mid = p0 + (mid << 16u);
    let lo_carry = select(0u, 1u, lo_with_mid < p0);

    let result_lo = lo_with_mid;
    let result_hi = p3 + (mid >> 16u) + (mid_carry << 16u) + lo_carry;

    // Cross terms: a.x * b.y + a.y * b.x (only lower 32 bits matter for mod 2^64)
    let cross = a.x * b.y + a.y * b.x;

    return vec2<u32>(result_lo, result_hi + cross);
}

// 64-bit right shift by 33 bits
fn shr64_33(v: vec2<u32>) -> vec2<u32> {
    // Shifting by 33 = shifting high word right by 1, with no contribution from low word
    // (since 33 > 32, all of low word is shifted out, and high word shifts by 33-32=1)
    return vec2<u32>(v.y >> 1u, 0u);
}

// ============================================================================
// CompactValue fingerprinting (matches CPU compact_value_fp_from_bits)
// ============================================================================

const FNV_OFFSET_LO: u32 = 0x84222325u;
const FNV_OFFSET_HI: u32 = 0xcbf29ce4u;
const FNV_PRIME_LO: u32 = 0x000001b3u;
const FNV_PRIME_HI: u32 = 0x00000100u;

fn fnv_offset() -> vec2<u32> {
    return vec2<u32>(FNV_OFFSET_LO, FNV_OFFSET_HI);
}

fn fnv_prime() -> vec2<u32> {
    return vec2<u32>(FNV_PRIME_LO, FNV_PRIME_HI);
}

fn compact_value_fp(bits_lo: u32, bits_hi: u32) -> vec2<u32> {
    let tag = bits_lo & 7u;

    // TAG_BOOL = 0b010 = 2
    if tag == 2u {
        let b = (bits_lo >> 3u) & 1u;
        var h = fnv_offset();
        // XOR with type tag 0
        h = xor64(h, vec2<u32>(0u, 0u));
        h = mul64(h, fnv_prime());
        // XOR with bool value (0 or 1)
        h = xor64(h, vec2<u32>(b, 0u));
        h = mul64(h, fnv_prime());
        return h;
    }

    // TAG_INT = 0b001 = 1
    if tag == 1u {
        // Extract i64 via arithmetic right shift by 3
        // Reconstruct the full i64 from the shifted bits
        let shifted_lo = (bits_lo >> 3u) | (bits_hi << 29u);
        let shifted_hi = bits_hi >> 3u;
        // Sign extend: if bit 60 of original (bit 28 of hi) was set
        let sign_bit = (bits_hi >> 2u) & 1u;
        let sign_extend = select(0u, 0xE0000000u, sign_bit == 1u);
        let n_lo = shifted_lo;
        let n_hi = shifted_hi | sign_extend;

        var h = fnv_offset();
        // XOR with type tag 1
        h = xor64(h, vec2<u32>(1u, 0u));
        h = mul64(h, fnv_prime());
        // XOR with each LE byte of the i64
        // Byte 0
        h = xor64(h, vec2<u32>(n_lo & 0xFFu, 0u));
        h = mul64(h, fnv_prime());
        // Byte 1
        h = xor64(h, vec2<u32>((n_lo >> 8u) & 0xFFu, 0u));
        h = mul64(h, fnv_prime());
        // Byte 2
        h = xor64(h, vec2<u32>((n_lo >> 16u) & 0xFFu, 0u));
        h = mul64(h, fnv_prime());
        // Byte 3
        h = xor64(h, vec2<u32>((n_lo >> 24u) & 0xFFu, 0u));
        h = mul64(h, fnv_prime());
        // Byte 4
        h = xor64(h, vec2<u32>(n_hi & 0xFFu, 0u));
        h = mul64(h, fnv_prime());
        // Byte 5
        h = xor64(h, vec2<u32>((n_hi >> 8u) & 0xFFu, 0u));
        h = mul64(h, fnv_prime());
        // Byte 6
        h = xor64(h, vec2<u32>((n_hi >> 16u) & 0xFFu, 0u));
        h = mul64(h, fnv_prime());
        // Byte 7
        h = xor64(h, vec2<u32>((n_hi >> 24u) & 0xFFu, 0u));
        h = mul64(h, fnv_prime());
        return h;
    }

    // Unknown tag (heap or other): return raw bits as proxy
    return vec2<u32>(bits_lo, bits_hi);
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

    let num_vars = params.num_vars;
    // Each u64 is stored as 2 consecutive u32 values in the states array
    let state_base = state_idx * num_vars * 2u;

    var combined = vec2<u32>(0u, 0u);

    for (var v = 0u; v < num_vars; v = v + 1u) {
        // Read CompactValue bits (lo, hi)
        let cv_lo = states[state_base + v * 2u];
        let cv_hi = states[state_base + v * 2u + 1u];

        // Compute per-value fingerprint
        let vfp = compact_value_fp(cv_lo, cv_hi);

        // Read salt (lo, hi)
        let salt = vec2<u32>(salts[v * 2u], salts[v * 2u + 1u]);

        // contribution = salt * (vfp + 1)
        let vfp_plus_1 = add64(vfp, vec2<u32>(1u, 0u));
        let contribution = mul64(salt, vfp_plus_1);

        // combined ^= contribution
        combined = xor64(combined, contribution);
    }

    // Finalize: combined *= FNV_PRIME; combined ^= combined >> 33; combined *= FNV_PRIME
    let prime = vec2<u32>(params.fnv_prime_lo, params.fnv_prime_hi);
    combined = mul64(combined, prime);
    combined = xor64(combined, shr64_33(combined));
    combined = mul64(combined, prime);

    // Write output fingerprint
    fingerprints[state_idx * 2u] = combined.x;
    fingerprints[state_idx * 2u + 1u] = combined.y;
}
