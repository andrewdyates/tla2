// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::layout::MarkingConfig;
use super::width::TokenWidth;
use crate::invariant::ImpliedPlace;

fn reserve_packed_bytes(buf: &mut Vec<u8>, width: TokenWidth, values: usize) {
    buf.reserve(values * width.bytes());
}

fn encode_selected_tokens<'a>(
    values: impl Iterator<Item = &'a u64>,
    width: TokenWidth,
    count: usize,
    buf: &mut Vec<u8>,
) {
    buf.clear();
    reserve_packed_bytes(buf, width, count);

    let mut values = values;
    match width {
        TokenWidth::U8 => {
            for &value in values.by_ref() {
                buf.push(value as u8);
            }
        }
        TokenWidth::U16 => {
            for &value in values.by_ref() {
                buf.extend_from_slice(&(value as u16).to_le_bytes());
            }
        }
        TokenWidth::U64 => {
            for &value in values.by_ref() {
                buf.extend_from_slice(&value.to_le_bytes());
            }
        }
    }
}

fn decode_selected_slots(
    packed: &[u8],
    width: TokenWidth,
    target_indices: impl Iterator<Item = usize>,
    out: &mut [u64],
) {
    let mut target_indices = target_indices;
    match width {
        TokenWidth::U8 => {
            for (byte_idx, place) in target_indices.by_ref().enumerate() {
                out[place] = packed[byte_idx] as u64;
            }
        }
        TokenWidth::U16 => {
            let mut byte_idx = 0;
            for place in target_indices.by_ref() {
                out[place] = u16::from_le_bytes([packed[byte_idx], packed[byte_idx + 1]]) as u64;
                byte_idx += 2;
            }
        }
        TokenWidth::U64 => {
            let mut byte_idx = 0;
            for place in target_indices.by_ref() {
                let chunk = &packed[byte_idx..byte_idx + 8];
                out[place] = u64::from_le_bytes(chunk.try_into().expect("8-byte chunk"));
                byte_idx += 8;
            }
        }
    }
}

/// Pack a u64 marking into a compact byte representation.
///
/// Reuses `buf` to avoid allocation in the hot BFS loop.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn pack_marking(marking: &[u64], width: TokenWidth, buf: &mut Vec<u8>) {
    encode_selected_tokens(marking.iter(), width, marking.len(), buf);
}

/// Unpack a compact byte representation back to u64 token values.
///
/// Reuses `out` to avoid allocation in the hot BFS loop.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn unpack_marking(
    packed: &[u8],
    width: TokenWidth,
    num_places: usize,
    out: &mut Vec<u64>,
) {
    out.clear();
    out.resize(num_places, 0);
    decode_selected_slots(packed, width, 0..num_places, out.as_mut_slice());
}

/// Pack a full marking into compact bytes, excluding implied places.
pub(crate) fn pack_marking_config(marking: &[u64], config: &MarkingConfig, buf: &mut Vec<u8>) {
    encode_selected_tokens(
        config.stored_places().map(|place| &marking[place]),
        config.width,
        config.packed_len,
        buf,
    );
}

/// Unpack compact bytes and reconstruct implied places to produce a full marking.
pub(crate) fn unpack_marking_config(packed: &[u8], config: &MarkingConfig, out: &mut Vec<u64>) {
    out.clear();
    out.resize(config.num_places, 0);
    decode_selected_slots(
        packed,
        config.width,
        config.stored_places(),
        out.as_mut_slice(),
    );
    reconstruct_implied_places(out, config.implied_places());
}

/// Reconstruct implied places in a full marking vector.
///
/// For each implied place p:
///   `m(p) = (C - sum(w_q * m(q))) / d`
///
/// Division is exact for reachable markings by the P-invariant property.
pub(crate) fn reconstruct_implied_places(marking: &mut [u64], implied: &[ImpliedPlace]) {
    for implied_place in implied {
        let reconstruction = &implied_place.reconstruction;
        let sum: u64 = reconstruction
            .terms
            .iter()
            .map(|&(place, weight)| weight * marking[place])
            .sum();
        let numerator = reconstruction.constant - sum;
        debug_assert!(
            numerator.is_multiple_of(reconstruction.divisor),
            "P-invariant reconstruction: non-exact division for place {:?} \
             (numerator={numerator}, divisor={})",
            implied_place.place,
            reconstruction.divisor,
        );
        marking[implied_place.place] = numerator / reconstruction.divisor;
    }
}
