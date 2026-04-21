// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_single_byte() {
    assert_eq!(read_u32(&[0x05], 0).unwrap(), (5, 1));
    assert_eq!(read_u64(&[0x05], 0).unwrap(), (5, 1));
}

#[test]
fn test_multi_byte() {
    // 300 = 0b100101100 → LEB128: [0xAC, 0x02]
    assert_eq!(read_u32(&[0xAC, 0x02], 0).unwrap(), (300, 2));
    assert_eq!(read_u64(&[0xAC, 0x02], 0).unwrap(), (300, 2));
}

#[test]
fn test_offset() {
    let data = [0x00, 0x05, 0x00];
    assert_eq!(read_u32(&data, 1).unwrap(), (5, 2));
}

#[test]
fn test_truncated() {
    assert!(read_u32(&[0x80], 0).is_err());
    assert!(read_u64(&[0x80], 0).is_err());
}

#[test]
fn test_overflow_u32() {
    // 5 continuation bytes = 35 bits > 32
    assert!(read_u32(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x01], 0).is_err());
}

#[test]
fn test_overflow_u64() {
    // 10 continuation bytes = 70 bits > 64
    assert!(read_u64(
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01],
        0
    )
    .is_err());
}

#[test]
fn test_zero_value() {
    assert_eq!(read_u32(&[0x00], 0).unwrap(), (0, 1));
    assert_eq!(read_u64(&[0x00], 0).unwrap(), (0, 1));
}

#[test]
fn test_max_u32() {
    // u32::MAX = 4294967295 = LEB128: [0xFF, 0xFF, 0xFF, 0xFF, 0x0F]
    let (val, pos) = read_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F], 0).unwrap();
    assert_eq!(val, u32::MAX);
    assert_eq!(pos, 5);
}

#[test]
fn test_roundtrip_u64() {
    // Encode then decode a large value
    let val: u64 = 1_000_000;
    let mut encoded = Vec::new();
    let mut v = val;
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            encoded.push(byte);
            break;
        }
        encoded.push(byte | 0x80);
    }
    let (decoded, _) = read_u64(&encoded, 0).unwrap();
    assert_eq!(decoded, val);
}
