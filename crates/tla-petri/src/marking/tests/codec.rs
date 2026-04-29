// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::marking::{
    pack_marking, pack_marking_config, unpack_marking, unpack_marking_config, MarkingConfig,
    TokenWidth,
};

#[test]
fn test_pack_unpack_u8_roundtrip() {
    let marking = vec![0, 1, 255, 42, 0];
    let mut buf = Vec::new();
    pack_marking(&marking, TokenWidth::U8, &mut buf);
    assert_eq!(buf.len(), 5);
    assert_eq!(buf, vec![0, 1, 255, 42, 0]);

    let mut out = Vec::new();
    unpack_marking(&buf, TokenWidth::U8, 5, &mut out);
    assert_eq!(out, marking);
}

#[test]
fn test_pack_unpack_u16_roundtrip() {
    let marking = vec![0, 300, 65_535, 1000];
    let mut buf = Vec::new();
    pack_marking(&marking, TokenWidth::U16, &mut buf);
    assert_eq!(buf.len(), 8);

    let mut out = Vec::new();
    unpack_marking(&buf, TokenWidth::U16, 4, &mut out);
    assert_eq!(out, marking);
}

#[test]
fn test_pack_unpack_u64_roundtrip() {
    let marking = vec![0, 1, u64::MAX, 1_000_000];
    let mut buf = Vec::new();
    pack_marking(&marking, TokenWidth::U64, &mut buf);
    assert_eq!(buf.len(), 32);

    let mut out = Vec::new();
    unpack_marking(&buf, TokenWidth::U64, 4, &mut out);
    assert_eq!(out, marking);
}

#[test]
fn test_pack_empty_marking() {
    let marking: Vec<u64> = vec![];
    let mut buf = Vec::new();
    pack_marking(&marking, TokenWidth::U8, &mut buf);
    assert!(buf.is_empty());

    let mut out = Vec::new();
    unpack_marking(&buf, TokenWidth::U8, 0, &mut out);
    assert!(out.is_empty());
}

#[test]
fn test_pack_reuses_buffer() {
    let m1 = vec![1, 2, 3];
    let m2 = vec![4, 5, 6];
    let mut buf = Vec::new();

    pack_marking(&m1, TokenWidth::U8, &mut buf);
    let ptr1 = buf.as_ptr();
    assert_eq!(buf, vec![1, 2, 3]);

    pack_marking(&m2, TokenWidth::U8, &mut buf);
    assert_eq!(buf, vec![4, 5, 6]);
    assert_eq!(buf.as_ptr(), ptr1);
}

#[test]
fn test_distinct_markings_distinct_packed_u8() {
    let m1 = vec![1, 0];
    let m2 = vec![0, 1];
    let mut buf1 = Vec::new();
    let mut buf2 = Vec::new();
    pack_marking(&m1, TokenWidth::U8, &mut buf1);
    pack_marking(&m2, TokenWidth::U8, &mut buf2);
    assert_ne!(buf1, buf2);
}

#[test]
fn test_identical_markings_identical_packed_u16() {
    let marking = vec![300, 100];
    let mut buf1 = Vec::new();
    let mut buf2 = Vec::new();
    pack_marking(&marking, TokenWidth::U16, &mut buf1);
    pack_marking(&marking, TokenWidth::U16, &mut buf2);
    assert_eq!(buf1, buf2);
}

#[test]
fn test_marking_config_standard_matches_original() {
    let marking = vec![1, 2, 3, 4, 5];
    let config = MarkingConfig::standard(5, TokenWidth::U8);
    let mut buf_config = Vec::new();
    let mut buf_plain = Vec::new();

    pack_marking_config(&marking, &config, &mut buf_config);
    pack_marking(&marking, TokenWidth::U8, &mut buf_plain);
    assert_eq!(buf_config, buf_plain);

    let mut out_config = Vec::new();
    let mut out_plain = Vec::new();
    unpack_marking_config(&buf_config, &config, &mut out_config);
    unpack_marking(&buf_plain, TokenWidth::U8, 5, &mut out_plain);
    assert_eq!(out_config, out_plain);
}
