// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0
// Verbatim fork of httparse (https://github.com/seanmonstar/httparse)
// for TLA2 zero-external-dependency posture (Part of #4250, Wave 36).

use super::avx2;
use super::sse42;
use crate::iter::Bytes;
use std::sync::atomic::{AtomicU8, Ordering};

const AVX2: u8 = 1;
const SSE42: u8 = 2;
const NOP: u8 = 3;

fn detect_runtime_feature() -> u8 {
    if is_x86_feature_detected!("avx2") {
        AVX2
    } else if is_x86_feature_detected!("sse4.2") {
        SSE42
    } else {
        NOP
    }
}

static RUNTIME_FEATURE: AtomicU8 = AtomicU8::new(0);

#[inline]
fn get_runtime_feature() -> u8 {
    let mut feature = RUNTIME_FEATURE.load(Ordering::Relaxed);
    if feature == 0 {
        feature = detect_runtime_feature();
        RUNTIME_FEATURE.store(feature, Ordering::Relaxed);
    }

    feature
}

pub fn match_header_name_vectored(bytes: &mut Bytes) {
    super::swar::match_header_name_vectored(bytes);
}

pub fn match_uri_vectored(bytes: &mut Bytes) {
    // SAFETY: calls are guarded by a feature check
    unsafe {
        match get_runtime_feature() {
            AVX2 => avx2::match_uri_vectored(bytes),
            SSE42 => sse42::match_uri_vectored(bytes),
            _ /* NOP */ => super::swar::match_uri_vectored(bytes),
        }
    }
}

pub fn match_header_value_vectored(bytes: &mut Bytes) {
    // SAFETY: calls are guarded by a feature check
    unsafe {
        match get_runtime_feature() {
            AVX2 => avx2::match_header_value_vectored(bytes),
            SSE42 => sse42::match_header_value_vectored(bytes),
            _ /* NOP */ => super::swar::match_header_value_vectored(bytes),
        }
    }
}
