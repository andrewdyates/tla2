// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

// Forked verbatim from xxhash-rust 0.8.15 (https://github.com/DoumanAsh/xxhash-rust)
// Upstream author: Douman <douman@gmx.se>
// Upstream license: BSL-1.0 (see LICENSE-BSL)
// Fork maintainer: Andrew Yates <ayates@dropbox.com>

#[cfg(feature = "xxh32")]
#[test]
fn size_xxh32() {
    assert_eq!(core::mem::size_of::<xxhash_rust::xxh32::Xxh32>(), 44);
}

#[cfg(feature = "xxh64")]
#[test]
fn size_xxh64() {
    assert_eq!(core::mem::size_of::<xxhash_rust::xxh64::Xxh64>(), 80);
}

#[cfg(feature = "xxh3")]
#[test]
fn size_xxh3() {
    assert_eq!(core::mem::size_of::<xxhash_rust::xxh3::Xxh3>(), 576);
}
