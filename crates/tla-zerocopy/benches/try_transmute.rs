// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use zerocopy::Unalign;
use zerocopy_derive::*;

#[path = "formats/coco_static_size.rs"]
mod format;

#[derive(IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
struct MinimalViableSource {
    bytes: [u8; 6],
}

#[unsafe(no_mangle)]
fn bench_try_transmute(source: MinimalViableSource) -> Option<Unalign<format::CocoPacket>> {
    zerocopy::try_transmute!(source).ok()
}
