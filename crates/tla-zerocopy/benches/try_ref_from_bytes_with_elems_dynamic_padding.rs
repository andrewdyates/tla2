// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[path = "formats/coco_dynamic_padding.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_try_ref_from_bytes_with_elems_dynamic_padding(
    source: &[u8],
    count: usize,
) -> Option<&format::CocoPacket> {
    zerocopy::TryFromBytes::try_ref_from_bytes_with_elems(source, count).ok()
}
