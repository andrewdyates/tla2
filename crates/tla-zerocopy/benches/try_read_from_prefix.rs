// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[path = "formats/coco_static_size.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_try_read_from_prefix_static_size(source: &[u8]) -> Option<format::CocoPacket> {
    match zerocopy::TryFromBytes::try_read_from_prefix(source) {
        Ok((packet, _rest)) => Some(packet),
        _ => None,
    }
}
