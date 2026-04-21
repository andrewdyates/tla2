// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[path = "formats/coco_static_size.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_try_ref_from_bytes_static_size(source: &[u8]) -> Option<&format::CocoPacket> {
    zerocopy::TryFromBytes::try_ref_from_bytes(source).ok()
}
