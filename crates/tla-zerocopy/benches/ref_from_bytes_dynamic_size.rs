// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[path = "formats/coco_dynamic_size.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_ref_from_bytes_dynamic_size(source: &[u8]) -> Option<&format::LocoPacket> {
    zerocopy::FromBytes::ref_from_bytes(source).ok()
}
