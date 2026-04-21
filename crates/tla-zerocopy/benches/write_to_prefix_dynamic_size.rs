// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use zerocopy::*;

#[path = "formats/coco_dynamic_size.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_write_to_prefix_dynamic_size(
    source: &format::CocoPacket,
    destination: &mut [u8],
) -> Option<()> {
    source.write_to_prefix(destination).ok()
}
