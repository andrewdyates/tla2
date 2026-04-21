// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use zerocopy::*;

#[path = "formats/coco_dynamic_size.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_split_at_dynamic_size(
    source: &format::CocoPacket,
    len: usize,
) -> Option<Split<&format::CocoPacket>> {
    source.split_at(len)
}
