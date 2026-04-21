// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use zerocopy::*;

#[path = "formats/coco_dynamic_size.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_split_via_runtime_check_dynamic_size(
    split: Split<&format::CocoPacket>,
) -> Option<(&format::CocoPacket, &[[u8; 2]])> {
    split.via_runtime_check().ok()
}
