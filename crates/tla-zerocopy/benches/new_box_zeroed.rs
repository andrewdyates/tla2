// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use zerocopy::*;

#[path = "formats/coco_static_size.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_new_box_zeroed() -> Option<Box<format::LocoPacket>> {
    FromZeros::new_box_zeroed().ok()
}
