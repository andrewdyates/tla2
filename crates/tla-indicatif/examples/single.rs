// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::thread;
use std::time::Duration;

use indicatif::ProgressBar;

fn main() {
    let pb = ProgressBar::new(1024);
    for _ in 0..1024 {
        thread::sleep(Duration::from_millis(5));
        pb.inc(1);
    }
    pb.finish_with_message("done");
}
