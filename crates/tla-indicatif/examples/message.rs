// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::{thread, time::Duration};

use indicatif::ProgressBar;

fn main() {
    let pb = ProgressBar::new(100).with_message("Frobbing the widget");
    for _ in 0..100 {
        thread::sleep(Duration::from_millis(30));
        pb.inc(1);
    }
}
