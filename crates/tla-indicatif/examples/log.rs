// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::thread;
use std::time::Duration;

use indicatif::ProgressBar;

fn main() {
    let pb = ProgressBar::new(100);
    for i in 0..100 {
        thread::sleep(Duration::from_millis(25));
        pb.println(format!("[+] finished #{i}"));
        pb.inc(1);
    }
    pb.finish_with_message("done");
}
