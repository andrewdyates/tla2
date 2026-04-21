// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::thread;
use std::time::Duration;

use indicatif::{MultiProgress, ProgressBar};

#[test]
fn main() {
    let pb = {
        let m = MultiProgress::new();
        m.add(ProgressBar::new(10))
        // The MultiProgress is dropped here.
    };

    {
        #[allow(clippy::redundant_clone)]
        let pb2 = pb.clone();
        for _ in 0..10 {
            pb2.inc(1);
            thread::sleep(Duration::from_millis(50));
        }
    }

    pb.set_message("Done");
    pb.finish();

    println!("Done with MultiProgress");
}
