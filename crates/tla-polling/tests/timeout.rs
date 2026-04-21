// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use std::io;
use std::time::{Duration, Instant};

use polling::{Events, Poller};

#[test]
fn twice() -> io::Result<()> {
    let poller = Poller::new()?;
    let mut events = Events::new();

    for _ in 0..2 {
        let start = Instant::now();
        poller.wait(&mut events, Some(Duration::from_secs(1)))?;
        let elapsed = start.elapsed();

        assert!(elapsed >= Duration::from_secs(1));
    }

    Ok(())
}

#[test]
fn non_blocking() -> io::Result<()> {
    let poller = Poller::new()?;
    let mut events = Events::new();

    for _ in 0..100 {
        poller.wait(&mut events, Some(Duration::from_secs(0)))?;
    }

    Ok(())
}
