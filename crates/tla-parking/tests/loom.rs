#![cfg(loom)]
// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0


#[test]
fn smoke() {
    loom::model(|| {
        let (p, u) = parking::pair();

        loom::thread::spawn(move || {
            p.park();
        });

        u.unpark();
    });
}

#[test]
fn yield_then_unpark() {
    loom::model(|| {
        let (p, u) = parking::pair();

        loom::thread::spawn(move || {
            loom::thread::yield_now();
            u.unpark();
        });

        p.park();
    });
}
