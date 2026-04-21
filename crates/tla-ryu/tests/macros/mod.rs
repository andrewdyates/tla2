// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

macro_rules! check {
    ($f:tt) => {
        assert_eq!(pretty($f), stringify!($f));
    };
    (-$f:tt) => {
        assert_eq!(pretty(-$f), concat!("-", stringify!($f)));
    };
}
