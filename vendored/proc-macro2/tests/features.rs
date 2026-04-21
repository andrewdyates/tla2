#![allow(clippy::assertions_on_constants, clippy::ignore_without_reason)]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0


#[test]
fn make_sure_no_proc_macro() {
    assert!(
        !cfg!(feature = "proc-macro"),
        "still compiled with proc_macro?"
    );
}
