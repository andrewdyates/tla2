// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[test]
fn full_path() {
    defmac::defmac! { len x => x.len() }

    assert_eq!(len!(&[1, 2]), 2);
}
