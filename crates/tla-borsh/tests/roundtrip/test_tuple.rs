// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use borsh::{from_slice, to_vec};

#[test]
fn test_unary_tuple() {
    let expected = (true,);
    let buf = to_vec(&expected).unwrap();
    #[cfg(feature = "std")]
    insta::assert_debug_snapshot!(buf);
    let actual = from_slice::<(bool,)>(&buf).expect("failed to deserialize");
    assert_eq!(actual, expected);
}
