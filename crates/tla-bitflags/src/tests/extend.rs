// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn cases() {
    let mut flags = TestFlags::empty();

    flags.extend(TestFlags::A);

    assert_eq!(TestFlags::A, flags);

    flags.extend(TestFlags::A | TestFlags::B | TestFlags::C);

    assert_eq!(TestFlags::ABC, flags);

    flags.extend(TestFlags::from_bits_retain(1 << 5));

    assert_eq!(TestFlags::ABC | TestFlags::from_bits_retain(1 << 5), flags);
}

mod external {
    use super::*;

    #[test]
    fn cases() {
        let mut flags = TestExternal::empty();

        flags.extend(TestExternal::A);

        assert_eq!(TestExternal::A, flags);

        flags.extend(TestExternal::A | TestExternal::B | TestExternal::C);

        assert_eq!(TestExternal::ABC, flags);

        flags.extend(TestExternal::from_bits_retain(1 << 5));

        assert_eq!(
            TestExternal::ABC | TestExternal::from_bits_retain(1 << 5),
            flags
        );
    }
}
