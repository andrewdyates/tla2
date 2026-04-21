// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

impl<T: Clone> ::zerocopy::util::macro_util::core_reexport::cmp::PartialEq for Foo<T>
where
    Self: ::zerocopy::IntoBytes + ::zerocopy::Immutable,
    Self: Sized,
{
    fn eq(&self, other: &Self) -> bool {
        ::zerocopy::util::macro_util::core_reexport::cmp::PartialEq::eq(
            ::zerocopy::IntoBytes::as_bytes(self),
            ::zerocopy::IntoBytes::as_bytes(other),
        )
    }
}
impl<T: Clone> ::zerocopy::util::macro_util::core_reexport::cmp::Eq for Foo<T>
where
    Self: ::zerocopy::IntoBytes + ::zerocopy::Immutable,
    Self: Sized,
{}
