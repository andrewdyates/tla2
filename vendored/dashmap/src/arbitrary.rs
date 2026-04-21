// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use arbitrary::{Arbitrary, Unstructured};
use core::hash::BuildHasher;

impl<'a, K, V, S> Arbitrary<'a> for crate::DashMap<K, V, S>
where
    K: Eq + std::hash::Hash + Arbitrary<'a>,
    V: Arbitrary<'a>,
    S: Default + BuildHasher + Clone,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        u.arbitrary_iter()?.collect()
    }
}
