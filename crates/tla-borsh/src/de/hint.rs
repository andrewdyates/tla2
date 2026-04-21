// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[inline]
pub fn cautious<T>(hint: u32) -> usize {
    let el_size = core::mem::size_of::<T>() as u32;
    core::cmp::max(core::cmp::min(hint, 4096 / el_size), 1) as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_cautious_u8() {
        assert_eq!(cautious::<u8>(10), 10);
    }
}
