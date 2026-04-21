// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg(test)]
mod tests {
    use bytemuck::{Pod, Zeroable};

    bitflags! {
        #[derive(Pod, Zeroable, Clone, Copy)]
        #[repr(transparent)]
        struct Color: u32 {
            const RED = 0x1;
            const GREEN = 0x2;
            const BLUE = 0x4;
        }
    }

    #[test]
    fn test_bytemuck() {
        assert_eq!(0x1, bytemuck::cast::<Color, u32>(Color::RED));
    }
}
