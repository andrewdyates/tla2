// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Header: `pthread/stack_np.h`
//!
//! <https://github.com/apple-oss-distributions/libpthread/blob/main/include/pthread/stack_np.h>

use crate::prelude::*;

extern "C" {
    pub fn pthread_stack_frame_decode_np(
        frame_addr: uintptr_t,
        return_addr: *mut uintptr_t,
    ) -> uintptr_t;
}
