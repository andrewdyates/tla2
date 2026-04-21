// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Header: `sys/_types/_ucontext.h`

pub use crate::machine::_mcontext::*;
use crate::prelude::*;

s! {
    pub struct __darwin_ucontext {
        pub uc_onstack: c_int,
        pub uc_sigmask: crate::sigset_t,
        pub uc_stack: crate::stack_t,
        pub uc_link: *mut ucontext_t,
        pub uc_mcsize: usize,
        pub uc_mcontext: mcontext_t,
    }
}

pub type ucontext_t = __darwin_ucontext;
