// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Header: `semaphore.h`

use super::*;
use crate::prelude::*;

extern "C" {
    pub fn sem_init(sem: *mut sem_t, pshared: c_int, value: c_uint) -> c_int;
    pub fn sem_destroy(sem: *mut sem_t) -> c_int;
    pub fn sem_wait(sem: *mut sem_t) -> c_int;
    pub fn sem_trywait(sem: *mut sem_t) -> c_int;
    pub fn sem_post(sem: *mut sem_t) -> c_int;
    pub fn sem_getvalue(sem: *mut sem_t, sval: *mut c_int) -> c_int;
}
