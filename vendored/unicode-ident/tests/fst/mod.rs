#![allow(clippy::module_name_repetitions)]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0


pub fn xid_start_fst() -> fst::Set<&'static [u8]> {
    let data = include_bytes!("xid_start.fst");
    fst::Set::from(fst::raw::Fst::new(data.as_slice()).unwrap())
}

pub fn xid_continue_fst() -> fst::Set<&'static [u8]> {
    let data = include_bytes!("xid_continue.fst");
    fst::Set::from(fst::raw::Fst::new(data.as_slice()).unwrap())
}
