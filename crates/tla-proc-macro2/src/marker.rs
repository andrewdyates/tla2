// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use alloc::rc::Rc;
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};

// Zero sized marker with the correct set of autotrait impls we want all proc
// macro types to have.
#[derive(Copy, Clone)]
#[cfg_attr(
    all(procmacro2_semver_exempt, any(not(wrap_proc_macro), super_unstable)),
    derive(PartialEq, Eq)
)]
pub(crate) struct ProcMacroAutoTraits(PhantomData<Rc<()>>);

pub(crate) const MARKER: ProcMacroAutoTraits = ProcMacroAutoTraits(PhantomData);

impl UnwindSafe for ProcMacroAutoTraits {}
impl RefUnwindSafe for ProcMacroAutoTraits {}
