// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/*! ```compile_fail,E0277

// Check that we can't use the par-iter API to access contents of a `Cell`.

use rayon::prelude::*;
use std::cell::Cell;

let c = Cell::new(42_i32);
(0_i32..1024).into_par_iter()
    .map(|_| c.get()) //~ ERROR E0277
    .min();

``` */
