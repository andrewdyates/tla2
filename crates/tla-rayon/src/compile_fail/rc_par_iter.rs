// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/*! ```compile_fail,E0599

// Check that we can't use the par-iter API to access contents of an
// `Rc`.

use rayon::prelude::*;
use std::rc::Rc;

let x = vec![Rc::new(22), Rc::new(23)];
let mut y = vec![];
x.into_par_iter() //~ ERROR no method named `into_par_iter`
    .map(|rc| *rc)
    .collect_into_vec(&mut y);

``` */
