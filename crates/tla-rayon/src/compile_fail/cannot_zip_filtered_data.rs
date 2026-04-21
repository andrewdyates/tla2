// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

/*! ```compile_fail,E0277

use rayon::prelude::*;

// zip requires data of exact size, but filter yields only bounded
// size, so check that we cannot apply it.

let mut a: Vec<usize> = (0..1024).rev().collect();
let b: Vec<usize> = (0..1024).collect();

a.par_iter()
    .zip(b.par_iter().filter(|&&x| x > 3)); //~ ERROR

``` */
