// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use async_trait::async_trait;

pub struct Struct;

#[async_trait]
pub trait Trait {
    async fn f((_a, _b): (Struct, Struct)) {
        // Expands to something like:
        //
        //    fn f(__arg0: (Struct, Struct)) -> … {
        //        Box::pin(async move {
        //            let (_a, _b) = __arg0;
        //            …
        //        })
        //    }
        //
        // but user's code must not be allowed to name that temporary argument:
        let _ = __arg0;
    }
}

fn main() {}
