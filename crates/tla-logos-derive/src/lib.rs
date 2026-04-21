// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use proc_macro::TokenStream;

#[proc_macro_derive(Logos, attributes(logos, extras, error, end, token, regex))]
pub fn logos(input: TokenStream) -> TokenStream {
    logos_codegen::generate(input.into()).into()
}
