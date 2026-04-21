// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

macro_rules! format_err {
    ($obj:expr, $($format:tt)+) => {{
        #[allow(unused_imports)]
        use $crate::utils::error::*;
        let msg = format!($($format)+);
        $obj.EXPECTED_Span_OR_ToTokens(msg)
    }};
}

macro_rules! abort {
    ($obj:expr, $($format:tt)+) => {{
        return Err(format_err!($obj, $($format)+));
    }};
}

macro_rules! abort_call_site {
    ($($format:tt)+) => {{
        let span = proc_macro2::Span::call_site();
        abort!(span, $($format)+)
    }};
}
