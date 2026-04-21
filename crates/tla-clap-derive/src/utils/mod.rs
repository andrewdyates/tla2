// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

pub(crate) mod error;

mod doc_comments;
mod spanned;
mod ty;

pub(crate) use doc_comments::extract_doc_comment;
pub(crate) use doc_comments::format_doc_comment;

pub(crate) use self::{
    spanned::Sp,
    ty::{Ty, inner_type, is_simple_ty, sub_type, subty_if_name},
};
