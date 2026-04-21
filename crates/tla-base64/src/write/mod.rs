// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Implementations of `io::Write` to transparently handle base64.
mod encoder;
mod encoder_string_writer;

pub use self::{
    encoder::EncoderWriter,
    encoder_string_writer::{EncoderStringWriter, StrConsumer},
};

#[cfg(test)]
mod encoder_tests;
