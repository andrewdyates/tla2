// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Error, Debug)]
#[error("...")]
#[error("...")]
pub struct Error;

#[derive(Error, Debug)]
#[error(fmt = core::fmt::Octal::fmt)]
#[error(fmt = core::fmt::LowerHex::fmt)]
pub enum FmtFmt {}

#[derive(Error, Debug)]
#[error(fmt = core::fmt::Octal::fmt)]
#[error(transparent)]
pub enum FmtTransparent {}

#[derive(Error, Debug)]
#[error(fmt = core::fmt::Octal::fmt)]
#[error("...")]
pub enum FmtDisplay {}

fn main() {}
