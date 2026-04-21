// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

mod help;
#[cfg(feature = "help")]
mod help_template;
mod usage;

pub(crate) mod fmt;
#[cfg(feature = "help")]
pub(crate) mod textwrap;

pub(crate) use self::help::write_help;
#[cfg(feature = "help")]
pub(crate) use self::help_template::AutoHelp;
#[cfg(feature = "help")]
pub(crate) use self::help_template::HelpTemplate;
#[cfg(feature = "help")]
pub(crate) use self::textwrap::core::display_width;
#[cfg(feature = "help")]
pub(crate) use self::textwrap::wrap;
pub(crate) use self::usage::Usage;

pub(crate) const TAB: &str = "  ";
#[cfg(feature = "help")]
pub(crate) const TAB_WIDTH: usize = TAB.len();
