// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Shell-specific generators

mod bash;
mod elvish;
mod fish;
mod powershell;
mod shell;
mod zsh;

pub use bash::Bash;
pub use elvish::Elvish;
pub use fish::Fish;
pub use powershell::PowerShell;
pub use shell::Shell;
pub use zsh::Zsh;
