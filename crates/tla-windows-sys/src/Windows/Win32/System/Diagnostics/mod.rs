// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "Win32_System_Diagnostics_Ceip")]
pub mod Ceip;
#[cfg(feature = "Win32_System_Diagnostics_Debug")]
pub mod Debug;
#[cfg(feature = "Win32_System_Diagnostics_Etw")]
pub mod Etw;
#[cfg(feature = "Win32_System_Diagnostics_ProcessSnapshotting")]
pub mod ProcessSnapshotting;
#[cfg(feature = "Win32_System_Diagnostics_ToolHelp")]
pub mod ToolHelp;
#[cfg(feature = "Win32_System_Diagnostics_TraceLogging")]
pub mod TraceLogging;
