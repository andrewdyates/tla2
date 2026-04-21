// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "Win32_UI_Accessibility")]
pub mod Accessibility;
#[cfg(feature = "Win32_UI_ColorSystem")]
pub mod ColorSystem;
#[cfg(feature = "Win32_UI_Controls")]
pub mod Controls;
#[cfg(feature = "Win32_UI_HiDpi")]
pub mod HiDpi;
#[cfg(feature = "Win32_UI_Input")]
pub mod Input;
#[cfg(feature = "Win32_UI_InteractionContext")]
pub mod InteractionContext;
#[cfg(feature = "Win32_UI_Magnification")]
pub mod Magnification;
#[cfg(feature = "Win32_UI_Shell")]
pub mod Shell;
#[cfg(feature = "Win32_UI_TabletPC")]
pub mod TabletPC;
#[cfg(feature = "Win32_UI_TextServices")]
pub mod TextServices;
#[cfg(feature = "Win32_UI_WindowsAndMessaging")]
pub mod WindowsAndMessaging;
