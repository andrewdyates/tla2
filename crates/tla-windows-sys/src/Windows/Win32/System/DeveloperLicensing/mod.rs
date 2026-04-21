// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

windows_link::link!("wsclient.dll" "system" fn AcquireDeveloperLicense(hwndparent : super::super::Foundation:: HWND, pexpiration : *mut super::super::Foundation:: FILETIME) -> windows_sys::core::HRESULT);
windows_link::link!("wsclient.dll" "system" fn CheckDeveloperLicense(pexpiration : *mut super::super::Foundation:: FILETIME) -> windows_sys::core::HRESULT);
windows_link::link!("wsclient.dll" "system" fn RemoveDeveloperLicense(hwndparent : super::super::Foundation:: HWND) -> windows_sys::core::HRESULT);
