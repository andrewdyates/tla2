// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

pub const PERCEPTIONFIELD_StateStream_TimeStamps: windows_sys::core::GUID = windows_sys::core::GUID::from_u128(0xaa886119_f32f_49bf_92ca_f9ddf784d297);
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct PERCEPTION_PAYLOAD_FIELD {
    pub FieldId: windows_sys::core::GUID,
    pub OffsetInBytes: u32,
    pub SizeInBytes: u32,
}
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct PERCEPTION_STATE_STREAM_TIMESTAMPS {
    pub InputTimestampInQpcCounts: i64,
    pub AvailableTimestampInQpcCounts: i64,
}
