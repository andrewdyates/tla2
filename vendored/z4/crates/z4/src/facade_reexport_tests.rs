// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn stat_value_accessible_through_root_api_and_prelude() {
    let _: fn() -> Option<crate::StatValue> = || None;
    let _: fn() -> Option<crate::api::StatValue> = || None;
    let _: fn() -> Option<crate::prelude::StatValue> = || None;
}

#[test]
fn chc_detail_types_accessible_through_facade() {
    let _: fn() -> Option<crate::chc::CounterexampleStep> = || None;
    let _: fn() -> Option<crate::chc::PredicateInterpretation> = || None;
}
