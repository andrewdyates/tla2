// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for LivenessMode enum: compute, stores_full_states, is_active.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn liveness_mode_compute_tracks_storage_symmetry_and_view() {
    assert_eq!(
        LivenessMode::compute(false, false, false, false),
        LivenessMode::Disabled
    );
    assert_eq!(
        LivenessMode::compute(true, true, false, false),
        LivenessMode::FullState {
            symmetry: false,
            view: false,
        }
    );
    assert_eq!(
        LivenessMode::compute(true, true, true, true),
        LivenessMode::FullState {
            symmetry: true,
            view: true,
        }
    );
    assert_eq!(
        LivenessMode::compute(true, false, false, true),
        LivenessMode::FingerprintOnly { view: true }
    );
}

#[test]
fn liveness_mode_stores_full_states_matches_variant() {
    assert!(!LivenessMode::Disabled.stores_full_states());
    assert!(LivenessMode::FullState {
        symmetry: false,
        view: false,
    }
    .stores_full_states());
    assert!(LivenessMode::FullState {
        symmetry: true,
        view: true,
    }
    .stores_full_states());
    assert!(!LivenessMode::FingerprintOnly { view: false }.stores_full_states());
    assert!(!LivenessMode::FingerprintOnly { view: true }.stores_full_states());
}

#[test]
fn liveness_mode_is_active_matches_non_disabled() {
    assert!(!LivenessMode::Disabled.is_active());
    assert!(LivenessMode::FullState {
        symmetry: false,
        view: false,
    }
    .is_active());
    assert!(LivenessMode::FingerprintOnly { view: true }.is_active());
}
