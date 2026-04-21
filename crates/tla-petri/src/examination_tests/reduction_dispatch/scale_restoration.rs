// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Scale-restoration tests that inspect reduced nets directly.

use crate::output::Verdict;
use crate::petri_net::TransitionIdx;
use crate::reduction::{reduce_iterative, reduce_iterative_structural};

use super::super::super::{one_safe_verdict, state_space_stats};
use super::super::fixtures::default_config;
use super::support::{gcd_sensitive_one_safe_net, gcd_sensitive_state_space_net};

#[test]
fn test_one_safe_verdict_uses_structural_only_path_on_scale_sensitive_net() {
    let net = gcd_sensitive_one_safe_net();
    let config = default_config();
    let scaled = reduce_iterative(&net).expect("reduction should succeed");
    let structural =
        reduce_iterative_structural(&net).expect("structural reduction should succeed");

    assert_eq!(scaled.place_scales, vec![1, 2]);
    assert_eq!(
        scaled
            .net
            .fire(&scaled.net.initial_marking, TransitionIdx(0)),
        vec![0, 1]
    );
    assert_eq!(
        structural
            .net
            .fire(&structural.net.initial_marking, TransitionIdx(0)),
        vec![0, 2]
    );
    assert_eq!(one_safe_verdict(&net, &config, &[]), Verdict::False);
}

#[test]
fn test_state_space_stats_preserve_original_scale_on_gcd_eligible_net() {
    let net = gcd_sensitive_state_space_net();
    let config = default_config();
    let scaled = reduce_iterative(&net).expect("reduction should succeed");

    assert_eq!(scaled.net.initial_marking, vec![2, 0]);
    let stats = state_space_stats(&net, &config).expect("small net should finish");

    assert_eq!(stats.states, 3);
    assert_eq!(stats.edges, 4);
    assert_eq!(stats.max_token_in_place, 4);
    assert_eq!(stats.max_token_sum, 4);
}
