// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::*;
use crate::check_result::CheckResult;
use crate::ic3::Ic3Config;
use crate::parser::parse_aag;
use crate::sat_types::SolverBackend;
use crate::transys::Transys;


#[test]
fn test_portfolio_trivially_unsafe() {
    let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Bmc { step: 1 }, EngineConfig::Kind],
        max_depth: 10,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(matches!(result, CheckResult::Unsafe { .. }));
}

#[test]
fn test_portfolio_trivially_safe() {
    let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Bmc { step: 1 }, EngineConfig::Kind],
        max_depth: 10,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    // Kind should prove this safe (bad = constant FALSE)
    // BMC will return Unknown at bound
    assert!(
        result.is_definitive() || matches!(result, CheckResult::Unknown { .. }),
        "unexpected result: {result:?}"
    );
}

#[test]
fn test_portfolio_toggle_reachable() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Bmc { step: 1 }, EngineConfig::Kind],
        max_depth: 10,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(matches!(result, CheckResult::Unsafe { .. }));
}

#[test]
fn test_portfolio_latch_stays_zero() {
    // Latch next=0, bad=latch. k-induction should prove safe.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Kind],
        max_depth: 10,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Safe),
        "expected Safe, got {result:?}"
    );
}

#[test]
fn test_portfolio_default_config() {
    let config = default_portfolio();
    // Includes IC3 + inn IC3 + predprop + SimpleSolver + CEGAR + BMC + z4-variant BMC
    // + Kind (standard + simple-path #4050 + skip-bmc + z4 variants + strengthened).
    // Count drift updated after #4259 small-circuit + #4288 additions (stale expectation).
    // TL63 drive-by: bump 40 → 41 after #4307 ic3-ctg5-counter addition (b5a10a158a).
    assert_eq!(config.engines.len(), 41);
    assert_eq!(config.timeout, Duration::from_secs(3600));
}

#[test]
fn test_portfolio_ic3_safe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Ic3],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(matches!(result, CheckResult::Safe), "got {result:?}");
}

#[test]
fn test_portfolio_ic3_unsafe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Ic3],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "got {result:?}"
    );
}

#[test]
fn test_portfolio_timeout() {
    // Use a tiny timeout with a circuit that won't resolve quickly
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_millis(1), // 1ms timeout
        engines: vec![EngineConfig::Bmc { step: 1 }],
        max_depth: 1_000_000, // Very deep
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    // Should either timeout or resolve (kind would prove safe)
    // With BMC only, it should reach bound or timeout
    assert!(
        matches!(result, CheckResult::Unknown { .. } | CheckResult::Safe),
        "unexpected: {result:?}"
    );
}

// -----------------------------------------------------------------------
// IC3 portfolio variant tests
// -----------------------------------------------------------------------

#[test]
fn test_ic3_conservative_safe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_conservative()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(matches!(result, CheckResult::Safe), "got {result:?}");
}

#[test]
fn test_ic3_ctp_unsafe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_ctp()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "got {result:?}"
    );
}

#[test]
fn test_ic3_inf_safe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_inf()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(matches!(result, CheckResult::Safe), "got {result:?}");
}

#[test]
fn test_ic3_internal_safe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_internal()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(matches!(result, CheckResult::Safe), "got {result:?}");
}

#[test]
fn test_ic3_ternary_unsafe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_ternary()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "got {result:?}"
    );
}

#[test]
fn test_ic3_full_safe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_full()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(matches!(result, CheckResult::Safe), "got {result:?}");
}

#[test]
fn test_ic3_full_unsafe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_full()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "got {result:?}"
    );
}

#[test]
fn test_full_ic3_portfolio_config() {
    let config = full_ic3_portfolio();
    // Includes IC3 + inn IC3 + predprop + SimpleSolver + CEGAR + BMC + z4-variant BMC
    // + Kind (standard + simple-path #4050 + skip-bmc + z4 variants + strengthened).
    // Count bumped to 41 for ic3_ctg5_counter (#4307).
    assert_eq!(config.engines.len(), 41);
}

#[test]
fn test_competition_portfolio_config() {
    let config = competition_portfolio();
    // Competition portfolio: IC3 + inn IC3 + SimpleSolver IC3 + drop-threshold IC3
    // + CEGAR-IC3 + BMC (basic + dynamic + geometric + z4 variants + deep)
    // + Kind (standard + simple-path #4050 + skip-bmc + z4 variants + strengthened)
    // Count bumped to 63 for ic3_ctg5_counter (#4307).
    assert_eq!(config.engines.len(), 63);
}

/// #4307: `ic3_ctg5_counter` must be registered with the exact parameters from
/// R17's Gap 2 design: moderate CTG depth (ctg_max=5, ctg_limit=3, ctg_down=true).
/// The config exists to target `counter_bit_width_small` (57 latches, UNSAT) and
/// similar sequential counter benchmarks where conservative CTG misses and deep
/// CTG over-recurses. Also asserts the variant is wired into both the default
/// (`full_ic3_portfolio`) and `competition_portfolio` rotations.
#[test]
fn test_ic3_ctg5_counter_registered() {
    let engine = ic3_ctg5_counter();
    assert_eq!(engine.name(), "ic3-ctg5-counter");
    match &engine {
        EngineConfig::Ic3Configured { config, name } => {
            assert_eq!(name.as_str(), "ic3-ctg5-counter");
            assert_eq!(config.ctg_max, 5, "ctg_max must be 5 (#4307 design)");
            assert_eq!(config.ctg_limit, 3, "ctg_limit must be 3 (#4307 design)");
            assert!(
                config.ctg_down,
                "ctg_down must be true (flip-based aggressive MIC, #4307 design)"
            );
            assert_eq!(config.random_seed, 190, "random_seed must be 190 (unique)");
        }
        other => panic!("expected Ic3Configured, got {other:?}"),
    }

    // Variant must appear in both the default and competition portfolios.
    let default_has = full_ic3_portfolio()
        .engines
        .iter()
        .any(|e| e.name() == "ic3-ctg5-counter");
    assert!(
        default_has,
        "full_ic3_portfolio() must contain ic3-ctg5-counter (#4307)"
    );
    let competition_has = competition_portfolio()
        .engines
        .iter()
        .any(|e| e.name() == "ic3-ctg5-counter");
    assert!(
        competition_has,
        "competition_portfolio() must contain ic3-ctg5-counter (#4307)"
    );
}

#[test]
fn test_full_portfolio_toggle_unsafe() {
    // All IC3 variants + BMC + Kind should agree this is unsafe.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(10),
        ..full_ic3_portfolio()
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "full portfolio should find Unsafe, got {result:?}"
    );
}

#[test]
fn test_full_portfolio_latch_zero_safe() {
    // All IC3 variants + BMC + Kind should agree this is safe.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(10),
        ..full_ic3_portfolio()
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Safe),
        "full portfolio should find Safe, got {result:?}"
    );
}

#[test]
fn test_detailed_result_has_solver_name() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_conservative()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check_detailed(&circuit, config);
    assert!(
        matches!(result.result, CheckResult::Unsafe { .. }),
        "got {:?}",
        result.result
    );
    assert_eq!(result.solver_name, "ic3-conservative");
    assert!(result.time_secs >= 0.0);
}

#[test]
fn test_engine_config_names() {
    assert_eq!(ic3_conservative().name(), "ic3-conservative");
    assert_eq!(ic3_ctp().name(), "ic3-ctp");
    assert_eq!(ic3_inf().name(), "ic3-inf");
    assert_eq!(ic3_internal().name(), "ic3-internal");
    assert_eq!(ic3_ternary().name(), "ic3-ternary");
    assert_eq!(ic3_full().name(), "ic3-full");
    assert_eq!(ic3_ctp_inf().name(), "ic3-ctp-inf");
    assert_eq!(ic3_internal_ternary().name(), "ic3-internal-ternary");
    assert_eq!(ic3_deep_ctg().name(), "ic3-deep-ctg");
    assert_eq!(ic3_internal_ctp().name(), "ic3-internal-ctp");
    assert_eq!(ic3_deep_ctg_internal().name(), "ic3-deep-ctg-internal");
    assert_eq!(ic3_ternary_inf().name(), "ic3-ternary-inf");
    assert_eq!(ic3_aggressive_ctp().name(), "ic3-aggressive-ctp");
    assert_eq!(ic3_deep_ctg_ctp().name(), "ic3-deep-ctg-ctp");
    assert_eq!(ic3_full_alt_seed().name(), "ic3-full-alt");
    assert_eq!(ic3_kitchen_sink().name(), "ic3-kitchen-sink");
    assert_eq!(ic3_ctg_down().name(), "ic3-ctg-down");
    assert_eq!(ic3_ctg_down_ctp().name(), "ic3-ctg-down-ctp");
    assert_eq!(ic3_dynamic().name(), "ic3-dynamic");
    assert_eq!(ic3_dynamic_ctp().name(), "ic3-dynamic-ctp");
    assert_eq!(ic3_dynamic_internal().name(), "ic3-dynamic-internal");
    assert_eq!(ic3_no_drop().name(), "ic3-no-drop");
    assert_eq!(ic3_reverse_topo().name(), "ic3-reverse-topo");
    assert_eq!(ic3_reverse_topo_ctp().name(), "ic3-reverse-topo-ctp");
    assert_eq!(ic3_random_shuffle().name(), "ic3-random-shuffle");
    assert_eq!(ic3_random_deep().name(), "ic3-random-deep");
    assert_eq!(ic3_circuit_adapt().name(), "ic3-circuit-adapt");
    assert_eq!(ic3_circuit_adapt_full().name(), "ic3-circuit-adapt-full");
    assert_eq!(ic3_geometric_restart().name(), "ic3-geometric-restart");
    assert_eq!(ic3_luby_restart().name(), "ic3-luby-restart");
    assert_eq!(ic3_deep_pipeline().name(), "ic3-deep-pipeline");
    assert_eq!(ic3_wide_comb().name(), "ic3-wide-comb");
    assert_eq!(ic3_dynamic_adapt().name(), "ic3-dynamic-adapt");
    assert_eq!(ic3_multi_order().name(), "ic3-multi-order");
    assert_eq!(ic3_multi_order_ctp().name(), "ic3-multi-order-ctp");
    assert_eq!(ic3_multi_order_full().name(), "ic3-multi-order-full");
    assert_eq!(cegar_ic3_conservative().name(), "cegar-ic3-conservative");
    assert_eq!(cegar_ic3_ctp_inf().name(), "cegar-ic3-ctp-inf");
    assert_eq!(EngineConfig::Kind.name(), "kind");
    assert_eq!(EngineConfig::KindSimplePath.name(), "kind-simple-path");
    assert_eq!(EngineConfig::Bmc { step: 1 }.name(), "bmc-1");
    assert_eq!(EngineConfig::Bmc { step: 5 }.name(), "bmc");
    assert_eq!(EngineConfig::BmcDynamic.name(), "bmc-dynamic");
    assert_eq!(EngineConfig::KindSkipBmc.name(), "kind-skip-bmc");
    assert_eq!(EngineConfig::KindStrengthened.name(), "kind-strengthened");
}

#[test]
fn test_single_ic3_config() {
    let config = single_ic3(
        Duration::from_secs(5),
        Ic3Config {
            ctp: true,
            inf_frame: true,
            ..Ic3Config::default()
        },
        "custom-ic3",
    );
    assert_eq!(config.engines.len(), 1);
    assert_eq!(config.engines[0].name(), "custom-ic3");
}

#[test]
fn test_new_ic3_configs_safe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    for config_fn in [
        ic3_deep_ctg,
        ic3_internal_ctp,
        ic3_deep_ctg_internal,
        ic3_ternary_inf,
        ic3_aggressive_ctp,
        ic3_deep_ctg_ctp,
        ic3_full_alt_seed,
        ic3_kitchen_sink,
        ic3_ctg_down,
        ic3_ctg_down_ctp,
        ic3_dynamic,
        ic3_dynamic_ctp,
        ic3_dynamic_internal,
        ic3_no_drop,
        ic3_reverse_topo,
        ic3_reverse_topo_ctp,
        ic3_random_shuffle,
        ic3_random_deep,
        ic3_circuit_adapt,
        ic3_circuit_adapt_full,
        ic3_geometric_restart,
        ic3_luby_restart,
        ic3_deep_pipeline,
        ic3_wide_comb,
        ic3_dynamic_adapt,
        ic3_no_preprocess,
        ic3_no_parent,
        ic3_predprop,
        ic3_predprop_ctp,
    ] {
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![config_fn()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "{} should find Safe, got {result:?}",
            config_fn().name()
        );
    }
}

#[test]
fn test_new_ic3_configs_unsafe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    for config_fn in [
        ic3_deep_ctg,
        ic3_internal_ctp,
        ic3_deep_ctg_internal,
        ic3_ternary_inf,
        ic3_aggressive_ctp,
        ic3_deep_ctg_ctp,
        ic3_full_alt_seed,
        ic3_kitchen_sink,
        ic3_ctg_down,
        ic3_ctg_down_ctp,
        ic3_dynamic,
        ic3_dynamic_ctp,
        ic3_dynamic_internal,
        ic3_no_drop,
        ic3_reverse_topo,
        ic3_reverse_topo_ctp,
        ic3_random_shuffle,
        ic3_random_deep,
        ic3_circuit_adapt,
        ic3_circuit_adapt_full,
        ic3_geometric_restart,
        ic3_luby_restart,
        ic3_deep_pipeline,
        ic3_wide_comb,
        ic3_dynamic_adapt,
        ic3_no_preprocess,
        ic3_no_parent,
        ic3_predprop,
        ic3_predprop_ctp,
    ] {
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![config_fn()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "{} should find Unsafe, got {result:?}",
            config_fn().name()
        );
    }
}

#[test]
fn test_competition_portfolio_all_unique_seeds() {
    // Every IC3 config in the competition portfolio should have a unique seed.
    let config = competition_portfolio();
    let mut seeds = Vec::new();
    for engine in &config.engines {
        if let EngineConfig::Ic3Configured {
            config: ic3_cfg, ..
        } = engine
        {
            seeds.push(ic3_cfg.random_seed);
        }
    }
    let unique_count = {
        let mut s = seeds.clone();
        s.sort();
        s.dedup();
        s.len()
    };
    assert_eq!(
        unique_count,
        seeds.len(),
        "all IC3 configs must have unique seeds, got {seeds:?}"
    );
}

#[test]
fn test_competition_portfolio_ctg_diversity() {
    // Competition portfolio should have configs with default and deep CTG.
    // (Extreme CTG configs with ctg_max=7 were removed in favor of
    // generalization order diversity in #4065.)
    let config = competition_portfolio();
    let mut has_default_ctg = false;
    let mut has_deep_ctg = false;
    for engine in &config.engines {
        if let EngineConfig::Ic3Configured {
            config: ic3_cfg, ..
        } = engine
        {
            if ic3_cfg.ctg_max == 3 && ic3_cfg.ctg_limit == 1 {
                has_default_ctg = true;
            }
            if ic3_cfg.ctg_max == 5 && ic3_cfg.ctg_limit == 15 {
                has_deep_ctg = true;
            }
        }
    }
    assert!(has_default_ctg, "should have default CTG configs");
    assert!(has_deep_ctg, "should have deep CTG configs");
}

#[test]
fn test_competition_portfolio_vsids_diversity() {
    // Competition portfolio should have configs with default VSIDS decay.
    // (Fast/slow decay configs were removed in favor of generalization
    // order diversity in #4065.)
    let config = competition_portfolio();
    let mut has_default_decay = false;
    for engine in &config.engines {
        if let EngineConfig::Ic3Configured {
            config: ic3_cfg, ..
        } = engine
        {
            if (ic3_cfg.vsids_decay - 0.99).abs() < 0.001 {
                has_default_decay = true;
            }
        }
    }
    assert!(has_default_decay, "should have default decay (0.99) configs");
}

#[test]
fn test_competition_portfolio_has_skip_bmc_kind() {
    // Competition portfolio should have both Kind and KindSkipBmc for diversity.
    let config = competition_portfolio();
    let has_kind = config.engines.iter().any(|e| matches!(e, EngineConfig::Kind));
    let has_skip_bmc = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::KindSkipBmc));
    assert!(has_kind, "should have standard k-induction");
    assert!(has_skip_bmc, "should have skip-bmc k-induction");
}

#[test]
fn test_portfolio_bmc_dynamic_unsafe() {
    // Trivially unsafe (bad=1 at step 0): dynamic BMC finds it at depth 0.
    let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::BmcDynamic],
        max_depth: 1000,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "bmc-dynamic should find Unsafe, got {result:?}"
    );
}

#[test]
fn test_portfolio_bmc_geometric_backoff_unsafe() {
    // Trivially unsafe (bad=1 at step 0): geometric backoff BMC finds it at depth 0.
    let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::BmcGeometricBackoff {
            initial_depths: 50,
            double_interval: 20,
            max_step: 64,
        }],
        max_depth: 1000,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "bmc-geometric-backoff should find Unsafe, got {result:?}"
    );
}

#[test]
fn test_portfolio_bmc_geometric_backoff_z4_variant_unsafe() {
    // Toggle flip-flop: geometric backoff z4-Luby should find bug at depth 1.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::BmcGeometricBackoffZ4Variant {
            initial_depths: 50,
            double_interval: 20,
            max_step: 64,
            backend: crate::sat_types::SolverBackend::Z4Luby,
        }],
        max_depth: 1000,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "bmc-geometric-z4-luby should find Unsafe, got {result:?}"
    );
}

#[test]
fn test_default_portfolio_includes_geometric_backoff() {
    let config = default_portfolio();
    let geo_count = config
        .engines
        .iter()
        .filter(|e| {
            matches!(
                e,
                EngineConfig::BmcGeometricBackoff { .. }
                    | EngineConfig::BmcGeometricBackoffZ4Variant { .. }
            )
        })
        .count();
    assert!(
        geo_count >= 1,
        "default portfolio should have at least 1 geometric backoff BMC config, got {geo_count}"
    );
}

#[test]
fn test_competition_portfolio_includes_geometric_backoff() {
    let config = competition_portfolio();
    let geo_count = config
        .engines
        .iter()
        .filter(|e| {
            matches!(
                e,
                EngineConfig::BmcGeometricBackoff { .. }
                    | EngineConfig::BmcGeometricBackoffZ4Variant { .. }
            )
        })
        .count();
    assert!(
        geo_count >= 1,
        "competition portfolio should have at least 1 geometric backoff BMC config, got {geo_count}"
    );
}

#[test]
fn test_competition_portfolio_includes_deep_bmc_configs() {
    // Deep BMC configs (#4123, #4194): 4 geometric backoff configs tuned for
    // depths 200, 500, 1000, and 5000 respectively.
    let config = competition_portfolio();
    let deep_geo_count = config
        .engines
        .iter()
        .filter(|e| matches!(
            e,
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 3..=10,
                max_step: 32..=512,
                ..
            }
        ))
        .count();
    assert!(
        deep_geo_count >= 3,
        "competition portfolio should have at least 3 deep BMC geometric backoff configs, got {deep_geo_count}"
    );
}

#[test]
fn test_bmc_deep_200_config() {
    let config = bmc_deep_200();
    match config {
        EngineConfig::BmcGeometricBackoff {
            initial_depths,
            double_interval,
            max_step,
        } => {
            assert_eq!(initial_depths, 10, "deep-200 should start with 10 thorough depths");
            assert_eq!(double_interval, 10, "deep-200 should double every 10 calls");
            assert_eq!(max_step, 32, "deep-200 should cap step at 32");
        }
        _ => panic!("bmc_deep_200 should be BmcGeometricBackoff"),
    }
}

#[test]
fn test_bmc_deep_500_config() {
    let config = bmc_deep_500();
    match config {
        EngineConfig::BmcGeometricBackoff {
            initial_depths,
            double_interval,
            max_step,
        } => {
            assert_eq!(initial_depths, 10, "deep-500 should start with 10 thorough depths");
            assert_eq!(double_interval, 8, "deep-500 should double every 8 calls");
            assert_eq!(max_step, 64, "deep-500 should cap step at 64");
        }
        _ => panic!("bmc_deep_500 should be BmcGeometricBackoff"),
    }
}

#[test]
fn test_bmc_deep_1000_config() {
    let config = bmc_deep_1000();
    match config {
        EngineConfig::BmcGeometricBackoff {
            initial_depths,
            double_interval,
            max_step,
        } => {
            assert_eq!(initial_depths, 5, "deep-1000 should start with 5 thorough depths");
            assert_eq!(double_interval, 5, "deep-1000 should double every 5 calls");
            assert_eq!(max_step, 128, "deep-1000 should cap step at 128");
        }
        _ => panic!("bmc_deep_1000 should be BmcGeometricBackoff"),
    }
}

#[test]
fn test_bmc_deep_configs_produce_correct_results() {
    // Deep BMC configs should still find trivial unsafe properties at depth 0.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    for (name, config_fn) in [
        ("bmc_deep_200", bmc_deep_200 as fn() -> EngineConfig),
        ("bmc_deep_500", bmc_deep_500 as fn() -> EngineConfig),
        ("bmc_deep_1000", bmc_deep_1000 as fn() -> EngineConfig),
    ] {
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![config_fn()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "{name} should find Unsafe on trivial circuit, got {result:?}"
        );
    }
}

#[test]
fn test_sat_focused_portfolio_includes_deeper_bmc() {
    let config = sat_focused_portfolio();
    let has_step_500 = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::Bmc { step: 500 }));
    assert!(has_step_500, "SAT-focused portfolio should have BMC step=500");
    // Should have SimpleSolver BMC variants (#4149)
    let has_simple_bmc = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::BmcZ4Variant { backend: SolverBackend::Simple, .. }));
    assert!(has_simple_bmc, "SAT-focused portfolio should have SimpleSolver BMC (#4149)");
    // Should have deep geometric backoff with max_step >= 256 (#4149)
    let has_deep_geometric = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::BmcGeometricBackoff { max_step, .. } if *max_step >= 256));
    assert!(has_deep_geometric, "SAT-focused portfolio should have deep geometric backoff (#4149)");
    // max_depth should be at least 200,000 (#4149)
    assert!(config.max_depth >= 200000, "SAT-focused portfolio max_depth should be >= 200000");
}

#[test]
fn test_is_sat_likely_heuristic() {
    // Use real circuits to test the heuristic instead of constructing Transys manually.
    // Simple circuit: 0 inputs, 1 latch => not SAT-likely
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let ts = Transys::from_aiger(&circuit);
    assert!(!is_sat_likely(&ts), "0 inputs should not be SAT-likely");

    // Circuit with 2 inputs, 0 latches: not SAT-likely (0 latches guard)
    let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
    let ts = Transys::from_aiger(&circuit);
    assert!(!is_sat_likely(&ts), "0 latches should not be SAT-likely");
}

#[test]
fn test_is_sat_likely_small_circuit_guard() {
    // #4259: Small industrial UNSAT circuits (cal14: 54I/23L) must NOT trigger
    // Pattern 1 (inputs > 2*latches) because they are UNSAT and need IC3/kind,
    // not BMC-heavy portfolios. The guard is num_latches >= 30.
    //
    // Synthesize a small circuit with inputs=5, latches=2 (I/L ratio = 2.5):
    //   Old heuristic: 5 > 2*2 = 4 → SAT-likely (wrong for UNSAT)
    //   New heuristic: latches=2 < 30 → not SAT-likely
    let circuit = parse_aag(
        "aag 7 5 2 0 0 1\n\
         2\n4\n6\n8\n10\n\
         12 0\n14 0\n\
         14\n",
    )
    .unwrap();
    let ts = Transys::from_aiger(&circuit);
    assert!(
        !is_sat_likely(&ts),
        "#4259: small circuit (latches<30) must not trip Pattern 1 on high input ratio"
    );
}

#[test]
fn test_portfolio_kind_standard_proves_safe() {
    // Standard k-induction (no simple-path) can prove safe properties.
    // This replaces the simple-path variant which was unable to prove
    // Safe due to the #4039 soundness guard (#4050).
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Kind],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Safe),
        "kind (standard) should prove Safe, got {result:?}"
    );
}

#[test]
fn test_portfolio_kind_standard_finds_unsafe() {
    // Standard k-induction should find unsafe properties (via base case).
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Kind],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "kind (standard) should find Unsafe, got {result:?}"
    );
}

#[test]
fn test_portfolio_cancellation_propagates() {
    // Two IC3 configs racing on a trivially unsafe circuit.
    // Both should find Unsafe quickly; the first wins and cancels the other.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![ic3_conservative(), ic3_ctp()],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check_detailed(&circuit, config);
    assert!(matches!(result.result, CheckResult::Unsafe { .. }));
    // The solver name should be one of the two
    assert!(
        result.solver_name == "ic3-conservative" || result.solver_name == "ic3-ctp",
        "unexpected solver: {}",
        result.solver_name
    );
}

#[test]
fn test_ric3_portfolio_config() {
    let config = ric3_portfolio();
    // rIC3 bl_default has 16 engines: 11 IC3 + 4 BMC + 1 kind
    assert_eq!(config.engines.len(), 16, "ric3 portfolio should have 16 engines");

    // Verify we have the expected engine types
    let ic3_count = config
        .engines
        .iter()
        .filter(|e| e.name().starts_with("ic3-"))
        .count();
    let bmc_count = config
        .engines
        .iter()
        .filter(|e| e.name().starts_with("bmc"))
        .count();
    let kind_count = config
        .engines
        .iter()
        .filter(|e| e.name().starts_with("kind"))
        .count();
    assert_eq!(ic3_count, 11, "should have 11 IC3 variants");
    assert_eq!(bmc_count, 4, "should have 4 BMC variants");
    assert_eq!(kind_count, 1, "should have 1 k-induction");

    // All IC3 configs should have unique random_seeds
    let ic3_seeds: Vec<u64> = config
        .engines
        .iter()
        .filter_map(|e| match e {
            EngineConfig::Ic3Configured { config, .. } => Some(config.random_seed),
            _ => None,
        })
        .collect();
    let unique_seeds: std::collections::HashSet<u64> = ic3_seeds.iter().copied().collect();
    assert_eq!(
        ic3_seeds.len(),
        unique_seeds.len(),
        "IC3 seeds must be unique"
    );
}

#[test]
fn test_kind_skip_bmc_skips_base_case() {
    // Toggle circuit: latch starts 0, next = NOT latch, bad = latch
    // At step 1, latch=1, so bad=1 → Unsafe via base case.
    // But skip-bmc mode does NOT check base cases (that's the point --
    // a separate BMC engine handles base cases in the portfolio).
    // So it should report Safe (the induction step holds) or Unknown.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::KindSkipBmc],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    // skip-bmc only checks induction, not base case, so it won't find
    // the counterexample. It may report Safe (if induction holds) or
    // Unknown (if max_depth reached without proving induction).
    assert!(
        !matches!(result, CheckResult::Unsafe { .. }),
        "kind-skip-bmc should NOT find base case violations, got {result:?}"
    );
}

#[test]
fn test_kind_skip_bmc_proves_safe() {
    // Stuck-at-zero: latch starts 0, next = 0, bad = latch
    // Latch is always 0, so bad is never asserted → Safe
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::KindSkipBmc],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Safe),
        "kind-skip-bmc should prove Safe, got {result:?}"
    );
}

// -----------------------------------------------------------------------
// Arithmetic portfolio tests
// -----------------------------------------------------------------------

#[test]
fn test_arithmetic_portfolio_config() {
    let config = arithmetic_portfolio();
    // 6 arithmetic IC3 + 4 inn IC3 (#4148) + 4 general IC3 + 9 BMC + 2 Kind = 25
    assert_eq!(config.engines.len(), 25);
    assert_eq!(config.timeout, Duration::from_secs(3600));
    assert_eq!(config.max_depth, 50000);

    // Verify arithmetic IC3 configs are present
    let names: Vec<&str> = config.engines.iter().map(|e| e.name()).collect();
    assert!(names.contains(&"ic3-arithmetic"));
    assert!(names.contains(&"ic3-arithmetic-ctg-down"));
    assert!(names.contains(&"ic3-arithmetic-no-internal"));
    assert!(names.contains(&"ic3-arithmetic-conservative"));
    assert!(names.contains(&"ic3-arithmetic-tight-budget"));
    assert!(names.contains(&"ic3-arithmetic-core-only"));
    // Verify internal signal (--inn) IC3 configs are present (#4148)
    assert!(names.contains(&"ic3-inn"));
    assert!(names.contains(&"ic3-inn-ctp"));
    assert!(names.contains(&"ic3-inn-noctg"));
    assert!(names.contains(&"ic3-inn-dynamic"));
}

#[test]
fn test_arithmetic_ic3_configs_safe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    for config_fn in [
        ic3_arithmetic,
        ic3_arithmetic_ctg_down,
        ic3_arithmetic_no_internal,
        ic3_arithmetic_conservative,
        ic3_arithmetic_tight_budget,
        ic3_arithmetic_core_only,
    ] {
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![config_fn()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "{} should find Safe, got {result:?}",
            config_fn().name()
        );
    }
}

#[test]
fn test_arithmetic_ic3_configs_unsafe() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    for config_fn in [
        ic3_arithmetic,
        ic3_arithmetic_ctg_down,
        ic3_arithmetic_no_internal,
        ic3_arithmetic_conservative,
        ic3_arithmetic_tight_budget,
        ic3_arithmetic_core_only,
    ] {
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![config_fn()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "{} should find Unsafe, got {result:?}",
            config_fn().name()
        );
    }
}

#[test]
fn test_arithmetic_portfolio_unique_seeds() {
    let config = arithmetic_portfolio();
    let mut seeds = Vec::new();
    for engine in &config.engines {
        if let EngineConfig::Ic3Configured {
            config: ic3_cfg, ..
        } = engine
        {
            seeds.push(ic3_cfg.random_seed);
        }
    }
    let unique_count = {
        let mut s = seeds.clone();
        s.sort();
        s.dedup();
        s.len()
    };
    assert_eq!(
        unique_count,
        seeds.len(),
        "all arithmetic portfolio IC3 configs must have unique seeds, got {seeds:?}"
    );
}

#[test]
fn test_arithmetic_config_names() {
    assert_eq!(ic3_arithmetic().name(), "ic3-arithmetic");
    assert_eq!(ic3_arithmetic_ctg_down().name(), "ic3-arithmetic-ctg-down");
    assert_eq!(
        ic3_arithmetic_no_internal().name(),
        "ic3-arithmetic-no-internal"
    );
    assert_eq!(
        ic3_arithmetic_conservative().name(),
        "ic3-arithmetic-conservative"
    );
    assert_eq!(
        ic3_arithmetic_tight_budget().name(),
        "ic3-arithmetic-tight-budget"
    );
    assert_eq!(
        ic3_arithmetic_core_only().name(),
        "ic3-arithmetic-core-only"
    );
}

// -----------------------------------------------------------------------
// z4-sat variant BMC/Kind portfolio tests (replaces CaDiCaL tests)
// -----------------------------------------------------------------------

mod z4_variant_portfolio_tests {
    use super::*;

    #[test]
    fn test_portfolio_bmc_z4_luby_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::BmcZ4Variant {
                step: 1,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            }],
            max_depth: 10,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "z4-sat Luby BMC should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_bmc_z4_variant_dynamic_unsafe() {
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::BmcZ4VariantDynamic {
                backend: crate::sat_types::SolverBackend::Z4Vmtf,
            }],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "z4-sat VMTF dynamic BMC should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_bmc_z4_stable_safe_bounded() {
        // Latch next=0, bad=latch. BMC returns Unknown (can't prove safety).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::BmcZ4Variant {
                step: 1,
                backend: crate::sat_types::SolverBackend::Z4Stable,
            }],
            max_depth: 10,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unknown { .. }),
            "z4-sat Stable BMC should return Unknown for safe circuit, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_z4_variant_bmc_config_names() {
        assert_eq!(
            EngineConfig::BmcZ4Variant {
                step: 10,
                backend: crate::sat_types::SolverBackend::Z4Luby
            }
            .name(),
            "bmc-z4-luby"
        );
        assert_eq!(
            EngineConfig::BmcZ4Variant {
                step: 65,
                backend: crate::sat_types::SolverBackend::Z4Stable
            }
            .name(),
            "bmc-z4-stable"
        );
        assert_eq!(
            EngineConfig::BmcZ4VariantDynamic {
                backend: crate::sat_types::SolverBackend::Z4Vmtf
            }
            .name(),
            "bmc-z4-variant-dynamic"
        );
    }

    #[test]
    fn test_default_portfolio_includes_z4_variant_bmc() {
        let config = default_portfolio();
        let variant_count = config
            .engines
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    EngineConfig::BmcZ4Variant { .. }
                        | EngineConfig::BmcZ4VariantDynamic { .. }
                )
            })
            .count();
        assert_eq!(
            variant_count, 4,
            "default portfolio should have 4 z4-sat variant BMC configs"
        );
    }

    #[test]
    fn test_sat_focused_portfolio_includes_z4_variant_bmc() {
        let config = sat_focused_portfolio();
        let variant_count = config
            .engines
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    EngineConfig::BmcZ4Variant { .. }
                        | EngineConfig::BmcZ4VariantDynamic { .. }
                        | EngineConfig::BmcGeometricBackoffZ4Variant { .. }
                )
            })
            .count();
        // 5 SimpleSolver BMC (step 1/5/25/50/100) + 2 SimpleSolver geometric
        // + 2 z4-sat variant (Luby step=1, Stable step=10) + 1 z4-sat dynamic (Vmtf)
        // + 1 z4-sat Luby geometric = 11 total (#4149 + Wave 29 #4299 larger SimpleSolver steps)
        assert_eq!(
            variant_count, 11,
            "SAT-focused portfolio should have 11 variant BMC configs (SimpleSolver #4149 + #4299 step 50/100)"
        );
    }

    #[test]
    fn test_arithmetic_portfolio_includes_z4_variant_bmc() {
        let config = arithmetic_portfolio();
        let variant_count = config
            .engines
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    EngineConfig::BmcZ4Variant { .. }
                        | EngineConfig::BmcZ4VariantDynamic { .. }
                )
            })
            .count();
        assert_eq!(
            variant_count, 2,
            "arithmetic portfolio should have 2 z4-sat variant BMC configs"
        );
    }

    /// z4-sat variant and default z4-sat BMC should agree on a 2-step counter.
    #[test]
    fn test_portfolio_z4_variant_default_agree_two_step_counter() {
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();

        // z4-sat default BMC
        let default_config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Bmc { step: 1 }],
            max_depth: 10,
            preprocess: Default::default(),
        };
        let default_result = portfolio_check_detailed(&circuit, default_config);

        // z4-sat Luby variant BMC
        let luby_config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::BmcZ4Variant {
                step: 1,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            }],
            max_depth: 10,
            preprocess: Default::default(),
        };
        let luby_result = portfolio_check_detailed(&circuit, luby_config);

        // Both should find Unsafe at depth 2.
        assert!(
            matches!(default_result.result, CheckResult::Unsafe { depth: 2, .. }),
            "z4-sat default BMC: {default_result:?}"
        );
        assert!(
            matches!(luby_result.result, CheckResult::Unsafe { depth: 2, .. }),
            "z4-sat Luby BMC: {luby_result:?}"
        );
    }

    // -------------------------------------------------------------------
    // z4-sat variant k-induction portfolio tests
    // -------------------------------------------------------------------

    #[test]
    fn test_portfolio_kind_z4_luby_proves_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::KindZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Luby,
            }],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "z4-sat Luby kind should prove Safe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_kind_z4_luby_finds_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::KindZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Luby,
            }],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "z4-sat Luby kind should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_kind_skip_bmc_z4_luby_proves_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::KindSkipBmcZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Luby,
            }],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "z4-sat Luby kind-skip-bmc should prove Safe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_z4_variant_kind_config_names() {
        assert_eq!(
            EngineConfig::KindZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Luby
            }
            .name(),
            "kind-z4-luby"
        );
        assert_eq!(
            EngineConfig::KindSkipBmcZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Luby
            }
            .name(),
            "kind-skip-bmc-z4-luby"
        );
    }

    #[test]
    fn test_default_portfolio_includes_z4_variant_kind() {
        let config = default_portfolio();
        let variant_kind_count = config
            .engines
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    EngineConfig::KindZ4Variant { .. }
                        | EngineConfig::KindSkipBmcZ4Variant { .. }
                )
            })
            .count();
        assert_eq!(
            variant_kind_count, 3,
            "default portfolio should have 3 z4-sat variant k-induction configs"
        );
    }

    #[test]
    fn test_competition_portfolio_includes_z4_variant_kind() {
        let config = competition_portfolio();
        let variant_kind_count = config
            .engines
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    EngineConfig::KindZ4Variant { .. }
                        | EngineConfig::KindSkipBmcZ4Variant { .. }
                )
            })
            .count();
        // Wave 10: 3 standard variants (Luby/Stable/Vmtf) + 3 skip-bmc variants = 6
        assert_eq!(
            variant_kind_count, 6,
            "competition portfolio should have 6 z4-sat variant k-induction configs"
        );
    }

    // ---------------------------------------------------------------
    // IC3 inn portfolio config tests (#4148)
    // ---------------------------------------------------------------

    #[test]
    fn test_ic3_inn_portfolio_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_inn()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "ic3_inn safe: got {result:?}");
    }

    #[test]
    fn test_ic3_inn_portfolio_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_inn()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "ic3_inn unsafe: got {result:?}"
        );
    }

    #[test]
    fn test_ic3_inn_ctp_portfolio_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_inn_ctp()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "ic3_inn_ctp safe: got {result:?}");
    }

    #[test]
    fn test_ic3_inn_no_ctg_portfolio_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_inn_noctg()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "ic3_inn_no_ctg safe: got {result:?}");
    }

    #[test]
    fn test_ic3_inn_dynamic_portfolio_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_inn_dynamic()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "ic3_inn_dynamic safe: got {result:?}");
    }
}

// -----------------------------------------------------------------------
// Safe result validation tests (#4216)
// -----------------------------------------------------------------------

mod safe_validation_tests {
    use super::*;
    use crate::sat_types::Lit;

    /// IC3 Safe result on a trivially safe circuit passes portfolio validation.
    #[test]
    fn test_portfolio_ic3_safe_passes_validation() {
        // Latch next=0, bad=latch. Latch is always 0, so safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Ic3],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "IC3 should prove Safe and pass validation, got {result:?}"
        );
    }

    /// IC3 Safe result with multiple IC3 configs all pass validation.
    #[test]
    fn test_portfolio_ic3_variants_safe_pass_validation() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        for config_fn in [ic3_conservative, ic3_ctp, ic3_inf, ic3_full] {
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![config_fn()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Safe),
                "{} should prove Safe and pass validation, got {result:?}",
                config_fn().name()
            );
        }
    }

    /// verify_safe_invariant on a trivially safe Transys with empty lemmas succeeds.
    #[test]
    fn test_verify_safe_invariant_empty_lemmas() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = ts.verify_safe_invariant(&[]);
        assert!(result.is_ok(), "empty lemmas should pass: {result:?}");
    }

    /// verify_safe_invariant with a valid invariant lemma.
    /// Circuit: latch L starts at 0, next = 0, bad = L.
    /// The invariant is just [!L] (latch is always false).
    #[test]
    fn test_verify_safe_invariant_valid_lemma() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        // Latch var is Var(1). Lemma: [!L] = [Lit::neg(Var(1))].
        let latch_var = ts.latch_vars[0];
        let lemma = vec![Lit::neg(latch_var)];
        let result = ts.verify_safe_invariant(&[lemma]);
        assert!(result.is_ok(), "valid invariant should pass: {result:?}");
    }

    /// verify_safe_invariant with a lemma that violates Init => Inv.
    /// If we claim the invariant is [L] (latch is true), but init sets L=0,
    /// then Init => Inv should fail.
    #[test]
    fn test_verify_safe_invariant_fails_init() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let latch_var = ts.latch_vars[0];
        // Bogus lemma: [L] (latch is true), but init says L=0.
        let lemma = vec![Lit::pos(latch_var)];
        let result = ts.verify_safe_invariant(&[lemma]);
        assert!(result.is_err(), "invariant violating Init should fail");
        let err = result.unwrap_err();
        assert!(
            err.contains("Init => Inv FAILED"),
            "error should mention Init check: {err}"
        );
    }

    /// verify_safe_invariant with a lemma that violates Inv => !Bad.
    /// Circuit: latch L starts at 0, next = 0 (always stays 0), bad = NOT L.
    /// If we claim invariant is [!L] (latch=0), it passes Init (L=0) and
    /// consecution (next=0 preserves L'=0), but bad = !L is true when L=0,
    /// so Inv AND Bad is SAT.
    #[test]
    fn test_verify_safe_invariant_fails_bad() {
        // aag 1 0 1 0 0 1
        // latch: var=1, next=0 (constant false, latch stays 0)
        // bad = 3 (= NOT var1 = NOT L)
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n3\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let latch_var = ts.latch_vars[0];
        // Lemma [!L] — latch is 0. Passes Init (L init=0) and consecution
        // (next=0, so L'=0, !L' holds). But bad = !L, so Inv AND Bad is SAT.
        let lemma = vec![Lit::neg(latch_var)];
        let result = ts.verify_safe_invariant(&[lemma]);
        assert!(result.is_err(), "invariant allowing bad state should fail");
        let err = result.unwrap_err();
        assert!(
            err.contains("Inv => !Bad FAILED"),
            "error should mention Bad check: {err}"
        );
    }

    /// verify_safe_invariant with a lemma that violates consecution (Inv AND T => Inv').
    /// Circuit: latch L starts at 0, next = NOT L, bad = L.
    /// If we claim invariant is [!L] (latch=0), but next = NOT L = 1,
    /// then in the next state L'=1, so the lemma [!L'] is violated.
    #[test]
    fn test_verify_safe_invariant_fails_consecution() {
        // Toggle circuit: latch starts 0, next = NOT latch, bad = latch.
        // Invariant [!L] holds at init but is NOT inductive (next state has L'=1).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let latch_var = ts.latch_vars[0];
        let lemma = vec![Lit::neg(latch_var)];
        let result = ts.verify_safe_invariant(&[lemma]);
        assert!(
            result.is_err(),
            "non-inductive invariant should fail consecution"
        );
        let err = result.unwrap_err();
        assert!(
            err.contains("Inv AND T => Inv' FAILED"),
            "error should mention consecution: {err}"
        );
    }
}

#[test]
fn test_cross_validate_safe_loses_to_unsafe() {
    let candidate_safe = PortfolioResult {
        result: CheckResult::Safe,
        solver_name: "kind".into(),
        time_secs: 0.12,
    };
    let unsafe_result = PortfolioResult {
        result: CheckResult::Unsafe {
            depth: 0,
            trace: vec![rustc_hash::FxHashMap::default()],
        },
        solver_name: "bmc-1".into(),
        time_secs: 0.19,
    };

    let winner = super::runner::cross_validate_safe_result(
        candidate_safe,
        vec![unsafe_result.clone()],
    );

    assert!(matches!(&winner.result, CheckResult::Unsafe { depth: 0, .. }));
    assert_eq!(winner.solver_name.as_str(), "bmc-1");
    assert_eq!(winner.time_secs, unsafe_result.time_secs);
}

#[test]
fn test_cross_validate_safe_alone() {
    let candidate_safe = PortfolioResult {
        result: CheckResult::Safe,
        solver_name: "kind".into(),
        time_secs: 0.12,
    };

    let winner =
        super::runner::cross_validate_safe_result(candidate_safe.clone(), vec![]);

    assert!(matches!(&winner.result, CheckResult::Safe));
    assert_eq!(winner.solver_name.as_str(), candidate_safe.solver_name.as_str());
    assert_eq!(winner.time_secs, candidate_safe.time_secs);
}

#[test]
fn test_cross_validate_safe_agrees_with_another_safe() {
    let candidate_safe = PortfolioResult {
        result: CheckResult::Safe,
        solver_name: "kind".into(),
        time_secs: 0.12,
    };
    let confirming_safe = PortfolioResult {
        result: CheckResult::Safe,
        solver_name: "ic3-default".into(),
        time_secs: 0.17,
    };

    let winner = super::runner::cross_validate_safe_result(
        candidate_safe.clone(),
        vec![confirming_safe],
    );

    assert!(matches!(&winner.result, CheckResult::Safe));
    assert_eq!(winner.solver_name.as_str(), candidate_safe.solver_name.as_str());
    assert_eq!(winner.time_secs, candidate_safe.time_secs);
}

// =====================================================================
// #4315 Safe-result cross-validation — portfolio integration tests.
//
// These exercise the `validate_safe` hook wired into `runner::portfolio_check`.
// The direct unit tests for the validator live in `portfolio::safe_witness`;
// here we confirm the hook fires at the right time through the real portfolio
// code path without rejecting legitimate results.
// =====================================================================

/// #4315 integration: legitimate IC3 Safe verdict must survive
/// `validate_safe`. IC3 emits an inductive invariant (`Ic3Result::Safe`
/// with `lemmas`) that is re-checked by a fresh independent SAT backend.
/// A correct invariant must pass all three consecution checks
/// (init => inv, inv & T => inv', inv => !bad) and be accepted.
#[test]
fn test_portfolio_safe_validation_ic3_inductive_accepted() {
    // Latch next=0, bad=latch — trivially safe. IC3 produces a small
    // inductive invariant that `validate_safe` independently verifies.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(10),
        engines: vec![EngineConfig::Ic3],
        max_depth: 100,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Safe),
        "IC3 inductive invariant should be accepted by validate_safe, got {result:?}"
    );
}

/// #4315 integration: Kind-only Safe verdict is accepted via the
/// `EngineVerified` path (Kind's internal k-induction proof is trusted
/// but logged — there's no formal witness to independently re-check).
/// Regresses if a future refactor conservatively downgrades
/// `SafeWitness::EngineVerified` to `Unwitnessed`.
#[test]
fn test_portfolio_safe_validation_kind_engine_verified_accepted() {
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(10),
        engines: vec![EngineConfig::Kind],
        max_depth: 10,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Safe),
        "Kind engine-verified Safe must not be downgraded by validate_safe, got {result:?}"
    );
}

/// #4315 integration: validator does NOT mask genuine Unsafe verdicts.
/// The hook is scoped to `CheckResult::Safe` arms only — an Unsafe (SAT)
/// outcome must pass through unchanged. Protects against a refactor that
/// accidentally wraps the wrong result arm.
#[test]
fn test_portfolio_safe_validation_does_not_mask_unsafe() {
    // Latch next=!latch, bad=latch — reachable in 1 step.
    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
    let config = PortfolioConfig {
        timeout: Duration::from_secs(5),
        engines: vec![EngineConfig::Bmc { step: 1 }, EngineConfig::Ic3],
        max_depth: 10,
        preprocess: Default::default(),
    };
    let result = portfolio_check(&circuit, config);
    assert!(
        matches!(result, CheckResult::Unsafe { .. }),
        "validate_safe must not interfere with Unsafe verdicts, got {result:?}"
    );
}

/// #4315 integration: `validate_safe_with_budget` direct-call smoke test —
/// builds a real Transys from a trivially-safe circuit and confirms the
/// engine-verified variant is Accepted end-to-end on production input.
/// Complements the in-module unit tests by constructing the Transys
/// through the full preprocess/parse pipeline.
#[test]
fn test_validate_safe_on_real_transys_engine_verified() {
    use super::safe_witness::{validate_safe, SafeValidation, SafeWitness};

    let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
    let ts = Transys::from_aiger(&circuit);
    let witness = SafeWitness::EngineVerified { engine: "k-induction" };
    let outcome = validate_safe(&witness, &ts);
    assert!(
        matches!(outcome, SafeValidation::Accepted),
        "EngineVerified witness should be Accepted on real Transys, got {outcome:?}"
    );
}
