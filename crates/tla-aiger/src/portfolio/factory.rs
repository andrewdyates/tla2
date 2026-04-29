// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-defined IC3 configurations, portfolio presets, and engine factory functions.

use std::time::Duration;

use super::config::{EngineConfig, PortfolioConfig};
use crate::ic3::{GeneralizationOrder, Ic3Config, RestartStrategy, ValidationStrategy};

// ---------------------------------------------------------------------------
// Pre-defined IC3 configurations (mirroring rIC3's portfolio diversity)
//
// rIC3's bl_default portfolio runs 16 engines total:
//   11 IC3 configs + 4 BMC configs + 1 k-induction
// Each IC3 config varies: ctg on/off, ctg_max, ctg_limit, ctp, internal
// signals (inn), drop_po, random seed.
//
// We mirror the most impactful axes:
//   - Feature toggles: ctp, inf_frame, internal_signals, ternary_reduce
//   - CTG tuning: ctg_max (3 vs 5), ctg_limit (1 vs 15)
//   - CTP tuning: ctp_max
//   - Random seed diversity: each config gets a unique seed
// ---------------------------------------------------------------------------

/// IC3 with all optimizations off (conservative baseline).
/// Mirrors rIC3's `ic3 --rseed 1`. Best single-config performance on many benchmarks.
pub fn ic3_conservative() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            random_seed: 1,
            ..Ic3Config::default()
        },
        name: "ic3-conservative".into(),
    }
}

/// IC3 with Counter-To-Propagation enabled.
/// CTP strengthens frames during propagation, helping benchmarks where
/// lemma push-through is the bottleneck.
/// Mirrors rIC3's `ic3_inn_ctp` (CTP is paired with internal signals in rIC3).
pub fn ic3_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            random_seed: 2,
            ..Ic3Config::default()
        },
        name: "ic3-ctp".into(),
    }
}

/// IC3 with infinity frame promotion.
/// Globally-inductive lemmas are promoted and never re-propagated,
/// reducing work on deep induction chains.
pub fn ic3_inf() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            inf_frame: true,
            random_seed: 3,
            ..Ic3Config::default()
        },
        name: "ic3-inf".into(),
    }
}

/// IC3 with internal signals (AND gate variables in cubes).
/// FMCAD'21 technique: including internal signals in cubes can help
/// generalization on circuits with complex combinational logic.
/// Mirrors rIC3's `ic3_inn` configuration.
pub fn ic3_internal() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            random_seed: 4,
            ..Ic3Config::default()
        },
        name: "ic3-internal".into(),
    }
}

/// IC3 with ternary simulation pre-reduction.
/// Ternary simulation quickly identifies don't-care literals in bad cubes,
/// reducing cube size before the expensive MIC generalization loop.
pub fn ic3_ternary() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ternary_reduce: true,
            random_seed: 5,
            ..Ic3Config::default()
        },
        name: "ic3-ternary".into(),
    }
}

/// IC3 with all optimizations enabled (aggressive mode).
/// Combines CTP, infinity frame, internal signals, and ternary reduction.
/// May be the fastest on some benchmarks, but the overhead of all
/// optimizations together can hurt on others.
pub fn ic3_full() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            random_seed: 6,
            ..Ic3Config::default()
        },
        name: "ic3-full".into(),
    }
}

/// IC3 with CTP + infinity frame (best for deep safety proofs).
pub fn ic3_ctp_inf() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            random_seed: 7,
            ..Ic3Config::default()
        },
        name: "ic3-ctp-inf".into(),
    }
}

/// IC3 with internal signals + ternary reduce (best for complex combinational logic).
pub fn ic3_internal_ternary() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            ternary_reduce: true,
            random_seed: 8,
            ..Ic3Config::default()
        },
        name: "ic3-internal-ternary".into(),
    }
}

/// IC3 with aggressive CTG limits (deep generalization).
/// Mirrors rIC3's `ic3_ctg_limit` with `--ctg-max 5 --ctg-limit 15`.
/// Higher limits allow deeper counterexample blocking during MIC,
/// producing shorter lemmas at the cost of more SAT calls per literal drop.
/// Complements the conservative config which uses ctg_max=3, ctg_limit=1.
pub fn ic3_deep_ctg() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 5,
            ctg_limit: 15,
            random_seed: 9,
            ..Ic3Config::default()
        },
        name: "ic3-deep-ctg".into(),
    }
}

/// IC3 with internal signals + CTP.
/// Mirrors rIC3's `ic3_inn_ctp` — combining CTP with internal signals often
/// excels on circuits with deep combinational logic where both shorter
/// cubes (from internal signals) and stronger propagation (from CTP) help.
pub fn ic3_internal_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            ctp: true,
            random_seed: 10,
            ..Ic3Config::default()
        },
        name: "ic3-internal-ctp".into(),
    }
}

/// IC3 with deep CTG + internal signals.
/// Combines aggressive generalization (ctg_max=5, ctg_limit=15) with
/// internal signal cubes, targeting circuits where standard IC3 produces
/// overly specific lemmas.
pub fn ic3_deep_ctg_internal() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 5,
            ctg_limit: 15,
            internal_signals: true,
            random_seed: 11,
            ..Ic3Config::default()
        },
        name: "ic3-deep-ctg-internal".into(),
    }
}

/// IC3 with ternary reduction + infinity frame + unique seed.
/// Lightweight preprocessing (ternary) plus global lemma promotion (inf),
/// a complementary combination not covered by other configs.
pub fn ic3_ternary_inf() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ternary_reduce: true,
            inf_frame: true,
            random_seed: 12,
            ..Ic3Config::default()
        },
        name: "ic3-ternary-inf".into(),
    }
}

/// IC3 with aggressive CTP (max 5 attempts).
/// Higher CTP limit for propagation-bound benchmarks where the default
/// ctp_max=3 is insufficient to push all lemmas through.
pub fn ic3_aggressive_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            random_seed: 13,
            ..Ic3Config::default()
        },
        name: "ic3-aggressive-ctp".into(),
    }
}

/// IC3 with deep CTG + CTP (strongest generalization + propagation combo).
/// Combines aggressive CTG (ctg_max=5, ctg_limit=15) with CTP for benchmarks
/// where both generalization and propagation are bottlenecks. This is the
/// configuration closest to rIC3's strongest single-engine mode.
pub fn ic3_deep_ctg_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 5,
            ctg_limit: 15,
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            random_seed: 14,
            ..Ic3Config::default()
        },
        name: "ic3-deep-ctg-ctp".into(),
    }
}

/// IC3 with all features plus high seed (maximum diversity).
/// Identical feature set to ic3_full but with a different random seed,
/// providing complementary MIC literal orderings. On many benchmarks,
/// the best-performing config depends on literal ordering luck —
/// two identical feature sets with different seeds often solve different
/// subsets of benchmarks.
pub fn ic3_full_alt_seed() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            random_seed: 15,
            ..Ic3Config::default()
        },
        name: "ic3-full-alt".into(),
    }
}

/// IC3 with internal signals + deep CTG + CTP + ternary (kitchen sink, high seed).
/// The most aggressive configuration in the portfolio. Combines every
/// optimization axis. Expensive per-step but can solve the hardest benchmarks
/// that no single optimization can crack.
pub fn ic3_kitchen_sink() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            ctg_max: 5,
            ctg_limit: 15,
            random_seed: 16,
            ..Ic3Config::default()
        },
        name: "ic3-kitchen-sink".into(),
    }
}

/// IC3 with CTG-down MIC variant.
/// Uses the flip-based cube shrinking from rIC3's `ctg_down()` instead of
/// standard literal dropping. More aggressive generalization that can remove
/// multiple literals at once by using the SAT model to guide shrinking.
/// Reference: rIC3 mic.rs:122 — `ctg_down()`.
pub fn ic3_ctg_down() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_down: true,
            random_seed: 17,
            ..Ic3Config::default()
        },
        name: "ic3-ctg-down".into(),
    }
}

/// IC3 with CTG-down + CTP + inf (aggressive generalization + propagation).
/// Combines the flip-based MIC with CTP and infinity frame for maximum
/// generalization effectiveness.
pub fn ic3_ctg_down_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_down: true,
            ctp: true,
            inf_frame: true,
            random_seed: 18,
            ..Ic3Config::default()
        },
        name: "ic3-ctg-down-ctp".into(),
    }
}

/// IC3 with dynamic generalization (GAP-5).
/// Adaptively adjusts CTG parameters based on proof obligation activity.
/// High-activity POs get more aggressive generalization, while easy POs
/// use minimal overhead. Combined with drop_po (enabled by default).
/// Reference: rIC3 block.rs:129-159 — dynamic MicType selection.
pub fn ic3_dynamic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            dynamic: true,
            random_seed: 19,
            ..Ic3Config::default()
        },
        name: "ic3-dynamic".into(),
    }
}

/// IC3 with dynamic generalization + CTP + infinity frame.
/// The dynamic+CTP combination is strong: dynamic adjusts generalization
/// effort per-cube, while CTP strengthens frames during propagation.
pub fn ic3_dynamic_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            dynamic: true,
            ctp: true,
            inf_frame: true,
            random_seed: 20,
            ..Ic3Config::default()
        },
        name: "ic3-dynamic-ctp".into(),
    }
}

/// IC3 with dynamic generalization + internal signals.
/// Dynamic CTG adapts to per-cube difficulty while internal signals
/// provide richer cubes for generalization.
pub fn ic3_dynamic_internal() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            dynamic: true,
            internal_signals: true,
            random_seed: 21,
            ..Ic3Config::default()
        },
        name: "ic3-dynamic-internal".into(),
    }
}

/// IC3 tuned for arithmetic circuits (adders, multipliers, counters).
///
/// Arithmetic circuits have specific characteristics that benefit from:
/// - **Deep CTG** (ctg_max=5, ctg_limit=15): arithmetic invariants often
///   require aggressive generalization across carry chain boundaries.
/// - **Internal signals**: carry chain AND gate outputs provide useful
///   generalization anchors.
/// - **CTP**: propagation is the bottleneck on deep arithmetic circuits
///   where lemmas must be pushed through many carry-dependent frames.
/// - **Ternary reduce**: carry chains create many don't-care bits.
/// - **Dynamic generalization**: arithmetic cubes vary greatly in difficulty
///   (simple constant propagation vs. full carry chain reasoning).
///
/// This config is selected automatically when circuit analysis detects
/// XOR/carry chain patterns (see `preprocess::xor_detect`).
pub fn ic3_arithmetic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            ctg_max: 5,
            ctg_limit: 15,
            dynamic: true,
            random_seed: 100,
            blocking_budget: 500,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic".into(),
    }
}

/// IC3 for arithmetic circuits with CTG-down MIC variant.
///
/// Combines the arithmetic-tuned parameters with CTG-down's aggressive
/// model-based cube shrinking. On arithmetic circuits, CTG-down can
/// remove multiple carry-chain-dependent literals at once by using the
/// SAT model to identify which literals are actually relevant.
pub fn ic3_arithmetic_ctg_down() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            ctg_down: true,
            random_seed: 101,
            blocking_budget: 500,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-ctg-down".into(),
    }
}

/// IC3 for arithmetic circuits without internal signals (diversity).
///
/// Some arithmetic benchmarks perform better without internal signals
/// because the carry chain AND gates add too many variables to cubes.
/// This provides portfolio diversity against the full arithmetic config.
pub fn ic3_arithmetic_no_internal() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: false,
            ternary_reduce: true,
            ctg_max: 5,
            ctg_limit: 15,
            dynamic: true,
            random_seed: 102,
            blocking_budget: 500,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-no-internal".into(),
    }
}

/// IC3 for arithmetic circuits with conservative MIC (#4072).
///
/// Arithmetic circuits have carry chain dependencies that make per-literal
/// MIC drops expensive and mostly futile. This config:
/// - **No CTG** (ctg_max=0): carry chain predecessors are numerous and
///   structured — CTG wastes SAT calls trying to block them.
/// - **MIC drop budget = 100**: limits the literal-drop loop to 100 SAT calls.
///   UNSAT core reduction (Phase 1) typically removes 30-60% of literals for
///   free; the budget catches truly independent bits but avoids carry chain
///   thrashing.
/// - **Blocking budget = 200**: limits bad-state discoveries per depth to force
///   frame advancement. Core-only lemmas are weaker, so fewer per depth is OK.
/// - **CTP + inf_frame**: propagation is the bottleneck on deep arithmetic
///   circuits, so these features accelerate convergence via frame strengthening.
/// - **No internal signals**: carry chain AND gates add variables that increase
///   cube size without improving generalization quality.
///
/// This is the key convergence fix: standard MIC on a 32-bit counter wastes
/// 32+ SAT calls per cube discovering that every bit is essential. With a
/// budget of 100, MIC returns the core-reduced cube after ~100 calls and IC3
/// makes progress instead of thrashing.
pub fn ic3_arithmetic_conservative() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: false,
            ternary_reduce: true,
            ctg_max: 0,
            ctg_limit: 0,
            dynamic: false,
            mic_drop_budget: 100,
            blocking_budget: 200,
            random_seed: 103,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-conservative".into(),
    }
}

/// IC3 for arithmetic circuits with tight MIC budget + dynamic (#4072).
///
/// Variant of conservative mode with dynamic generalization enabled.
/// Dynamic CTG is activity-aware: low-activity POs (common on first encounter
/// of arithmetic cubes) get zero CTG, while high-activity POs (thrashing cubes
/// that keep reappearing) get aggressive CTG. Combined with the MIC budget
/// and blocking budget, this avoids wasting SAT calls on easy cubes while
/// investing more effort in persistently difficult ones.
pub fn ic3_arithmetic_tight_budget() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: false,
            ternary_reduce: true,
            ctg_max: 2,
            ctg_limit: 1,
            dynamic: true,
            mic_drop_budget: 50,
            blocking_budget: 300,
            random_seed: 104,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-tight-budget".into(),
    }
}

/// IC3 for arithmetic circuits: core-only MIC (#4072).
///
/// The most aggressive budget configuration: mic_drop_budget=1 means the
/// literal-drop loop effectively does nothing beyond the UNSAT core reduction
/// (which happens in Phase 1, before the drop loop). This produces slightly
/// weaker lemmas but runs extremely fast per-cube, letting IC3 explore more
/// frames and find the invariant through quantity rather than quality of
/// individual lemmas.
///
/// Blocking budget = 100 to force rapid frame advancement. The strategy is
/// quantity over quality: many weak lemmas across many frames, relying on
/// propagation to merge and strengthen them.
///
/// Best for deep arithmetic circuits (Fibonacci, counters) where the invariant
/// involves many correlated bits and per-literal dropping is futile.
pub fn ic3_arithmetic_core_only() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 3,
            inf_frame: true,
            internal_signals: false,
            ternary_reduce: true,
            ctg_max: 0,
            ctg_limit: 0,
            dynamic: false,
            mic_drop_budget: 1,
            blocking_budget: 100,
            random_seed: 105,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-core-only".into(),
    }
}

/// IC3 with 2-ordering lift for tighter generalizations (#4099).
///
/// After the standard Activity-ordered MIC pass, tries a second pass with
/// ReverseTopological ordering and keeps the shorter result. This is only
/// done when the first pass didn't reduce the cube much (> half original)
/// and the circuit has > 15 latches.
///
/// The complementary ordering explores a fundamentally different
/// generalization path through the search space, often finding literals
/// that Activity-based ordering misses because they have moderate
/// VSIDS scores but are structurally redundant.
pub fn ic3_multi_order() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::Activity,
            multi_lift_orderings: 2,
            random_seed: 110,
            ..Ic3Config::default()
        },
        name: "ic3-multi-order".into(),
    }
}

/// IC3 with 2-ordering lift + CTP + infinity frame (#4099).
///
/// Combines the multi-ordering lift with CTP and infinity frame for
/// stronger propagation. The multi-ordering lift produces tighter lemmas,
/// and CTP + inf_frame push those lemmas further forward, accelerating
/// convergence.
pub fn ic3_multi_order_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            gen_order: GeneralizationOrder::Activity,
            multi_lift_orderings: 2,
            random_seed: 111,
            ..Ic3Config::default()
        },
        name: "ic3-multi-order-ctp".into(),
    }
}

/// IC3 with 3-ordering lift (maximum diversity) + CTP + infinity frame (#4099).
///
/// Tries all three ordering strategies: Activity, ReverseTopological, and
/// RandomShuffle. Maximum generalization diversity at the cost of up to 3x
/// MIC calls on cubes where the first ordering underperforms.
///
/// Best for hard benchmarks where tight lemmas are critical for convergence.
pub fn ic3_multi_order_full() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            gen_order: GeneralizationOrder::Activity,
            multi_lift_orderings: 3,
            random_seed: 112,
            ..Ic3Config::default()
        },
        name: "ic3-multi-order-full".into(),
    }
}

/// IC3 with internal signals only (#4148).
///
/// Mirrors rIC3's vanilla `--inn` flag: extends the MIC variable domain to
/// include AND-gate outputs so generalization operates over latches + internal
/// signals. No other features enabled — pure internal signal diversity.
pub fn ic3_inn() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            random_seed: 150,
            ..Ic3Config::default()
        },
        name: "ic3-inn".into(),
    }
}

/// IC3 with internal signals + CTP (#4148).
///
/// Mirrors rIC3's `ic3_inn_ctp`: combining CTP propagation with internal
/// signals provides both stronger propagation (CTP pushes lemmas forward)
/// and richer generalization (internal signals in cubes). The combination
/// is particularly effective on arithmetic circuits with carry chains.
pub fn ic3_inn_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            ctp: true,
            inf_frame: true,
            random_seed: 151,
            ..Ic3Config::default()
        },
        name: "ic3-inn-ctp".into(),
    }
}

/// IC3 with internal signals, no CTG (#4148).
///
/// Mirrors rIC3's `ic3_inn_noctg`: internal signals for richer cubes but
/// CTG disabled (ctg_max=0) to avoid over-generalization.
pub fn ic3_inn_noctg() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            ctg_max: 0,
            ctg_limit: 0,
            random_seed: 152,
            ..Ic3Config::default()
        },
        name: "ic3-inn-noctg".into(),
    }
}

/// IC3 with internal signals + dynamic generalization (#4148).
///
/// Mirrors rIC3's `ic3_inn_dynamic`: internal signals + dynamic CTG that
/// adapts based on proof obligation activity.
pub fn ic3_inn_dynamic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            dynamic: true,
            drop_po: false,
            random_seed: 153,
            ..Ic3Config::default()
        },
        name: "ic3-inn-dynamic".into(),
    }
}

// ---------------------------------------------------------------------------
// inn-proper portfolio configs (#4308): promote internal signals to first-class
// latches (FMCAD'21). Mutually exclusive with the `internal_signals` cube-
// extension variant above — these set `inn_proper=true, internal_signals=false`.
// ---------------------------------------------------------------------------

/// IC3 with inn-proper: promote internal signals to latches (#4308).
///
/// Matches rIC3's `--inn` at the state-variable basis: AND-gate outputs that
/// do not depend on primary inputs are promoted to first-class latches with
/// next-state derived from the 1-step unrolled relation. IC3 frames become
/// clauses over `latches ∪ promoted_signals`, yielding structurally smaller
/// inductive invariants on arithmetic-heavy circuits (cal14, cal42, diffeq,
/// counter_bit_width_small).
pub fn ic3_inn_proper() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            inn_proper: true,
            random_seed: 160,
            ..Ic3Config::default()
        },
        name: "ic3-inn-proper".into(),
    }
}

/// IC3 with inn-proper + CTP (#4308).
///
/// Combines latch promotion with CTP propagation. The richer state basis
/// shortens lemmas; CTP pushes them through frames more aggressively.
pub fn ic3_inn_proper_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            inn_proper: true,
            ctp: true,
            inf_frame: true,
            random_seed: 161,
            ..Ic3Config::default()
        },
        name: "ic3-inn-proper-ctp".into(),
    }
}

/// IC3 with inn-proper, no CTG (#4308).
///
/// Latch promotion without counterexample-to-generalization. On circuits where
/// the richer state basis already produces concise lemmas, skipping CTG avoids
/// over-generalization overhead.
pub fn ic3_inn_proper_noctg() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            inn_proper: true,
            ctg_max: 0,
            ctg_limit: 0,
            random_seed: 162,
            ..Ic3Config::default()
        },
        name: "ic3-inn-proper-noctg".into(),
    }
}

/// IC3 with SimpleSolver backend for high-constraint-ratio circuits (#4092).
///
/// z4-sat produces FINALIZE_SAT_FAIL on circuits with high constraint-to-latch
/// ratios (e.g., NTU microban Sokoban puzzles with 100-300+ constraints on
/// 30-60 latches). The cross-check fallback mechanism in block.rs eventually
/// switches to SimpleSolver, but wastes several seconds on z4-sat failures
/// first. This config starts with SimpleSolver from the beginning.
///
/// SimpleSolver is a simple DPLL solver without CDCL or preprocessing.
/// It is slower per-query than z4-sat on most benchmarks, but never produces
/// false UNSAT or FINALIZE_SAT_FAIL. On high-constraint benchmarks where
/// z4-sat spends most of its time on error recovery, SimpleSolver is faster.
///
/// CTP + inf enabled for convergence. Full Auto validation required --
/// SkipConsecution is unsound in portfolio mode because the portfolio
/// accepts the first definitive result without waiting for a validating
/// member. microban_64/82/110/132/136/149/89 false UNSAT was caused by
/// ic3-simple-solver with SkipConsecution winning the portfolio race.
pub fn ic3_simple_solver() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ctp: true,
            inf_frame: true,
            random_seed: 160,
            validation_strategy: ValidationStrategy::Auto,
            crosscheck_disabled: true,
            ..Ic3Config::default()
        },
        name: "ic3-simple-solver".into(),
    }
}

/// Minimal-overhead IC3 config for very small circuits (<30 latches) (#4259, #4288).
///
/// Small circuits like cal14 (23 latches, 1656 trans clauses) solve in
/// sub-second time with rIC3 but previously timed out in tla-aiger due to
/// cross-check overhead and aggressive CTG recursion. This config forces
/// the minimal rIC3-equivalent baseline:
/// - Cross-check disabled (bypassed anyway by config.rs small-circuit gate)
/// - Minimal CTG (ctg_max=3, ctg_limit=1 — rIC3 defaults, no recursion)
/// - Predprop off (backward analysis adds overhead on trivial circuits)
/// - Internal signals off (AND-gate vars inflate cube size)
/// - drop_po off (keep all obligations — we expect few)
/// - dynamic off (no activity-based per-PO CTG scaling)
/// - parent_lemma/parent_lemma_mic off (no structural reuse)
/// - mic_drop_budget = 50 (cap MIC work per lemma; small circuits don't need more)
/// - bucket_queue_restarts = 0 (start directly in bucket-queue VSIDS for
///   fast O(1) variable selection on short queries)
pub fn ic3_small_circuit() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: false,
            inf_frame: true,
            internal_signals: false,
            ctg_max: 3,
            ctg_limit: 1,
            circuit_adapt: false,
            ctg_down: false,
            predprop: false,
            drop_po: false,
            dynamic: false,
            parent_lemma: false,
            parent_lemma_mic: false,
            mic_drop_budget: 50,
            mic_attempts: 0,
            bucket_queue_restarts: 0,
            random_seed: 200,
            crosscheck_disabled: true,
            validation_strategy: ValidationStrategy::Auto,
            // #4259 / z4#8802: disable domain-restricted SAT on small circuits
            // so z4-sat falls back to plain BCP (search_propagate_standard)
            // instead of the slow propagate_domain_bcp path. rIC3 solves the
            // Tier 1 benchmarks (cal14, cal42, loopv3, microban_1_UNSAT) in
            // <0.15s using plain BCP; tla-aiger times out at 100s+ with
            // domain restriction active.
            small_circuit_mode: true,
            ..Ic3Config::default()
        },
        name: "ic3-small-circuit".into(),
    }
}

/// IC3 with SimpleSolver + internal signals for high-constraint circuits (#4092).
///
/// Combines the SimpleSolver backend (no false UNSAT) with internal signals
/// for richer cubes. On constraint-heavy circuits where z4-sat fails,
/// this provides a complementary IC3 path with different generalization
/// behavior.
pub fn ic3_simple_solver_inn() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Simple,
            internal_signals: true,
            ctp: true,
            inf_frame: true,
            random_seed: 161,
            validation_strategy: ValidationStrategy::Auto,
            crosscheck_disabled: true,
            ..Ic3Config::default()
        },
        name: "ic3-simple-solver-inn".into(),
    }
}

/// Portfolio optimized for arithmetic circuits.
///
/// Arithmetic circuits (adders, multipliers, counters) have deep
/// combinational logic with regular carry chain structure. This portfolio:
/// - Includes 3 arithmetic-tuned IC3 configs (with/without internal signals, CTG-down)
/// - Includes 3 conservative MIC configs for carry-chain-heavy circuits (#4072)
/// - Includes 4 internal signal (--inn) IC3 variants for arithmetic generalization (#4148)
/// - Adds 4 general IC3 configs for diversity
/// - Uses deeper BMC (max_depth=50000) since arithmetic bugs often require depth
/// - Includes more BMC variants (step sizes 1, 10, 65, 200 for very deep bugs)
/// - k-induction with skip-bmc (induction is effective on regular arithmetic)
///
/// Selected automatically when `analyze_circuit().is_arithmetic` is true.
pub fn arithmetic_portfolio() -> PortfolioConfig {
    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines: vec![
            // Arithmetic-tuned IC3 (3 configs)
            ic3_arithmetic(),
            ic3_arithmetic_ctg_down(),
            ic3_arithmetic_no_internal(),
            // Conservative MIC configs for carry-chain circuits (#4072, 3 configs)
            ic3_arithmetic_conservative(),
            ic3_arithmetic_tight_budget(),
            ic3_arithmetic_core_only(),
            // Internal signal IC3 variants for arithmetic generalization (#4148, 4 configs)
            ic3_inn(),
            ic3_inn_ctp(),
            ic3_inn_noctg(),
            ic3_inn_dynamic(),
            // General IC3 for diversity (4 configs)
            ic3_conservative(),
            ic3_deep_ctg_ctp(),
            ic3_dynamic_ctp(),
            ic3_kitchen_sink(),
            // BMC variants with z4-sat (7 default + 2 z4 variant + 1 geometric, #4123)
            EngineConfig::Bmc { step: 1 },
            EngineConfig::Bmc { step: 10 },
            EngineConfig::Bmc { step: 65 },
            EngineConfig::Bmc { step: 200 },
            EngineConfig::Bmc { step: 500 }, // Deep arithmetic bugs (#4123)
            EngineConfig::BmcDynamic,
            // Geometric backoff BMC (#4123)
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 50,
                double_interval: 20,
                max_step: 64,
            },
            // z4-sat variant BMC: Luby restarts + VMTF for diversity
            EngineConfig::BmcZ4Variant {
                step: 10,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            },
            EngineConfig::BmcZ4VariantDynamic {
                backend: crate::sat_types::SolverBackend::Z4Vmtf,
            },
            // k-Induction (2 configs — arithmetic properties are often k-inductive)
            EngineConfig::Kind,
            EngineConfig::KindSkipBmc,
        ],
        max_depth: 50000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// IC3 without drop_po (GAP-2 disabled).
/// Some benchmarks benefit from NOT dropping high-activity POs, because
/// persistent cubes may eventually become blockable after enough lemmas
/// accumulate. This provides portfolio diversity against drop_po-enabled configs.
pub fn ic3_no_drop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: false,
            random_seed: 22,
            ..Ic3Config::default()
        },
        name: "ic3-no-drop".into(),
    }
}

/// IC3 with aggressive drop_po (threshold=10.0).
///
/// Lower threshold drops proof obligations sooner — after ~10 re-encounters
/// instead of the default ~20. Frees solver time on benchmarks with many
/// thrashing cubes at the cost of potentially missing blockable cubes that
/// need more attempts. Complements the default threshold=20.0 and no-drop
/// configs for portfolio diversity.
///
/// Reference: rIC3 portfolio.toml varies drop_po on/off but not threshold;
/// this is a tla-aiger extension for finer-grained PO management.
pub fn ic3_aggressive_drop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: true,
            drop_po_threshold: 10.0,
            random_seed: 170,
            ..Ic3Config::default()
        },
        name: "ic3-aggressive-drop".into(),
    }
}

/// IC3 with conservative drop_po (threshold=40.0).
///
/// Higher threshold keeps proof obligations alive longer — cubes must be
/// re-encountered ~40 times before being dropped. Gives IC3 more chances
/// to block persistent cubes that become blockable after frame lemmas
/// accumulate. Better for benchmarks where patience pays off, worse for
/// benchmarks with many hopeless cubes.
pub fn ic3_conservative_drop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: true,
            drop_po_threshold: 40.0,
            random_seed: 171,
            ..Ic3Config::default()
        },
        name: "ic3-conservative-drop".into(),
    }
}

/// IC3 with aggressive drop + CTP + infinity frame.
///
/// Combines aggressive PO dropping (threshold=10.0) with strong propagation.
/// CTP helps push lemmas forward even when cubes are being dropped aggressively,
/// compensating for the reduced blocking effort per cube.
pub fn ic3_aggressive_drop_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: true,
            drop_po_threshold: 10.0,
            ctp: true,
            inf_frame: true,
            random_seed: 172,
            ..Ic3Config::default()
        },
        name: "ic3-aggressive-drop-ctp".into(),
    }
}

/// IC3 with reverse topological generalization order.
/// Drops output-side latches (deeper in the AND-gate graph) before input-side
/// latches. This can find shorter generalizations on circuits with deep
/// pipelines where output-side latches are more likely to be don't-cares.
pub fn ic3_reverse_topo() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::ReverseTopological,
            random_seed: 23,
            ..Ic3Config::default()
        },
        name: "ic3-reverse-topo".into(),
    }
}

/// IC3 with reverse topological order + CTP + infinity frame.
/// Combines structural ordering with strong propagation for deep pipelines.
pub fn ic3_reverse_topo_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::ReverseTopological,
            ctp: true,
            inf_frame: true,
            random_seed: 24,
            ..Ic3Config::default()
        },
        name: "ic3-reverse-topo-ctp".into(),
    }
}

/// IC3 with random shuffle generalization order.
/// Pure diversity: randomized literal ordering avoids systematic biases.
/// Different from seed-based activity perturbation because it completely
/// decouples ordering from VSIDS activity, exploring orthogonal paths.
pub fn ic3_random_shuffle() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::RandomShuffle,
            random_seed: 25,
            ..Ic3Config::default()
        },
        name: "ic3-random-shuffle".into(),
    }
}

/// IC3 with random shuffle + internal signals + deep CTG.
/// Combines randomized ordering with internal signals and aggressive
/// generalization for maximum diversity on complex circuits.
pub fn ic3_random_deep() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::RandomShuffle,
            internal_signals: true,
            ctg_max: 5,
            ctg_limit: 15,
            random_seed: 26,
            ..Ic3Config::default()
        },
        name: "ic3-random-deep".into(),
    }
}

/// IC3 with circuit-size-based CTG adaptation.
/// Automatically adjusts CTG aggressiveness based on circuit size:
/// small circuits get deep CTG, large circuits get conservative CTG.
/// Combined with CTP and infinity frame for strong baseline.
pub fn ic3_circuit_adapt() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            circuit_adapt: true,
            ctp: true,
            inf_frame: true,
            random_seed: 27,
            ..Ic3Config::default()
        },
        name: "ic3-circuit-adapt".into(),
    }
}

/// IC3 with circuit adaptation + internal signals + ternary.
/// Circuit-size-aware CTG with richer cubes for broad coverage.
pub fn ic3_circuit_adapt_full() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            circuit_adapt: true,
            ctp: true,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            random_seed: 28,
            ..Ic3Config::default()
        },
        name: "ic3-circuit-adapt-full".into(),
    }
}

/// IC3 with geometric restart hint + deep CTG.
/// Advisory geometric restart strategy (base=100, factor=1.5) combined
/// with deep CTG. The restart hint serves as a portfolio diversity knob
/// for future z4-sat restart integration.
pub fn ic3_geometric_restart() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            restart_strategy: RestartStrategy::Geometric {
                base: 100,
                factor: 1.5,
            },
            ctg_max: 5,
            ctg_limit: 15,
            random_seed: 29,
            ..Ic3Config::default()
        },
        name: "ic3-geometric-restart".into(),
    }
}

/// IC3 with Luby restart hint + CTP.
/// Advisory Luby restart strategy (unit=512) with CTP propagation.
pub fn ic3_luby_restart() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            restart_strategy: RestartStrategy::Luby { unit: 512 },
            ctp: true,
            inf_frame: true,
            random_seed: 30,
            ..Ic3Config::default()
        },
        name: "ic3-luby-restart".into(),
    }
}

/// IC3 optimized for deep pipelines: reverse topo + deep CTG + internal signals.
/// Targets circuits with long sequential chains where output-side latches
/// are often irrelevant to the property. Deep CTG + internal signals help
/// generalize across pipeline stages.
///
/// Uses blocking_budget=500 (#4074) to force depth advancement on circuits
/// where the blocking phase generates exponentially many cubes at shallow depths.
pub fn ic3_deep_pipeline() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::ReverseTopological,
            ctg_max: 5,
            ctg_limit: 15,
            internal_signals: true,
            ctp: true,
            random_seed: 31,
            blocking_budget: 500,
            ..Ic3Config::default()
        },
        name: "ic3-deep-pipeline".into(),
    }
}

/// IC3 optimized for wide combinational logic: circuit adapt + all features.
/// Targets circuits with wide AND-gate fan-in where domain restriction and
/// ternary simulation are most effective. Circuit adaptation automatically
/// tunes CTG for the circuit's size.
pub fn ic3_wide_comb() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            circuit_adapt: true,
            ternary_reduce: true,
            internal_signals: true,
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            random_seed: 32,
            ..Ic3Config::default()
        },
        name: "ic3-wide-comb".into(),
    }
}

/// IC3 with dynamic generalization + circuit adaptation.
/// Combines per-PO activity-based CTG tuning with per-circuit size-based
/// CTG baseline. The circuit_adapt sets the baseline; dynamic adjusts from
/// there based on individual proof obligation difficulty.
///
/// Uses blocking_budget=300 (#4074) to force depth advancement on circuits
/// where the blocking phase generates exponentially many cubes.
pub fn ic3_dynamic_adapt() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            dynamic: true,
            circuit_adapt: true,
            ctp: true,
            inf_frame: true,
            random_seed: 33,
            blocking_budget: 300,
            ..Ic3Config::default()
        },
        name: "ic3-dynamic-adapt".into(),
    }
}

/// IC3 without preprocessing optimizations (CTG=0, drop_po=false).
///
/// Matches rIC3's `ic3_no_preproc` configuration: disables CTG generalization
/// and proof obligation dropping. Some benchmarks are hurt by aggressive
/// generalization or PO dropping — this variant catches those cases.
///
/// Reference: rIC3 `portfolio.toml` — `ic3_no_preproc` (CTG=false, FRTS=false, SCORR=false, drop_po=false).
pub fn ic3_no_preprocess() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 0,
            ctg_limit: 0,
            drop_po: false,
            parent_lemma: false,
            random_seed: 34,
            ..Ic3Config::default()
        },
        name: "ic3-no-preprocess".into(),
    }
}

/// IC3 without parent lemma heuristic and without drop_po.
///
/// Matches rIC3's `ic3_no_parent` configuration: disables proof obligation
/// dropping and the parent lemma MIC heuristic. The parent lemma biases
/// generalization toward reusing structure from prior lemmas, which can
/// be counterproductive on circuits where fresh generalizations are needed.
///
/// Reference: rIC3 `portfolio.toml` — `ic3_no_parent` (drop_po=false, parent_lemma=false).
pub fn ic3_no_parent() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: false,
            parent_lemma: false,
            random_seed: 35,
            ..Ic3Config::default()
        },
        name: "ic3-no-parent".into(),
    }
}

/// IC3 with parent lemma MIC seeding (CAV'23 #4150).
///
/// Enables the parent lemma MIC seeding optimization: when a proof obligation
/// has a parent, the intersection of the current cube and the parent's blocking
/// lemma is used as a tighter starting point for MIC generalization.
pub fn ic3_parent_mic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            parent_lemma: true,
            parent_lemma_mic: true,
            random_seed: 38,
            ..Ic3Config::default()
        },
        name: "ic3-parent-mic".into(),
    }
}

/// IC3 with parent lemma MIC seeding + CTP + internal signals (CAV'23 #4150).
pub fn ic3_parent_mic_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            parent_lemma: true,
            parent_lemma_mic: true,
            ctp: true,
            inf_frame: true,
            internal_signals: true,
            random_seed: 39,
            ..Ic3Config::default()
        },
        name: "ic3-parent-mic-ctp".into(),
    }
}

/// IC3 with predicate propagation (backward bad-state analysis).
///
/// Uses a backward transition solver to find predecessors of bad states,
/// complementing standard forward IC3. Effective on benchmarks where the
/// property has small backward reachability even if forward analysis struggles.
///
/// Reference: rIC3 `ic3/predprop.rs` — `PredProp` struct (127 LOC).
/// Reference: rIC3 `portfolio.toml` — `ic3_predprop`.
pub fn ic3_predprop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            predprop: true,
            random_seed: 36,
            ..Ic3Config::default()
        },
        name: "ic3-predprop".into(),
    }
}

/// IC3 with predicate propagation + CTP + infinity frame.
///
/// Combines backward analysis with strong forward features: CTP strengthens
/// frame propagation, infinity frame reduces re-propagation, and predprop
/// finds bad predecessors that forward-only analysis might miss.
pub fn ic3_predprop_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            predprop: true,
            ctp: true,
            inf_frame: true,
            random_seed: 37,
            ..Ic3Config::default()
        },
        name: "ic3-predprop-ctp".into(),
    }
}

/// IC3 with predicate propagation + deep CTG + internal signals (#4101).
///
/// Combines backward analysis (predprop) with aggressive generalization
/// (ctg_max=5, ctg_limit=15) and internal signals. The backward solver
/// finds predecessors of bad states that forward IC3 may miss; aggressive
/// CTG then produces tighter blocking lemmas from those predecessors.
/// Internal signals provide richer cubes for generalization over the
/// predecessor states, which often involve complex combinational paths.
///
/// This is a PredProp diversity variant: where `ic3_predprop_ctp` focuses
/// on propagation strength, this config focuses on generalization depth.
pub fn ic3_predprop_deep_ctg() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            predprop: true,
            ctg_max: 5,
            ctg_limit: 15,
            internal_signals: true,
            random_seed: 180,
            ..Ic3Config::default()
        },
        name: "ic3-predprop-deep-ctg".into(),
    }
}

/// IC3 with predicate propagation + dynamic generalization + CTP (#4101).
///
/// Combines backward analysis with per-PO activity-aware CTG tuning and
/// strong propagation. Dynamic generalization invests more effort in
/// predecessor cubes that prove difficult to block (high activity), while
/// keeping overhead low for easy cubes. CTP + infinity frame ensure that
/// blocking lemmas propagate forward efficiently.
///
/// This is a PredProp diversity variant that adapts its generalization
/// effort based on proof obligation difficulty, complementing the fixed
/// deep-CTG and fixed-conservative predprop configs.
pub fn ic3_predprop_dynamic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            predprop: true,
            dynamic: true,
            ctp: true,
            inf_frame: true,
            random_seed: 181,
            ..Ic3Config::default()
        },
        name: "ic3-predprop-dynamic".into(),
    }
}

/// IC3 with moderate CTG targeting sequential counter UNSAT benchmarks (#4307).
///
/// Targets `counter_bit_width_small` (57 latches, UNSAT, aic3 solves in 8s,
/// rIC3 in 16s) and similar sequential counter circuits whose inductive
/// invariant requires moderate CTG generalization depth. The default
/// conservative CTG (ctg_max=3, ctg_limit=1) and the existing "deep" CTG
/// configs (ctg_max=5, ctg_limit=15) both missed this benchmark in Wave 28
/// (tla-aiger timed out at 104s), leaving a middle tuning gap.
///
/// Design per `reports/2026-04-20-r17-wave29-gap-analysis.md` §"Gap 2" and
/// `designs/2026-04-18-hwmcc-path-to-supremacy.md` Blocker C:
/// - `ctg_max = 5`   — moderate per-query CTG effort (cheaper than #4284's
///                     `ctg_max=8` Sokoban variant; complementary, not redundant).
/// - `ctg_limit = 3` — bounded recursive trivial_block depth (the design's
///                     `ctg_recursion_depth`). Between default 1 and deep 15.
/// - `ctg_down`      — enables flip-based cube shrinking on MIC literal-drop
///                     failure. This is the closest in-tree analogue to the
///                     design's `ic3_ctg_enable_on_fail` + `mic_mode: Aggressive`
///                     intent: when a literal drop fails, use the counterexample
///                     model to shrink the cube more aggressively instead of
///                     giving up on that literal. Reference: rIC3 `mic.rs:122`
///                     — `ctg_down()`.
///
/// Seed 190 is unique; no collision with existing configs (seeds 1-45, 100-104,
/// 110-112, 150-161, 170-172, 180-182, 200).
pub fn ic3_ctg5_counter() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 5,
            ctg_limit: 3,
            ctg_down: true,
            random_seed: 190,
            ..Ic3Config::default()
        },
        name: "ic3-ctg5-counter".into(),
    }
}

/// IC3 with predicate propagation + no PO dropping + no parent lemma (#4101).
///
/// Backward-analysis predecessors are structurally important: they represent
/// states one transition away from violating the property. Unlike forward
/// IC3's bad cubes (which are often spurious approximations), predprop cubes
/// are precise transition predecessors. This config disables PO dropping
/// and parent lemma bias to give predprop cubes maximum persistence and
/// fresh generalization — drop_po=false ensures they are never discarded,
/// and parent_lemma=false ensures generalization is not biased by prior
/// lemma structure.
///
/// Reference: rIC3's `ic3_no_parent` + `predprop` combination.
pub fn ic3_predprop_no_drop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            predprop: true,
            drop_po: false,
            parent_lemma: false,
            random_seed: 182,
            ..Ic3Config::default()
        },
        name: "ic3-predprop-no-drop".into(),
    }
}

/// CEGAR-IC3 with conservative inner IC3 config (abs_all mode).
///
/// Runs IC3 inside a CEGAR abstraction-refinement loop. Best for large
/// circuits where only a small subset of latches is relevant to the property.
/// Uses abs_all mode: non-abstract latches become free variables.
pub fn cegar_ic3_conservative() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            random_seed: 40,
            ..Ic3Config::default()
        },
        name: "cegar-ic3-conservative".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractAll,
    }
}

/// CEGAR-IC3 with CTP + infinity frame inner config (abs_all mode).
///
/// Combines CEGAR's abstraction with CTP's stronger propagation and
/// infinity frame promotion.
pub fn cegar_ic3_ctp_inf() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            random_seed: 41,
            ..Ic3Config::default()
        },
        name: "cegar-ic3-ctp-inf".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractAll,
    }
}

/// CEGAR-IC3 in abs_cst mode: only abstract constraint enforcement.
///
/// Mirrors rIC3's `ic3_abs_cst` portfolio config. Keeps all latches and
/// transition relations but relaxes constraint enforcement for non-abstract
/// latches. This is a lighter abstraction that produces fewer spurious
/// counterexamples at the cost of less speedup.
pub fn ic3_abs_cst() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            random_seed: 42,
            ..Ic3Config::default()
        },
        name: "ic3-abs-cst".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractConstraints,
    }
}

/// CEGAR-IC3 in abs_all mode with internal signals.
///
/// Mirrors rIC3's `ic3_abs_all` portfolio config. Full abstraction (both
/// constraints and transition) with internal signal cubes for better
/// generalization on circuits with complex combinational logic.
pub fn ic3_abs_all() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            internal_signals: true,
            random_seed: 43,
            ..Ic3Config::default()
        },
        name: "ic3-abs-all".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractAll,
    }
}

/// CEGAR-IC3 with dynamic generalization inside the abstraction (#4064).
///
/// Combines CEGAR's abstraction-refinement loop with per-PO activity-based
/// CTG adaptation. In abstract models, proof obligation difficulty varies
/// widely: some cubes are trivially blocked on the small abstract lattice,
/// while others trigger refinement. Dynamic CTG invests generalization
/// effort proportionally, avoiding wasted SAT calls on easy abstract cubes
/// and strengthening lemmas on hard ones that might otherwise cause spurious
/// counterexamples requiring refinement.
///
/// Uses abs_all mode for maximum abstraction benefit, CTP + inf for strong
/// propagation on the (often small) abstract model.
pub fn cegar_ic3_dynamic() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            dynamic: true,
            ctp: true,
            inf_frame: true,
            random_seed: 44,
            ..Ic3Config::default()
        },
        name: "cegar-ic3-dynamic".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractAll,
    }
}

/// CEGAR-IC3 with SimpleSolver backend for z4-sat-resistant circuits (#4064).
///
/// Abstract models produced by CEGAR can have unusual constraint structures
/// (partially removed transitions, dangling constraint literals) that trigger
/// z4-sat's FINALIZE_SAT_FAIL or false UNSAT pathologies. SimpleSolver's
/// basic DPLL never produces these errors, providing a reliable fallback
/// CEGAR path.
///
/// Uses abs_cst mode (lighter abstraction) since SimpleSolver is slower
/// per-query than z4-sat — less abstraction means fewer refinement iterations,
/// compensating for the slower per-query backend. CTP + inf enabled for
/// convergence on the (full-size) abstract model.
pub fn cegar_ic3_simple_solver() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ctp: true,
            inf_frame: true,
            validation_strategy: ValidationStrategy::Auto,
            crosscheck_disabled: true,
            random_seed: 45,
            ..Ic3Config::default()
        },
        name: "cegar-ic3-simple-solver".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractConstraints,
    }
}

// ---------------------------------------------------------------------------
// Deep BMC configs (#4123)
// ---------------------------------------------------------------------------

/// Deep BMC targeting depth ~200 via geometric backoff.
///
/// Skips thorough shallow coverage (only 10 depths at step=1) and rapidly
/// doubles step size every 10 SAT calls, capped at step=32. Reaches depth 200
/// in roughly 10 + 6*10 = 70 SAT calls (vs 200 for fixed step=1).
///
/// Designed for benchmarks where counterexamples lie at medium-deep depths
/// (100-300) and the shallow region is already covered by step=1/2/5 BMC configs.
pub fn bmc_deep_200() -> EngineConfig {
    EngineConfig::BmcGeometricBackoff {
        initial_depths: 10,
        double_interval: 10,
        max_step: 32,
    }
}

/// Deep BMC targeting depth ~500 via geometric backoff.
///
/// Minimal shallow coverage (10 depths at step=1), then aggressive doubling
/// every 8 SAT calls, capped at step=64. Reaches depth 500 in roughly
/// 10 + 8*8 = 74 SAT calls. Effective on Sokoban/microban puzzles where
/// counterexamples lie at depth 200-600.
pub fn bmc_deep_500() -> EngineConfig {
    EngineConfig::BmcGeometricBackoff {
        initial_depths: 10,
        double_interval: 8,
        max_step: 64,
    }
}

/// Deep BMC targeting depth ~1000 via geometric backoff.
///
/// Minimal shallow coverage (5 depths at step=1), very aggressive doubling
/// every 5 SAT calls, capped at step=128. Reaches depth 1000 in roughly
/// 5 + 8*5 = 45 SAT calls. Maximum depth reach for extremely deep
/// counterexamples that no other BMC config can find in time.
pub fn bmc_deep_1000() -> EngineConfig {
    EngineConfig::BmcGeometricBackoff {
        initial_depths: 5,
        double_interval: 5,
        max_step: 128,
    }
}

// ---------------------------------------------------------------------------
// Portfolio presets
// ---------------------------------------------------------------------------

/// Default portfolio configuration.
///
/// Rebalanced from Wave 9 data (15/50 benchmarks solved):
/// - k-induction solved 5/7 UNSAT (strongest UNSAT solver) → more configs
/// - BMC solved 8/8 SAT (strongest SAT solver) → wider step coverage
/// - IC3 solved only 2 benchmarks → fewer configs, keep only proven/diverse ones
///
/// Total: 25 threads. For maximum coverage, use `competition_portfolio()`.
pub fn default_portfolio() -> PortfolioConfig {
    full_ic3_portfolio()
}

/// Full IC3 portfolio rebalanced from Wave 9 data.
///
/// Wave 9 results (15/50 benchmarks):
///   - k-induction: 5/7 UNSAT (strongest UNSAT solver)
///   - BMC: 8/8 SAT (strongest SAT solver)
///   - IC3: 2/15 (only conservative + arithmetic-tight-budget solved anything)
///
/// Rebalancing strategy (#4119, #4099):
///   - IC3: expanded from 5 to 6 (added multi-order-ctp for tighter generalization)
///   - CEGAR-IC3: expanded from 2 to 4 (#4064: dynamic + SimpleSolver variants)
///   - BMC: expanded from 11 to 14 (added step 2/5 to fill medium-depth gaps,
///     added z4-Geometric step 65 for backend diversity)
///   - k-induction: expanded from 3 to 7 (the UNSAT workhorse deserves more threads)
///     Standard + skip-bmc + z4-Luby + z4-Stable + z4-Vmtf skip-bmc
///     + strengthened + strengthened z4-Luby
///
/// Total: 12 IC3 + 1 SimpleSolver IC3 + 4 CEGAR + 14 BMC + 7 k-ind = 38 engines.
pub fn full_ic3_portfolio() -> PortfolioConfig {
    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines: vec![
            // IC3 variants (6 configurations — curated from Wave 9 data + #4099)
            // Only ic3-conservative solved a benchmark; keep it plus 5 maximally
            // diverse configs covering different axes.
            ic3_conservative(),    // seed 1: baseline, solved vis_QF_BV_bcuvis32
            ic3_ctp_inf(),         // seed 7: CTP + inf (strong propagation combo)
            ic3_deep_ctg_ctp(),    // seed 14: strongest generalization + propagation
            ic3_dynamic_ctp(),     // seed 20: per-PO adaptive + CTP + inf
            ic3_circuit_adapt(),   // seed 27: auto-tunes CTG for circuit size
            ic3_multi_order_ctp(), // seed 111: 2-ordering lift + CTP + inf (#4099)
            ic3_parent_mic(),      // seed 38: parent lemma MIC seeding (CAV'23 #4150)
            // Internal signal (--inn) IC3 variants (#4148, 2 configs)
            ic3_inn_ctp(),     // seed 151: inn + CTP + inf (matches rIC3 ic3_inn_ctp)
            ic3_inn_dynamic(), // seed 153: inn + dynamic (matches rIC3 ic3_inn_dynamic)
            // PredProp IC3 variants for backward analysis diversity (#4101, 2 configs)
            ic3_predprop_ctp(), // seed 37: predprop + CTP + inf (backward + propagation)
            ic3_predprop_deep_ctg(), // seed 180: predprop + deep CTG + internal signals
            // Moderate-CTG variant for sequential counter UNSAT (#4307)
            // counter_bit_width_small (57 latches) needs moderate CTG (ctg_max=5,
            // ctg_limit=3) with flip-based aggressive MIC. Fills the tuning gap
            // between conservative (ctg_max=3,limit=1) and deep (ctg_max=5,limit=15).
            ic3_ctg5_counter(), // seed 190: ctg_max=5, ctg_limit=3, ctg_down
            // SimpleSolver IC3 for high-constraint circuits (#4092)
            // z4-sat FINALIZE_SAT_FAIL on microban (100-300+ constraints) wastes
            // seconds on cross-check fallbacks. SimpleSolver is correct from the start.
            ic3_simple_solver(), // seed 160: SimpleSolver backend (no z4-sat false UNSAT)
            // Minimal-overhead IC3 for very small circuits (#4259, #4288)
            // cal14 (23 latches, 1656 trans clauses) solves in sub-second with
            // rIC3; this config forces the minimal rIC3-equivalent baseline.
            ic3_small_circuit(), // seed 200: minimal overhead, crosscheck off, no CTG recursion
            // CEGAR-IC3 variants (#4064: abstraction-refinement loop over IC3)
            ic3_abs_cst(),       // seed 42: abs_cst mode (constraint-only abstraction)
            ic3_abs_all(),       // seed 43: abs_all mode (full abstraction + internal signals)
            cegar_ic3_dynamic(), // seed 44: CEGAR + dynamic CTG + CTP + inf (abs_all)
            cegar_ic3_simple_solver(), // seed 45: CEGAR + SimpleSolver (abs_cst, no z4-sat false UNSAT)
            // BMC variants with z4-sat default (10 configurations, #4119)
            // Wave 9: BMC solved all 8 SAT benchmarks. Added step 2/5 to fill
            // gaps between step 1 and step 10 for medium-depth SAT benchmarks.
            EngineConfig::Bmc { step: 1 },
            EngineConfig::Bmc { step: 2 }, // Fill gap: medium-depth (#4119)
            EngineConfig::Bmc { step: 5 }, // Fill gap: shallow-mid (#4119)
            EngineConfig::Bmc { step: 10 },
            EngineConfig::Bmc { step: 65 },
            EngineConfig::Bmc { step: 200 },
            EngineConfig::Bmc { step: 500 }, // Deep Sokoban puzzles (#4123)
            EngineConfig::Bmc { step: 1000 }, // Extremely deep bugs (#4123)
            EngineConfig::BmcDynamic,
            // Geometric backoff BMC (#4123): step=1 for first 50 depths, then doubles.
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 50,
                double_interval: 20,
                max_step: 64,
            },
            // z4-sat variant BMC (4 configs): diverse SAT solver configs race
            EngineConfig::BmcZ4Variant {
                step: 1,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            },
            EngineConfig::BmcZ4Variant {
                step: 10,
                backend: crate::sat_types::SolverBackend::Z4Stable,
            },
            EngineConfig::BmcZ4Variant {
                step: 65,
                backend: crate::sat_types::SolverBackend::Z4Geometric,
            },
            EngineConfig::BmcZ4VariantDynamic {
                backend: crate::sat_types::SolverBackend::Z4Vmtf,
            },
            // k-Induction (8 configs — the UNSAT workhorse, up from 3, #4119/#4050)
            // Wave 9: k-induction solved 5/7 UNSAT. More backend diversity
            // races different z4-sat configs on the same induction problem.
            // Simple-path re-enabled with vacuity check guard (#4050).
            EngineConfig::Kind,           // default z4-sat
            EngineConfig::KindSimplePath, // simple-path strengthening (#4050)
            EngineConfig::KindSkipBmc,    // induction-only (BMC handled separately)
            EngineConfig::KindZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Luby,
            },
            EngineConfig::KindZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Stable,
            },
            EngineConfig::KindSkipBmcZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Vmtf,
            },
            // Strengthened k-Induction with invariant discovery (CEGS)
            EngineConfig::KindStrengthened,
            EngineConfig::KindStrengthenedZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Luby,
            },
            // Random forward simulation (1 config — zero-cost SAT-free diversity)
            EngineConfig::RandomSim {
                steps_per_walk: 1_000_000,
                num_walks: 50,
                seed: 42,
            },
        ],
        max_depth: 50000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// Competition portfolio optimized from Wave 9 sweep data.
///
/// Wave 9 results (15 correct / 50 benchmarks):
///   - BMC solved 7/8 SAT benchmarks (the SAT workhorse)
///   - k-induction solved 5/7 UNSAT benchmarks (the UNSAT workhorse)
///   - IC3 solved only 2/15 benchmarks (ic3-arithmetic-tight-budget + ic3 default)
///   - 37+ IC3 configs were redundant — most get stuck at depth 1-2 on industrial circuits
///
/// Portfolio rebalanced: fewer IC3 (keep only configs with proven value or
/// maximum diversity), more BMC step variants for deeper SAT coverage, more
/// k-induction variants with z4-sat backend diversity.
///
/// **IC3 (23 configs) — curated for maximum diversity:**
/// - conservative (seed 1): baseline, solved vis_QF_BV_bcuvis32
/// - arithmetic-tight-budget (seed 104): ONLY IC3 that uniquely solved a benchmark
/// - ctp-inf (seed 7): strong propagation + frame promotion combo
/// - deep-ctg-ctp (seed 14): strongest generalization + propagation
/// - circuit-adapt (seed 27): auto-tunes CTG for circuit size
/// - dynamic-ctp (seed 20): per-PO adaptive generalization
/// - predprop-ctp (seed 37): backward analysis for forward-hard circuits
/// - predprop-deep-ctg (seed 180): predprop + deep CTG + internal signals (#4101)
/// - predprop-dynamic (seed 181): predprop + dynamic + CTP + inf (#4101)
/// - predprop-no-drop (seed 182): predprop + no drop + no parent (#4101)
/// - no-preprocess (seed 34): rIC3 parity, no CTG/no drop_po
/// - multi-order-ctp (seed 111): 2-ordering MIC lift
/// - multi-order-full (seed 112): 3-ordering MIC lift (max diversity)
/// - parent-mic (seed 38): parent lemma MIC seeding (CAV'23)
/// - parent-mic-ctp (seed 39): parent MIC + CTP + inf
/// - inn-ctp (seed 151): internal signals + CTP (#4148)
/// - inn-noctg (seed 152): internal signals, no CTG (#4148)
/// - inn-dynamic (seed 153): internal signals + dynamic (#4148)
/// - simple-solver (seed 160): SimpleSolver for high-constraint circuits
/// - simple-solver-inn (seed 161): SimpleSolver + internal signals
/// - aggressive-drop (seed 170): drop_po threshold=10.0 (#4151)
/// - conservative-drop (seed 171): drop_po threshold=40.0 (#4151)
/// - aggressive-drop-ctp (seed 172): drop_po threshold=10.0 + CTP + inf (#4151)
///
/// **CEGAR-IC3 (4 configs, #4064) — abstraction for large circuits:**
/// - cegar-ic3-ctp-inf (seed 41): CEGAR + strong propagation (abs_all)
/// - ic3-abs-cst (seed 42): constraint-only abstraction
/// - cegar-ic3-dynamic (seed 44): CEGAR + dynamic CTG + CTP + inf (abs_all)
/// - cegar-ic3-simple-solver (seed 45): CEGAR + SimpleSolver (abs_cst)
///
/// **BMC (21 configs) — wide step range + z4-sat backend diversity + deep geometric:**
/// - Steps 1/2/5/10/25/65/100/200/500/1000 + dynamic + geometric backoff (12 default z4-sat)
/// - z4-sat Luby step 1/5, Stable step 10, Geometric step 25, VMTF dynamic, geo-backoff Luby (6 variants)
/// - Deep geometric backoff: depth 200/500/1000 targets (#4123) (3 configs)
///
/// **k-Induction (12 configs) — z4-sat backend diversity + strengthened (#4119) + simple-path (#4050):**
/// - Standard + simple-path (#4050) + skip-bmc (3 default z4-sat)
/// - z4-sat Luby/Stable/Vmtf standard (3 variants)
/// - z4-sat Luby/Stable/Vmtf skip-bmc (3 variants)
/// - Strengthened k-induction: default + z4-Luby + z4-Stable (3 configs)
///
/// Total: 23 IC3 + 4 CEGAR + 21 BMC + 12 k-ind = 60 engines.
pub fn competition_portfolio() -> PortfolioConfig {
    let engines = vec![
        // IC3 — 23 curated configs (15 general + 3 internal-signal + 2 SimpleSolver + 3 drop-threshold)
        // Wave 9 data: only ic3-conservative and ic3-arithmetic-tight-budget
        // solved benchmarks. Keep those plus maximally diverse configs that
        // cover different axes (CTG, CTP, dynamic, ordering, backward analysis,
        // internal signals for arithmetic generalization #4148,
        // drop_po threshold variants for thrashing prevention #4151).
        ic3_conservative(), // seed 1: baseline, solved vis_QF_BV_bcuvis32
        ic3_arithmetic_tight_budget(), // seed 104: solved qspiflash_qflexpress_divfive-p20
        ic3_ctp_inf(),      // seed 7: CTP + inf (strong propagation combo)
        ic3_deep_ctg_ctp(), // seed 14: deep CTG + CTP (strongest generalization)
        ic3_circuit_adapt(), // seed 27: auto-tunes CTG for circuit size
        ic3_dynamic_ctp(),  // seed 20: per-PO adaptive + CTP + inf
        ic3_predprop_ctp(), // seed 37: backward analysis + CTP + inf
        ic3_predprop_deep_ctg(), // seed 180: predprop + deep CTG + internal signals (#4101)
        ic3_predprop_dynamic(), // seed 181: predprop + dynamic + CTP + inf (#4101)
        ic3_predprop_no_drop(), // seed 182: predprop + no drop + no parent (#4101)
        ic3_ctg5_counter(), // seed 190: moderate CTG + ctg_down for counter UNSAT (#4307)
        ic3_no_preprocess(), // seed 34: no CTG, no drop_po (rIC3 parity)
        ic3_multi_order_ctp(), // seed 111: 2-ordering lift + CTP + inf
        ic3_multi_order_full(), // seed 112: 3-ordering lift + CTP + inf (max diversity)
        ic3_parent_mic(),   // seed 38: parent lemma MIC seeding (CAV'23 #4150)
        ic3_parent_mic_ctp(), // seed 39: parent MIC + CTP + inf (#4150)
        // Internal signal (--inn) IC3 variants (#4148, 3 configs)
        // rIC3's bl_default has 4 inn configs (ic3_inn, ic3_inn_ctp, ic3_inn_noctg,
        // ic3_inn_dynamic). Internal signals extend MIC to AND-gate outputs for
        // finer generalization, particularly effective on arithmetic circuits.
        ic3_inn_ctp(),     // seed 151: inn + CTP + inf (matches rIC3 ic3_inn_ctp)
        ic3_inn_noctg(),   // seed 152: inn + no CTG (matches rIC3 ic3_inn_noctg)
        ic3_inn_dynamic(), // seed 153: inn + dynamic (matches rIC3 ic3_inn_dynamic)
        // SimpleSolver IC3 for high-constraint circuits (#4092)
        ic3_simple_solver(),     // seed 160: SimpleSolver (no z4-sat false UNSAT)
        ic3_simple_solver_inn(), // seed 161: SimpleSolver + inn
        // Drop-PO threshold variants (#4151, 3 configs)
        // Default IC3 configs use drop_po=true, threshold=20.0. These variants
        // explore aggressive dropping (threshold=10.0) for thrash-heavy circuits
        // and conservative dropping (threshold=40.0) for circuits where persistence
        // eventually pays off. Complements no-drop (ic3_no_preprocess seed 34).
        ic3_aggressive_drop(),     // seed 170: threshold=10.0, drop sooner
        ic3_conservative_drop(),   // seed 171: threshold=40.0, drop later
        ic3_aggressive_drop_ctp(), // seed 172: threshold=10.0 + CTP + inf
        // CEGAR-IC3 — 4 configs (#4064: expanded from 2)
        cegar_ic3_ctp_inf(),       // seed 41: CEGAR + CTP + inf (abs_all)
        ic3_abs_cst(),             // seed 42: constraint-only abstraction
        cegar_ic3_dynamic(),       // seed 44: CEGAR + dynamic CTG + CTP + inf (abs_all)
        cegar_ic3_simple_solver(), // seed 45: CEGAR + SimpleSolver (abs_cst)
        // BMC — 21 configs (#4123: added step 1000 + geometric backoff + deep variants)
        // Wave 9: BMC solved 7/8 SAT benchmarks. More step variants give wider
        // depth coverage. Step 2 and 5 fill gaps between step 1 and step 10
        // for medium-depth SAT benchmarks (microban puzzles at depth 20-60).
        EngineConfig::Bmc { step: 1 },    // Every depth, thorough
        EngineConfig::Bmc { step: 2 },    // 2x faster depth coverage
        EngineConfig::Bmc { step: 5 },    // Shallow-mid bugs
        EngineConfig::Bmc { step: 10 },   // Mid-depth
        EngineConfig::Bmc { step: 25 },   // Mid-deep
        EngineConfig::Bmc { step: 65 },   // Deep bugs
        EngineConfig::Bmc { step: 100 },  // Very deep
        EngineConfig::Bmc { step: 200 },  // Very deep, fast exploration
        EngineConfig::Bmc { step: 500 },  // Extremely deep (Sokoban)
        EngineConfig::Bmc { step: 1000 }, // Maximum depth reach (#4123)
        EngineConfig::BmcDynamic,         // Circuit-adaptive
        // Geometric backoff BMC (#4123): best of both worlds — thorough shallow
        // coverage (step=1 for first 50 depths) then rapid deep exploration.
        EngineConfig::BmcGeometricBackoff {
            initial_depths: 50,
            double_interval: 20,
            max_step: 64,
        },
        // z4-sat variant BMC: different SAT solver configs race on same BMC problem
        EngineConfig::BmcZ4Variant {
            step: 1,
            backend: crate::sat_types::SolverBackend::Z4Luby,
        },
        EngineConfig::BmcZ4Variant {
            step: 5,
            backend: crate::sat_types::SolverBackend::Z4Luby,
        },
        EngineConfig::BmcZ4Variant {
            step: 10,
            backend: crate::sat_types::SolverBackend::Z4Stable,
        },
        EngineConfig::BmcZ4Variant {
            step: 25,
            backend: crate::sat_types::SolverBackend::Z4Geometric,
        },
        EngineConfig::BmcZ4VariantDynamic {
            backend: crate::sat_types::SolverBackend::Z4Vmtf,
        },
        // Geometric backoff with z4-sat Luby for diversity (#4123)
        EngineConfig::BmcGeometricBackoffZ4Variant {
            initial_depths: 50,
            double_interval: 20,
            max_step: 64,
            backend: crate::sat_types::SolverBackend::Z4Luby,
        },
        // Deep BMC via geometric backoff (#4123): targeted depth configs that
        // aggressively skip shallow regions to reach deep counterexamples fast.
        // Complements the thorough shallow-first geometric backoff above.
        bmc_deep_200(),  // Reach depth ~200 in ~70 SAT calls
        bmc_deep_500(),  // Reach depth ~500 in ~74 SAT calls
        bmc_deep_1000(), // Reach depth ~1000 in ~45 SAT calls
        // k-Induction — 12 configs total (9 basic + 3 strengthened): the UNSAT workhorse
        // Wave 9: k-induction solved 5/7 UNSAT benchmarks. Backend diversity
        // races different z4-sat configs on the same induction problem.
        // Simple-path re-enabled with vacuity check guard (#4050).
        EngineConfig::Kind,           // default z4-sat
        EngineConfig::KindSimplePath, // simple-path strengthening (#4050)
        EngineConfig::KindSkipBmc,    // induction-only (BMC handled separately)
        EngineConfig::KindZ4Variant {
            backend: crate::sat_types::SolverBackend::Z4Luby,
        },
        EngineConfig::KindZ4Variant {
            backend: crate::sat_types::SolverBackend::Z4Stable,
        },
        EngineConfig::KindZ4Variant {
            backend: crate::sat_types::SolverBackend::Z4Vmtf,
        },
        EngineConfig::KindSkipBmcZ4Variant {
            backend: crate::sat_types::SolverBackend::Z4Luby,
        },
        EngineConfig::KindSkipBmcZ4Variant {
            backend: crate::sat_types::SolverBackend::Z4Stable,
        },
        EngineConfig::KindSkipBmcZ4Variant {
            backend: crate::sat_types::SolverBackend::Z4Vmtf,
        },
        // Strengthened k-Induction with auxiliary invariant discovery (CEGS, #4119)
        // Supplements basic k-induction — strengthened induction may converge on
        // benchmarks where basic k-induction cannot, and vice versa. Both must run.
        // z4-sat variant diversity for strengthened induction as well.
        EngineConfig::KindStrengthened,
        EngineConfig::KindStrengthenedZ4Variant {
            backend: crate::sat_types::SolverBackend::Z4Luby,
        },
        EngineConfig::KindStrengthenedZ4Variant {
            backend: crate::sat_types::SolverBackend::Z4Stable,
        },
        // Random forward simulation (2 configs — zero-cost SAT-free diversity)
        EngineConfig::RandomSim {
            steps_per_walk: 1_000_000,
            num_walks: 50,
            seed: 42,
        },
        EngineConfig::RandomSim {
            steps_per_walk: 5_000_000,
            num_walks: 20,
            seed: 0xBAAD_F00D,
        },
    ];

    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines,
        max_depth: 50000,
        preprocess: crate::preprocess::PreprocessConfig::aggressive(),
    }
}

/// rIC3-matched portfolio: 11 IC3 + 4 BMC + 1 k-induction = 16 engines.
///
/// This portfolio exactly mirrors rIC3's `bl_default` configuration from
/// `portfolio.toml`, which is the configuration that achieved #2 safety
/// at HWMCC'25 (274/330 benchmarks solved).
///
/// **rIC3 bl_default mapping:**
/// ```text
/// ic3               → ic3-conservative (seed 1)
/// ic3_no_preproc    → ic3-ctp (seed 2, no CTG)   [we approximate]
/// ic3_no_parent     → ic3-inf (seed 3)            [we approximate]
/// ic3_abs_cst       → ic3-internal (seed 4)       [abstract const → internal signals]
/// ic3_abs_all       → ic3-ternary (seed 5)        [abstract all → ternary]
/// ic3_predprop      → ic3-full (seed 6)           [pred-prop → full features]
/// ic3_ctg_limit     → ic3-deep-ctg (seed 7)       [exact match: ctg_max=5 ctg_limit=15]
/// ic3_inn           → ic3-inn (seed 150)            [exact match #4148]
/// ic3_inn_ctp       → ic3-inn-ctp (seed 151)       [exact match #4148]
/// ic3_inn_noctg     → ic3-inn-noctg (seed 152)     [exact match #4148]
/// ic3_inn_dynamic   → ic3-inn-dynamic (seed 153)   [exact match #4148]
/// bmc               → bmc step=1 (seed 12)
/// bmc_kissat_10     → bmc step=10 (seed 13)
/// bmc_kissat_65     → bmc step=65 (seed 14)
/// bmc_kissat_dyn    → bmc dynamic (seed 15)
/// kind              → kind (seed 16)
/// ```
///
/// The key insight from rIC3: 16 engines is the sweet spot. Too few = missing
/// coverage. Too many = resource contention. The 11:4:1 ratio (IC3:BMC:Kind)
/// reflects that IC3 handles most UNSAT benchmarks while BMC finds most SAT ones.
///
/// Portfolio diversity comes from z4-sat configuration variants instead of
/// external solvers. The 3 Kissat-equivalent BMC slots (step 10, step 65,
/// dynamic) use z4-sat variants with different restart/branching configs,
/// providing the multi-solver diversity pattern rIC3 uses (CaDiCaL + Kissat)
/// but entirely within our own SAT solver stack.
pub fn ric3_portfolio() -> PortfolioConfig {
    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines: vec![
            // 11 IC3 variants (matching rIC3's bl_default 11 IC3 configs)
            ic3_conservative(), // seed 1: ic3 (default)
            ic3_ctp(),          // seed 2: ic3_no_preproc approx
            ic3_inf(),          // seed 3: ic3_no_parent approx
            ic3_internal(),     // seed 4: ic3_abs_cst → internal signals
            ic3_ternary(),      // seed 5: ic3_abs_all → ternary
            ic3_full(),         // seed 6: ic3_predprop → full features
            ic3_deep_ctg(),     // seed 7: ic3_ctg_limit (exact: ctg_max=5 ctg_limit=15)
            ic3_inn_ctp(), // seed 151: ic3_inn_ctp (cube-extension #4148; retained for diversity)
            // inn-proper (latch promotion, #4308): rIC3's state-variable basis
            // variant. Each AND-gate output not in input-fanout is promoted to
            // a first-class latch with next-state from 1-step unrolling. Yields
            // structurally smaller invariants on arithmetic-heavy UNSAT circuits
            // (cal14, cal42, diffeq, counter_bit_width_small). Mutually exclusive
            // with cube-extension `internal_signals` — these set inn_proper=true.
            ic3_inn_proper(),       // seed 160: inn-proper alone
            ic3_inn_proper_ctp(),   // seed 161: inn-proper + CTP + inf
            ic3_inn_proper_noctg(), // seed 162: inn-proper, no CTG
            // 4 BMC variants (matching rIC3's bl_default)
            // rIC3 uses plain CaDiCaL for step-1 and Kissat for step-10/65/dynamic.
            // We use z4-sat default for step-1 and z4-sat variants for the rest,
            // providing equivalent diversity through configuration knobs.
            EngineConfig::Bmc { step: 1 }, // bmc --step 1 (z4-sat default)
            EngineConfig::BmcZ4Variant {
                step: 10,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            }, // Luby restarts for step-10
            EngineConfig::BmcZ4Variant {
                step: 65,
                backend: crate::sat_types::SolverBackend::Z4Stable,
            }, // Stable mode for step-65
            EngineConfig::BmcZ4VariantDynamic {
                backend: crate::sat_types::SolverBackend::Z4Vmtf,
            }, // VMTF branching for dynamic
            // 1 k-induction (rIC3 uses --simple-path; vacuity check guards soundness #4050)
            EngineConfig::KindSimplePath,
        ],
        max_depth: 50000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// SAT-focused portfolio: more BMC threads, higher depth, fewer IC3 configs.
///
/// Optimized for benchmarks where the property is expected to be SAT (bug exists
/// at some depth), such as HWMCC Sokoban/microban puzzles (#4073, #4123, #4149).
/// The key insight: SAT benchmarks are solved by BMC, not IC3. IC3 probes for
/// safety (UNSAT), while BMC searches for bugs (SAT). This portfolio:
///
/// - **21 BMC configs**: z4-sat + SimpleSolver backends, wide step range + deep
///   geometric backoff targeting depths 200-5000 (#4149)
/// - **2 IC3 configs**: conservative + SimpleSolver for diversity (IC3 can find
///   shallow bugs faster than BMC via backward analysis)
/// - **max_depth = 200,000**: deep enough for complex Sokoban puzzles (#4149)
/// - **1 k-induction config**: skip-bmc (induction-only, BMC handled separately)
///
/// Selected when the CLI specifies `--sat-focus` or when circuit analysis
/// detects SAT-likely patterns (PI count > 2x latch count, or Sokoban/microban
/// pattern with I==L and high constraint ratio #4149).
pub fn sat_focused_portfolio() -> PortfolioConfig {
    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines: vec![
            // === BMC with z4-sat default (Z4NoPreprocess) ===
            // Step=1 for thorough shallow coverage, larger steps for depth reach.
            EngineConfig::Bmc { step: 1 },   // Every depth, thorough
            EngineConfig::Bmc { step: 5 },   // Shallow-mid bugs
            EngineConfig::Bmc { step: 10 },  // Mid-depth
            EngineConfig::Bmc { step: 25 },  // Mid-deep
            EngineConfig::Bmc { step: 100 }, // Very deep
            EngineConfig::Bmc { step: 500 }, // Extremely deep (#4123)
            EngineConfig::BmcDynamic,        // Circuit-adaptive step size
            // === Geometric backoff BMC: thorough shallow + rapid deep (#4123) ===
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 30,
                double_interval: 15,
                max_step: 64,
            },
            // === Deep geometric backoff targeting depths 2000-5000 (#4149) ===
            // Minimal shallow coverage, very aggressive doubling to reach deep
            // counterexamples. Microban puzzles with 40-60 latches may need
            // depths 200-500+ for complex Sokoban solutions.
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 5,
                double_interval: 5,
                max_step: 256,
            },
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 3,
                double_interval: 3,
                max_step: 512,
            },
            // === Linear-offset BMC for mid-deep Sokoban SAT (#4299, Wave 29) ===
            // Geometric backoff doubles step size and overshoots specific
            // counterexample depths. Sokoban SAT puzzles (microban_64/77/89/
            // 118/132/136/148/149) land at depths ~100-500 and need every
            // depth checked past the skip region. Two offset points cover
            // the shallow-Sokoban (rIC3 0.2-2s) and deep-Sokoban (rIC3 2-10s)
            // bands; others already run step=1 for depths 0-50.
            EngineConfig::BmcLinearOffset {
                start_depth: 50,
                step: 1,
                max_depth: 600,
            },
            EngineConfig::BmcLinearOffset {
                start_depth: 150,
                step: 1,
                max_depth: 800,
            },
            // === SimpleSolver BMC variants (#4149) ===
            // Microban/Sokoban puzzles have high constraint-to-latch ratios (5-16x)
            // that cause z4-sat FINALIZE_SAT_FAIL or spurious SAT. SimpleSolver
            // is a basic DPLL that never produces these errors. On high-constraint
            // circuits where z4-sat wastes time on error recovery, SimpleSolver
            // may be faster per-step despite lacking CDCL.
            EngineConfig::BmcZ4Variant {
                step: 1,
                backend: crate::sat_types::SolverBackend::Simple,
            },
            EngineConfig::BmcZ4Variant {
                step: 5,
                backend: crate::sat_types::SolverBackend::Simple,
            },
            EngineConfig::BmcZ4Variant {
                step: 25,
                backend: crate::sat_types::SolverBackend::Simple,
            },
            // Wave 29 (#4299): larger SimpleSolver steps for mid-deep Sokoban SAT.
            // On 40-60 latch microban circuits the constraint density thrashes
            // z4-sat; SimpleSolver is slow per-query but never false-UNSAT, and
            // with step=50/100 it covers depths 300-500 with far fewer SAT calls
            // than step=25 while still hitting specific counterexample depths.
            EngineConfig::BmcZ4Variant {
                step: 50,
                backend: crate::sat_types::SolverBackend::Simple,
            },
            EngineConfig::BmcZ4Variant {
                step: 100,
                backend: crate::sat_types::SolverBackend::Simple,
            },
            // SimpleSolver geometric backoff — deep exploration without z4-sat issues
            EngineConfig::BmcGeometricBackoffZ4Variant {
                initial_depths: 20,
                double_interval: 15,
                max_step: 64,
                backend: crate::sat_types::SolverBackend::Simple,
            },
            EngineConfig::BmcGeometricBackoffZ4Variant {
                initial_depths: 5,
                double_interval: 5,
                max_step: 256,
                backend: crate::sat_types::SolverBackend::Simple,
            },
            // === z4-sat variant BMC: diverse SAT solver configs (#4123) ===
            EngineConfig::BmcZ4Variant {
                step: 1,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            },
            EngineConfig::BmcZ4Variant {
                step: 10,
                backend: crate::sat_types::SolverBackend::Z4Stable,
            },
            EngineConfig::BmcZ4VariantDynamic {
                backend: crate::sat_types::SolverBackend::Z4Vmtf,
            },
            // z4-sat Luby geometric backoff — Luby restarts help deep BMC
            EngineConfig::BmcGeometricBackoffZ4Variant {
                initial_depths: 30,
                double_interval: 15,
                max_step: 64,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            },
            // === Random forward simulation (3 configs) ===
            // SAT-free exploration: millions of steps/sec. Won't find Sokoban
            // solutions (require specific sequences) but provides zero-cost
            // diversity for bugs reachable via many paths. Different seeds
            // give independent random walks for maximum coverage.
            EngineConfig::RandomSim {
                steps_per_walk: 1_000_000,
                num_walks: 100,
                seed: 1,
            },
            EngineConfig::RandomSim {
                steps_per_walk: 1_000_000,
                num_walks: 100,
                seed: 0xDEAD_BEEF,
            },
            EngineConfig::RandomSim {
                steps_per_walk: 10_000_000,
                num_walks: 10,
                seed: 0xCAFE_BABE,
            },
            // === IC3 (7 configs — union of #4247 small-UNSAT set and #4259 Tier 1) ===
            //
            // #4247 established that "SAT-likely" circuits may still be UNSAT
            // (microban_1_UNSAT shares structure with SAT microban variants but
            // is genuinely UNSAT). #4259 extends this with CTP+INN and predprop
            // variants that cover cal-family industrial UNSAT (cal14/cal42)
            // where forward IC3 alone thrashes on coarse frame approximations.
            // Keep the list disciplined to preserve CPU for the BMC workhorse.
            ic3_conservative(),
            ic3_ctp_inf(),       // strong propagation + frame promotion
            ic3_circuit_adapt(), // auto-tunes CTG for circuit size
            // SimpleSolver IC3 for high-constraint SAT/UNSAT benchmarks (#4092).
            // SimpleSolver is immune to z4-sat's known false-UNSAT bug, providing
            // independent soundness coverage on small UNSAT circuits (#4247).
            ic3_simple_solver(),
            ic3_simple_solver_inn(), // SimpleSolver + internal signals (#4148)
            // CTP + internal signals: covers constraint-heavy UNSAT structure (#4259).
            ic3_inn_ctp(),
            // Predicate propagation: backward analysis for UNSAT circuits where
            // forward IC3 struggles with coarse frame approximations (#4259).
            ic3_predprop_ctp(),
            // === k-Induction (3 configs — union of #4247 and #4259 Tier 1) ===
            // Cal-family (cal14, cal42) is industrial UNSAT; k-induction is the
            // workhorse UNSAT solver per Wave 9 data. Skip-BMC keeps each
            // induction thread focused on proving UNSAT.
            //
            // SOUNDNESS FIX (#4300): KindStrengthened was removed from this
            // SAT-likely portfolio because its BMC-based invariant discovery
            // (5-step reachability check treated as infinite invariant) is
            // unsound on deep-search SAT benchmarks like microban_64/77/89
            // (Sokoban puzzles). The shallow BMC misses real flips that occur
            // at greater depth, producing spurious invariants that let the
            // step solver falsely conclude Safe (= UNSAT). KindStrengthened
            // remains in default_portfolio (UNSAT-heavy circuits) where the
            // pattern is less likely to misfire.
            EngineConfig::KindSkipBmc,
            EngineConfig::KindSkipBmcZ4Variant {
                backend: crate::sat_types::SolverBackend::Z4Luby,
            },
            EngineConfig::KindSimplePath,
        ],
        max_depth: 200000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// SAT-likely heuristic: returns true when the circuit structure suggests
/// the property is likely SAT (a bug exists at some depth).
///
/// Two patterns are detected:
///
/// 1. **High input ratio on medium/large constrained circuits** (#4247, #4259):
///    `num_inputs > 2 * num_latches` AND `num_latches >= 30` AND
///    `!constraint_lits.is_empty()`. Circuits with many primary inputs relative
///    to latches have a large combinational input space that is often not
///    fully constrained, making it more likely that some input combination
///    can drive the circuit into a bad state.
///
///    Two guards prevent misfires on small industrial UNSAT circuits:
///    the constraint guard (#4247) rules out wide-unconstrained-input UNSAT
///    circuits (cal14: 23L/53I/0 constraints), and the latch-count guard
///    (#4259) rules out small circuits generally (cal42: 79L/180I with
///    constraints but still UNSAT). `sat_focused_portfolio` also runs an
///    expanded IC3/kind safety net (7 IC3 + 4 kind configs) so borderline
///    UNSAT circuits like microban_1_UNSAT (I=L=23, 124 constraints
///    triggering Pattern 2) still get proof coverage.
///
/// 2. **Sokoban/microban pattern** (#4149): `num_inputs == num_latches` AND
///    `constraint_count > 4 * num_latches`. These are game/puzzle encodings
///    where each action input corresponds to a state latch and the game rules
///    are encoded as environment constraints. Most HWMCC microban SAT puzzles
///    match this pattern (I=L, constraints/latches ratio 5-16x). rIC3 solves
///    these via deep BMC in 0.2-4.3s; they need deep unrolling to find the
///    winning game sequence (counterexample).
///
/// When this heuristic triggers, `portfolio_check_detailed` uses `sat_focused_portfolio()`
/// which allocates more threads to BMC configs with deeper step sizes (#4123, #4149).
pub(crate) fn is_sat_likely(ts: &crate::transys::Transys) -> bool {
    if ts.num_latches == 0 {
        return false;
    }
    // Pattern 1: many inputs relative to latches. Two guards prevent misfires
    // on small industrial UNSAT circuits:
    //   - Constraint guard (#4247): rules out circuits with wide unconstrained
    //     input interfaces (cal14: 23L/53I/0 constraints — UNSAT, solved by
    //     IC3 in 0.14s by rIC3).
    //   - Latch-count guard (#4259): rules out small circuits in general where
    //     I/L ratio is not a reliable SAT signal (cal42: 79L/180I — still UNSAT
    //     despite some constraints). Requiring >= 30 latches keeps the
    //     heuristic active on genuinely SAT-heavy medium circuits.
    // sat_focused_portfolio() also now runs an expanded IC3/kind safety net so
    // borderline UNSAT circuits (microban_1_UNSAT: I=L=23, 124 constraints
    // triggering Pattern 2) still get proof coverage even if classification
    // slips through.
    if ts.num_latches >= 30 && ts.num_inputs > 2 * ts.num_latches && !ts.constraint_lits.is_empty()
    {
        return true;
    }
    // Pattern 2: Sokoban/microban style — inputs == latches, heavy constraints
    // Microban puzzles: I=L (40-60), constraints = 5-16x latches (200-940).
    // The constraint ratio distinguishes game puzzles from ordinary sequential
    // circuits that happen to have I==L.
    if ts.num_inputs == ts.num_latches && ts.constraint_lits.len() > 4 * ts.num_latches {
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_types::SolverBackend;

    /// Compute the ordered sequence of depths at which `BmcLinearOffset` will
    /// invoke a SAT check, mirroring the loop in
    /// `BmcEngine::check_linear_offset` (`crates/tla-aiger/src/bmc/engine.rs`).
    ///
    /// For `step == 1`, a check fires after every unroll starting at
    /// `start_depth + 1`. For `step >= 2`, the any-depth accumulator fires at
    /// the end of each step window — so the first check depth is
    /// `start_depth + step`, then `start_depth + 2*step`, etc., capped at
    /// `max_depth`. Kept as a pure helper so the depth sequence can be unit
    /// tested without spinning up a SAT solver.
    fn linear_offset_check_depths(start_depth: usize, step: usize, max_depth: usize) -> Vec<usize> {
        let step = step.max(1);
        let mut depths = Vec::new();
        let mut k = start_depth.min(max_depth);
        while k < max_depth {
            if step == 1 {
                k += 1;
                depths.push(k);
            } else {
                let target = (k + step).min(max_depth);
                k = target;
                depths.push(k);
            }
        }
        depths
    }

    /// (i) `BmcLinearOffset { start_depth: 50, step: 50, max_depth: 250 }`
    /// visits depths 100, 150, 200, 250. Documents the semantics that the
    /// step=50 variant hits every 50-depth boundary past the skip region.
    #[test]
    fn bmc_linear_offset_step_50_yields_50_depth_intervals() {
        let depths = linear_offset_check_depths(50, 50, 250);
        assert_eq!(depths, vec![100, 150, 200, 250]);
    }

    /// (ii) `BmcLinearOffset { start_depth: 100, step: 100, max_depth: 500 }`
    /// visits depths 200, 300, 400, 500 — one SAT check per 100-depth band.
    #[test]
    fn bmc_linear_offset_step_100_yields_100_depth_intervals() {
        let depths = linear_offset_check_depths(100, 100, 500);
        assert_eq!(depths, vec![200, 300, 400, 500]);
    }

    /// (iii-a) `sat_focused_portfolio()` allocates both `BmcLinearOffset`
    /// engines that Wave 29 design Change 1 specifies: `(start=50,
    /// max=600)` and `(start=150, max=800)`, both at `step=1`.
    #[test]
    fn sat_focused_portfolio_contains_both_bmc_linear_offset_engines() {
        let portfolio = sat_focused_portfolio();
        let mut saw_start_50 = false;
        let mut saw_start_150 = false;
        for engine in &portfolio.engines {
            if let EngineConfig::BmcLinearOffset {
                start_depth,
                step,
                max_depth,
            } = engine
            {
                if *start_depth == 50 && *step == 1 && *max_depth == 600 {
                    saw_start_50 = true;
                }
                if *start_depth == 150 && *step == 1 && *max_depth == 800 {
                    saw_start_150 = true;
                }
            }
        }
        assert!(
            saw_start_50,
            "sat_focused_portfolio missing BmcLinearOffset {{ start_depth: 50, step: 1, max_depth: 600 }}"
        );
        assert!(
            saw_start_150,
            "sat_focused_portfolio missing BmcLinearOffset {{ start_depth: 150, step: 1, max_depth: 800 }}"
        );
    }

    /// (iii-b) `sat_focused_portfolio()` allocates both SimpleSolver
    /// BMC step=50 and step=100 engines that Wave 29 design Change 2
    /// specifies. SimpleSolver never produces false UNSAT, so these
    /// large-step configs leap over regions where z4-sat thrashes on
    /// Sokoban constraint density.
    #[test]
    fn sat_focused_portfolio_contains_simple_solver_step_50_and_100() {
        let portfolio = sat_focused_portfolio();
        let mut saw_step_50 = false;
        let mut saw_step_100 = false;
        for engine in &portfolio.engines {
            if let EngineConfig::BmcZ4Variant { step, backend } = engine {
                if matches!(backend, SolverBackend::Simple) {
                    if *step == 50 {
                        saw_step_50 = true;
                    }
                    if *step == 100 {
                        saw_step_100 = true;
                    }
                }
            }
        }
        assert!(
            saw_step_50,
            "sat_focused_portfolio missing BmcZ4Variant {{ step: 50, backend: Simple }}"
        );
        assert!(
            saw_step_100,
            "sat_focused_portfolio missing BmcZ4Variant {{ step: 100, backend: Simple }}"
        );
    }
}
