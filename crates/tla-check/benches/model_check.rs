// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Benchmarks comparing sequential vs parallel model checking
//!
//! Run with: cargo bench -p tla-check

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use tla_check::{check_module, check_module_parallel, Config};
use tla_core::{lower, parse_to_syntax_tree, FileId};

/// Helper to parse a module from source
fn parse_module(src: &str) -> tla_core::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let result = lower(FileId(0), &tree);
    result.module.expect("Failed to parse module")
}

/// Small counter spec - 10 states
fn small_counter_spec() -> &'static str {
    r#"
---- MODULE SmallCounter ----
VARIABLE x
Init == x = 0
Next == x < 9 /\ x' = x + 1
InRange == x >= 0 /\ x <= 9
====
"#
}

/// Medium counter spec - ~100 states (two variables, 10x10)
fn medium_counter_spec() -> &'static str {
    r#"
---- MODULE MediumCounter ----
VARIABLE x, y
Init == x \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} /\ y = 0
Next == (x < 9 /\ x' = x + 1 /\ y' = y) \/ (y < 9 /\ y' = y + 1 /\ UNCHANGED x)
InRange == x >= 0 /\ x <= 9 /\ y >= 0 /\ y <= 9
====
"#
}

/// Large counter spec - ~1000 states (10x10x10 minus constraints)
fn large_counter_spec() -> &'static str {
    r#"
---- MODULE LargeCounter ----
VARIABLE x, y, z
Init == x = 0 /\ y = 0 /\ z = 0
Next == (x < 9 /\ x' = x + 1 /\ UNCHANGED <<y, z>>)
     \/ (y < 9 /\ y' = y + 1 /\ UNCHANGED <<x, z>>)
     \/ (z < 9 /\ z' = z + 1 /\ UNCHANGED <<x, y>>)
InRange == x >= 0 /\ x <= 9 /\ y >= 0 /\ y <= 9 /\ z >= 0 /\ z <= 9
====
"#
}

/// Disjunctive transitions spec - branching factor stress test
fn branching_spec() -> &'static str {
    r#"
---- MODULE Branching ----
VARIABLE x
Init == x = 0
Next == x' \in {x + 1, x + 2, x + 3, x + 4, x + 5}
SmallValue == x < 20
====
"#
}

/// Very large state space - ~10,000 states (10x10x10)
fn very_large_spec() -> &'static str {
    r#"
---- MODULE VeryLarge ----
VARIABLE a, b, c, d
Init == a = 0 /\ b = 0 /\ c = 0 /\ d = 0
Next == (a < 9 /\ a' = a + 1 /\ UNCHANGED <<b, c, d>>)
     \/ (b < 9 /\ b' = b + 1 /\ UNCHANGED <<a, c, d>>)
     \/ (c < 9 /\ c' = c + 1 /\ UNCHANGED <<a, b, d>>)
     \/ (d < 9 /\ d' = d + 1 /\ UNCHANGED <<a, b, c>>)
InRange == a >= 0 /\ a <= 9 /\ b >= 0 /\ b <= 9 /\ c >= 0 /\ c <= 9 /\ d >= 0 /\ d <= 9
====
"#
}

/// Mutex spec - 2 processes competing for critical section
fn mutex_spec() -> &'static str {
    r#"
---- MODULE Mutex ----
VARIABLE pc1, pc2, turn
Init == pc1 = "idle" /\ pc2 = "idle" /\ turn = 1
Next == (pc1 = "idle" /\ pc1' = "want" /\ UNCHANGED <<pc2, turn>>)
     \/ (pc1 = "want" /\ (pc2 # "crit" \/ turn = 1) /\ pc1' = "crit" /\ UNCHANGED <<pc2, turn>>)
     \/ (pc1 = "crit" /\ pc1' = "idle" /\ turn' = 2 /\ UNCHANGED pc2)
     \/ (pc2 = "idle" /\ pc2' = "want" /\ UNCHANGED <<pc1, turn>>)
     \/ (pc2 = "want" /\ (pc1 # "crit" \/ turn = 2) /\ pc2' = "crit" /\ UNCHANGED <<pc1, turn>>)
     \/ (pc2 = "crit" /\ pc2' = "idle" /\ turn' = 1 /\ UNCHANGED pc1)
MutualExclusion == ~(pc1 = "crit" /\ pc2 = "crit")
====
"#
}

fn bench_sequential(c: &mut Criterion) {
    let mut group = c.benchmark_group("sequential");

    // Small counter
    {
        let module = parse_module(small_counter_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InRange".to_string()],
            ..Default::default()
        };

        group.bench_function("small_counter", |b| {
            b.iter(|| {
                let result = check_module(black_box(&module), black_box(&config));
                black_box(result)
            });
        });
    }

    // Medium counter
    {
        let module = parse_module(medium_counter_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InRange".to_string()],
            ..Default::default()
        };

        group.bench_function("medium_counter", |b| {
            b.iter(|| {
                let result = check_module(black_box(&module), black_box(&config));
                black_box(result)
            });
        });
    }

    // Large counter
    {
        let module = parse_module(large_counter_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InRange".to_string()],
            ..Default::default()
        };

        group.bench_function("large_counter", |b| {
            b.iter(|| {
                let result = check_module(black_box(&module), black_box(&config));
                black_box(result)
            });
        });
    }

    // Branching
    {
        let module = parse_module(branching_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["SmallValue".to_string()],
            ..Default::default()
        };

        group.bench_function("branching", |b| {
            b.iter(|| {
                let result = check_module(black_box(&module), black_box(&config));
                black_box(result)
            });
        });
    }

    // Very large - ~10,000 states
    {
        let module = parse_module(very_large_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InRange".to_string()],
            ..Default::default()
        };

        group.bench_function("very_large", |b| {
            b.iter(|| {
                let result = check_module(black_box(&module), black_box(&config));
                black_box(result)
            });
        });
    }

    // Mutex - concurrent system
    {
        let module = parse_module(mutex_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["MutualExclusion".to_string()],
            ..Default::default()
        };

        group.bench_function("mutex", |b| {
            b.iter(|| {
                let result = check_module(black_box(&module), black_box(&config));
                black_box(result)
            });
        });
    }

    group.finish();
}

fn bench_parallel(c: &mut Criterion) {
    let mut group = c.benchmark_group("parallel");

    // Small counter - various worker counts
    {
        let module = parse_module(small_counter_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InRange".to_string()],
            ..Default::default()
        };

        for workers in [1, 2, 4] {
            group.bench_with_input(
                BenchmarkId::new("small_counter", workers),
                &workers,
                |b, &workers| {
                    b.iter(|| {
                        let result =
                            check_module_parallel(black_box(&module), black_box(&config), workers);
                        black_box(result)
                    });
                },
            );
        }
    }

    // Medium counter - various worker counts
    {
        let module = parse_module(medium_counter_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InRange".to_string()],
            ..Default::default()
        };

        for workers in [1, 2, 4] {
            group.bench_with_input(
                BenchmarkId::new("medium_counter", workers),
                &workers,
                |b, &workers| {
                    b.iter(|| {
                        let result =
                            check_module_parallel(black_box(&module), black_box(&config), workers);
                        black_box(result)
                    });
                },
            );
        }
    }

    // Large counter - various worker counts
    {
        let module = parse_module(large_counter_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InRange".to_string()],
            ..Default::default()
        };

        for workers in [1, 2, 4] {
            group.bench_with_input(
                BenchmarkId::new("large_counter", workers),
                &workers,
                |b, &workers| {
                    b.iter(|| {
                        let result =
                            check_module_parallel(black_box(&module), black_box(&config), workers);
                        black_box(result)
                    });
                },
            );
        }
    }

    // Branching - various worker counts
    {
        let module = parse_module(branching_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["SmallValue".to_string()],
            ..Default::default()
        };

        for workers in [1, 2, 4] {
            group.bench_with_input(
                BenchmarkId::new("branching", workers),
                &workers,
                |b, &workers| {
                    b.iter(|| {
                        let result =
                            check_module_parallel(black_box(&module), black_box(&config), workers);
                        black_box(result)
                    });
                },
            );
        }
    }

    // Very large - various worker counts
    {
        let module = parse_module(very_large_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["InRange".to_string()],
            ..Default::default()
        };

        for workers in [1, 2, 4, 8] {
            group.bench_with_input(
                BenchmarkId::new("very_large", workers),
                &workers,
                |b, &workers| {
                    b.iter(|| {
                        let result =
                            check_module_parallel(black_box(&module), black_box(&config), workers);
                        black_box(result)
                    });
                },
            );
        }
    }

    // Mutex - various worker counts
    {
        let module = parse_module(mutex_spec());
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["MutualExclusion".to_string()],
            ..Default::default()
        };

        for workers in [1, 2, 4] {
            group.bench_with_input(
                BenchmarkId::new("mutex", workers),
                &workers,
                |b, &workers| {
                    b.iter(|| {
                        let result =
                            check_module_parallel(black_box(&module), black_box(&config), workers);
                        black_box(result)
                    });
                },
            );
        }
    }

    group.finish();
}

fn bench_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("comparison");

    // Direct comparison: sequential vs parallel (4 workers)
    let module = parse_module(medium_counter_spec());
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    group.bench_function("medium_sequential", |b| {
        b.iter(|| {
            let result = check_module(black_box(&module), black_box(&config));
            black_box(result)
        });
    });

    group.bench_function("medium_parallel_4", |b| {
        b.iter(|| {
            let result = check_module_parallel(black_box(&module), black_box(&config), 4);
            black_box(result)
        });
    });

    // Very large comparison - where parallel actually helps
    let large_module = parse_module(very_large_spec());
    let large_config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    group.bench_function("very_large_sequential", |b| {
        b.iter(|| {
            let result = check_module(black_box(&large_module), black_box(&large_config));
            black_box(result)
        });
    });

    group.bench_function("very_large_parallel_4", |b| {
        b.iter(|| {
            let result =
                check_module_parallel(black_box(&large_module), black_box(&large_config), 4);
            black_box(result)
        });
    });

    group.finish();
}

criterion_group!(benches, bench_sequential, bench_parallel, bench_comparison);
criterion_main!(benches);
