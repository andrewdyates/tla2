// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Criterion benchmarks for BTOR2 parsing speed on HWMCC'25 benchmarks.
//!
//! Target: parse all ~330 BTOR2 files (word-level BV) in under 1 second.
//!
//! Run with: cargo bench -p tla-btor2

use std::path::PathBuf;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use tla_btor2::parser::parse;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn hwmcc_bv_dir() -> PathBuf {
    let home = std::env::var("HOME").expect("HOME not set");
    PathBuf::from(home).join("hwmcc/benchmarks/wordlevel/bv")
}

/// Recursively find all .btor2 files under a directory.
fn find_btor2_files(dir: &PathBuf) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if !dir.exists() {
        return files;
    }
    collect_btor2_recursive(dir, &mut files);
    files.sort();
    files
}

fn collect_btor2_recursive(dir: &PathBuf, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_btor2_recursive(&path, out);
        } else if path.extension().is_some_and(|e| e == "btor2") {
            out.push(path);
        }
    }
}

/// Pre-load all BTOR2 file contents into memory to benchmark parsing only
/// (not I/O).
fn preload_files(files: &[PathBuf]) -> Vec<(String, String)> {
    files
        .iter()
        .filter_map(|path| {
            let contents = std::fs::read_to_string(path).ok()?;
            let name = path
                .file_name()
                .map(|f| f.to_string_lossy().to_string())
                .unwrap_or_default();
            Some((name, contents))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Benchmarks
// ---------------------------------------------------------------------------

/// Benchmark parsing individual BEEM protocol benchmarks.
///
/// These are small (500-4000 lines) and represent the directly TLA2-relevant
/// hardware model checking problems.
fn bench_parse_beem(c: &mut Criterion) {
    let beem_dir = hwmcc_bv_dir().join("2019/beem");
    let files = find_btor2_files(&beem_dir);
    if files.is_empty() {
        eprintln!("SKIP: no BEEM benchmarks found at {}", beem_dir.display());
        return;
    }

    let preloaded = preload_files(&files);

    let mut group = c.benchmark_group("btor2_parse_beem");
    for (name, contents) in &preloaded {
        group.throughput(Throughput::Bytes(contents.len() as u64));
        group.bench_with_input(BenchmarkId::new("parse", name), contents, |b, src| {
            b.iter(|| {
                let prog = parse(black_box(src)).expect("parse should succeed");
                black_box(&prog);
            });
        });
    }
    group.finish();
}

/// Benchmark parsing a representative selection of benchmarks by size class.
fn bench_parse_by_size(c: &mut Criterion) {
    let bv_dir = hwmcc_bv_dir();
    let all_files = find_btor2_files(&bv_dir);
    if all_files.is_empty() {
        eprintln!("SKIP: no BTOR2 files found at {}", bv_dir.display());
        return;
    }

    let preloaded = preload_files(&all_files);

    // Classify by size: small (<1KB), medium (1-10KB), large (10-100KB), xlarge (>100KB).
    let mut small_count = 0usize;
    let mut medium_count = 0usize;
    let mut large_count = 0usize;
    let mut xlarge_count = 0usize;
    let mut small_rep: Option<&(String, String)> = None;
    let mut medium_rep: Option<&(String, String)> = None;
    let mut large_rep: Option<&(String, String)> = None;
    let mut xlarge_rep: Option<&(String, String)> = None;

    for entry in &preloaded {
        let len = entry.1.len();
        if len < 1024 {
            small_count += 1;
            if small_rep.is_none() {
                small_rep = Some(entry);
            }
        } else if len < 10_240 {
            medium_count += 1;
            if medium_rep.is_none() {
                medium_rep = Some(entry);
            }
        } else if len < 102_400 {
            large_count += 1;
            if large_rep.is_none() {
                large_rep = Some(entry);
            }
        } else {
            xlarge_count += 1;
            if xlarge_rep.is_none() {
                xlarge_rep = Some(entry);
            }
        }
    }

    let mut group = c.benchmark_group("btor2_parse_size_class");

    // Bench one representative from each size class.
    if let Some((name, contents)) = small_rep {
        group.throughput(Throughput::Bytes(contents.len() as u64));
        group.bench_with_input(BenchmarkId::new("small", name), contents, |b, src| {
            b.iter(|| {
                let prog = parse(black_box(src)).expect("parse failed");
                black_box(&prog);
            });
        });
    }

    if let Some((name, contents)) = medium_rep {
        group.throughput(Throughput::Bytes(contents.len() as u64));
        group.bench_with_input(BenchmarkId::new("medium", name), contents, |b, src| {
            b.iter(|| {
                let prog = parse(black_box(src)).expect("parse failed");
                black_box(&prog);
            });
        });
    }

    if let Some((name, contents)) = large_rep {
        group.throughput(Throughput::Bytes(contents.len() as u64));
        group.bench_with_input(BenchmarkId::new("large", name), contents, |b, src| {
            b.iter(|| {
                let prog = parse(black_box(src)).expect("parse failed");
                black_box(&prog);
            });
        });
    }

    if let Some((name, contents)) = xlarge_rep {
        group.throughput(Throughput::Bytes(contents.len() as u64));
        group.bench_with_input(BenchmarkId::new("xlarge", name), contents, |b, src| {
            b.iter(|| {
                let prog = parse(black_box(src)).expect("parse failed");
                black_box(&prog);
            });
        });
    }

    group.finish();

    eprintln!(
        "Size distribution: {} small, {} medium, {} large, {} xlarge ({} total)",
        small_count,
        medium_count,
        large_count,
        xlarge_count,
        preloaded.len()
    );
}

/// Benchmark parsing ALL HWMCC'25 BV benchmarks in a single batch.
///
/// This is the key metric: can we parse all ~330 files in under 1 second?
fn bench_parse_all_hwmcc(c: &mut Criterion) {
    let bv_dir = hwmcc_bv_dir();
    let all_files = find_btor2_files(&bv_dir);
    if all_files.is_empty() {
        eprintln!("SKIP: no BTOR2 files found at {}", bv_dir.display());
        return;
    }

    let preloaded = preload_files(&all_files);
    let total_bytes: u64 = preloaded.iter().map(|(_, c)| c.len() as u64).sum();

    let mut group = c.benchmark_group("btor2_parse_all");
    group.throughput(Throughput::Bytes(total_bytes));
    group.sample_size(10); // Fewer samples since this parses hundreds of files.

    group.bench_function(
        BenchmarkId::new("all_hwmcc_bv", format!("{}_files", preloaded.len())),
        |b| {
            b.iter(|| {
                let mut total_lines = 0usize;
                for (_, src) in &preloaded {
                    let prog = parse(black_box(src)).expect("parse failed");
                    total_lines += prog.lines.len();
                }
                black_box(total_lines);
            });
        },
    );

    group.finish();

    eprintln!(
        "Benchmarked parsing {} files ({:.1} MB total)",
        preloaded.len(),
        total_bytes as f64 / 1_048_576.0
    );
}

criterion_group!(
    benches,
    bench_parse_beem,
    bench_parse_by_size,
    bench_parse_all_hwmcc
);
criterion_main!(benches);
