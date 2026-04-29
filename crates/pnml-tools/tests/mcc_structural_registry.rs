// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::{Path, PathBuf};

use pnml_tools::examination::Examination;
use pnml_tools::explorer::ExplorationConfig;
use pnml_tools::parser::parse_pnml_dir;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn mcc_model_dir(model: &str) -> PathBuf {
    workspace_root()
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

fn has_mcc_benchmark(model: &str) -> bool {
    mcc_model_dir(model).join("model.pnml").exists()
}

fn registry_path(file_name: &str) -> PathBuf {
    workspace_root()
        .join("registry")
        .join("mcc-labels")
        .join(file_name)
}

fn formula_index(formula_id: &str) -> usize {
    formula_id
        .rsplit_once('-')
        .expect("formula id should contain an index suffix")
        .1
        .parse::<usize>()
        .expect("formula index should parse")
}

fn load_bool_registry(path: &Path, model: &str) -> Vec<String> {
    let contents = std::fs::read_to_string(path).expect("registry CSV should read");
    let mut rows: Vec<(usize, String)> = contents
        .lines()
        .filter_map(|line| {
            let (lhs, rhs) = line.split_once(',')?;
            let (row_model, raw_index) = lhs.rsplit_once('/')?;
            if row_model != model {
                return None;
            }
            let index = raw_index
                .parse::<usize>()
                .expect("registry formula index should parse");
            let verdict = match rhs {
                "true" => String::from("TRUE"),
                "false" => String::from("FALSE"),
                other => panic!("unexpected registry verdict {other}"),
            };
            Some((index, verdict))
        })
        .collect();
    rows.sort_by_key(|(index, _)| *index);
    assert!(
        !rows.is_empty(),
        "registry should contain entries for the requested model"
    );
    rows.into_iter().map(|(_, verdict)| verdict).collect()
}

fn load_upper_bounds_registry(path: &Path, model: &str) -> Vec<u64> {
    let contents = std::fs::read_to_string(path).expect("registry CSV should read");
    let line = contents
        .lines()
        .find(|line| line.starts_with(&format!("{model},")))
        .unwrap_or_else(|| panic!("registry should contain upper-bounds row for {model}"));
    let (_, raw_values) = line
        .split_once(',')
        .expect("upper-bounds registry row should contain a comma");
    raw_values
        .split_whitespace()
        .map(|value| {
            value
                .parse::<u64>()
                .unwrap_or_else(|err| panic!("upper-bounds value should parse: {err}"))
        })
        .collect()
}

#[test]
fn test_reachability_cardinality_angiogenesis_matches_registry_via_public_api() {
    const MODEL: &str = "Angiogenesis-PT-01";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let model_dir = mcc_model_dir(MODEL);
    let net = parse_pnml_dir(&model_dir).expect("real benchmark PNML should parse");
    let config = ExplorationConfig::new(10_000).with_workers(1);
    let actual = pnml_tools::examination::check_reachability(
        &net,
        &model_dir,
        Examination::ReachabilityCardinality,
        &config,
    )
    .expect("ReachabilityCardinality property XML should parse");
    let expected = load_bool_registry(&registry_path("reachability-cardinality-2024.csv"), MODEL);

    assert_eq!(
        actual.len(),
        expected.len(),
        "registry/property arity should match"
    );
    for (id, verdict) in actual {
        let index = formula_index(&id);
        assert_eq!(
            verdict, expected[index],
            "{id} should match MCC reachability-cardinality registry"
        );
    }
}

#[test]
fn test_upper_bounds_angiogenesis_matches_registry_via_public_api() {
    const MODEL: &str = "Angiogenesis-PT-01";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let model_dir = mcc_model_dir(MODEL);
    let net = parse_pnml_dir(&model_dir).expect("real benchmark PNML should parse");
    let config = ExplorationConfig::new(10_000).with_workers(1);
    let actual = pnml_tools::examination::check_upper_bounds(&net, &model_dir, &config)
        .expect("UpperBounds property XML should parse");
    let expected = load_upper_bounds_registry(&registry_path("upper-bounds-2024.csv"), MODEL);

    assert_eq!(
        actual.len(),
        expected.len(),
        "registry/property arity should match"
    );
    for (id, maybe_bound) in actual {
        let index = formula_index(&id);
        let bound = maybe_bound.unwrap_or_else(|| panic!("{id} should resolve to a numeric bound"));
        assert_eq!(
            bound, expected[index],
            "{id} should match MCC upper-bounds registry"
        );
    }
}

#[test]
fn test_upper_bounds_angiogenesis_partial_structural_results_match_registry_via_public_api() {
    const MODEL: &str = "Angiogenesis-PT-01";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let model_dir = mcc_model_dir(MODEL);
    let net = parse_pnml_dir(&model_dir).expect("real benchmark PNML should parse");
    let config = ExplorationConfig::new(1).with_workers(1);
    let actual = pnml_tools::examination::check_upper_bounds(&net, &model_dir, &config)
        .expect("UpperBounds property XML should parse");
    let expected = load_upper_bounds_registry(&registry_path("upper-bounds-2024.csv"), MODEL);

    let resolved: Vec<_> = actual
        .into_iter()
        .filter_map(|(id, maybe_bound)| maybe_bound.map(|bound| (id, bound)))
        .collect();

    assert!(
        !resolved.is_empty(),
        "expected at least one structurally certified UpperBounds result at a 1-state budget"
    );
    for (id, bound) in resolved {
        let index = formula_index(&id);
        assert_eq!(
            bound, expected[index],
            "{id} should only emit registry-correct structural exactness under an incomplete run"
        );
    }
}
