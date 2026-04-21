// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use tempfile::TempDir;

use crate::petri_net::PetriNet;

use super::{
    emit_bmc_incremental_preamble, run_depth_ladder, run_depth_ladder_incremental, DepthAction,
    DepthQuery, IncrementalPropertyQuery, SolverOutcome,
};

fn write_fake_solver_script(dir: &Path, name: &str, body: &str) -> PathBuf {
    let path = dir.join(name);
    let script = format!("#!/bin/sh\nset -eu\n{body}\n");
    fs::write(&path, script).expect("failed to write fake solver script");
    #[cfg(unix)]
    {
        let mut perms = fs::metadata(&path)
            .expect("script metadata should exist")
            .permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&path, perms).expect("failed to mark fake solver executable");
    }
    path
}

fn empty_net() -> PetriNet {
    PetriNet {
        name: Some("empty".to_string()),
        places: vec![],
        transitions: vec![],
        initial_marking: vec![],
    }
}

#[test]
fn test_run_depth_ladder_returns_last_explored_depth_before_unknown() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let state_path = tempdir.path().join("state");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-depth-runner-unknown",
        &format!(
            "printf 'call\\n' >> \"{}\"\ncat >/dev/null\nif [ ! -f \"{}\" ]; then\n  : > \"{}\"\n  printf 'unsat\\n'\nelse\n  printf 'unknown\\n'\nfi",
            calls_path.display(),
            state_path.display(),
            state_path.display()
        ),
    );

    let mut built_depths = Vec::new();
    let max_depth = run_depth_ladder(
        &solver,
        &[1, 2, 4],
        None,
        Duration::from_secs(1),
        &mut built_depths,
        |built_depths, depth| {
            built_depths.push(depth);
            Some(DepthQuery::new("(check-sat)\n".to_string(), 1))
        },
        |_, _, results| match results {
            Some([SolverOutcome::Unsat]) => DepthAction::Explored,
            Some([SolverOutcome::Unknown]) | None => DepthAction::StopDeepening,
            other => panic!("unexpected solver result: {other:?}"),
        },
    );

    if calls_path.exists() {
        assert_eq!(max_depth, Some(1));
        assert_eq!(built_depths, vec![1, 2]);
        assert_eq!(
            fs::read_to_string(&calls_path)
                .expect("call log should exist")
                .lines()
                .count(),
            2,
            "the helper should stop before trying the third ladder depth"
        );
    } else {
        assert_eq!(max_depth, None);
        assert_eq!(
            built_depths,
            vec![1],
            "solver startup failure should stop deepening after the first attempted depth"
        );
    }
}

#[test]
fn test_run_depth_ladder_stops_when_builder_has_no_more_work() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-depth-runner-no-more-work",
        &format!(
            "printf 'call\\n' >> \"{}\"\ncat >/dev/null\nprintf 'unsat\\n'",
            calls_path.display()
        ),
    );

    let mut built_depths = Vec::new();
    let max_depth = run_depth_ladder(
        &solver,
        &[1, 2, 4],
        None,
        Duration::from_secs(1),
        &mut built_depths,
        |built_depths, depth| {
            built_depths.push(depth);
            if depth == 1 {
                Some(DepthQuery::new("(check-sat)\n".to_string(), 1))
            } else {
                None
            }
        },
        |_, _, results| match results {
            Some([SolverOutcome::Unsat]) => DepthAction::Explored,
            None => DepthAction::StopDeepening,
            other => panic!("unexpected solver result: {other:?}"),
        },
    );

    if calls_path.exists() {
        assert_eq!(max_depth, Some(1));
        assert_eq!(built_depths, vec![1, 2]);
        assert_eq!(
            fs::read_to_string(&calls_path)
                .expect("call log should exist")
                .lines()
                .count(),
            1,
            "the helper should not invoke the solver after build_query returns None"
        );
    } else {
        assert_eq!(max_depth, None);
        assert_eq!(
            built_depths,
            vec![1],
            "solver startup failure should stop before the builder reaches the second depth"
        );
    }
}

#[test]
fn test_incremental_depth_ladder_skips_next_depth_when_builder_has_no_more_work() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let stdin_log_path = tempdir.path().join("stdin.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-incremental-no-more-work",
        &format!(
            "probe_done=0\nwhile IFS= read -r line; do\n  printf '%s\\n' \"$line\" >> \"{}\"\n  case \"$line\" in\n    \"(check-sat)\")\n      if [ \"$probe_done\" -eq 0 ]; then\n        probe_done=1\n        printf 'sat\\n'\n      else\n        printf 'unsat\\n'\n      fi\n      ;;\n    \"(exit)\")\n      exit 0\n      ;;\n  esac\ndone",
            stdin_log_path.display()
        ),
    );
    let net = empty_net();
    let mut built_depths = Vec::new();

    let max_depth = run_depth_ladder_incremental(
        &solver,
        &[1, 2],
        None,
        Duration::from_secs(1),
        &net,
        &mut built_depths,
        emit_bmc_incremental_preamble,
        |built_depths, depth| {
            built_depths.push(depth);
            (depth == 1).then(|| IncrementalPropertyQuery {
                assertions: vec!["(assert true)\n".to_string()],
            })
        },
        |_, _, results| match results {
            Some([SolverOutcome::Unsat]) => DepthAction::Explored,
            Some([SolverOutcome::Unknown]) | None => DepthAction::StopDeepening,
            other => panic!("unexpected solver result: {other:?}"),
        },
        |_, _| panic!("incremental solver should not fall back to batch mode"),
        |_, _, _| panic!("incremental solver should not fall back to batch mode"),
    );

    assert_eq!(max_depth, Some(1));
    assert_eq!(built_depths, vec![1, 2]);

    let stdin_log = fs::read_to_string(&stdin_log_path).expect("stdin log should exist");
    assert_eq!(
        stdin_log.matches("(check-sat)").count(),
        2,
        "only the startup probe plus one property check should run after the builder returns None"
    );
    assert!(
        !stdin_log.contains("(assert (or stay_1))"),
        "the runner should not encode transition constraints for depth 2 when there is no work left: {stdin_log}"
    );
}

#[test]
fn test_incremental_depth_ladder_shares_one_timeout_budget_across_properties() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let stdin_log_path = tempdir.path().join("stdin.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-incremental-shared-timeout",
        &format!(
            "probe_done=0\nwhile IFS= read -r line; do\n  printf '%s\\n' \"$line\" >> \"{}\"\n  case \"$line\" in\n    \"(check-sat)\")\n      if [ \"$probe_done\" -eq 0 ]; then\n        probe_done=1\n        printf 'sat\\n'\n      else\n        sleep 0.12\n        printf 'unsat\\n'\n      fi\n      ;;\n    \"(exit)\")\n      exit 0\n      ;;\n  esac\ndone",
            stdin_log_path.display()
        ),
    );
    let net = empty_net();
    let mut seen_results = Vec::new();

    let max_depth = run_depth_ladder_incremental(
        &solver,
        &[1],
        None,
        Duration::from_millis(200),
        &net,
        &mut seen_results,
        emit_bmc_incremental_preamble,
        |_, _| {
            Some(IncrementalPropertyQuery {
                assertions: vec!["(assert true)\n".to_string(), "(assert true)\n".to_string()],
            })
        },
        |seen_results, _, results| {
            let outcomes = results.expect("incremental run should still report outcomes");
            seen_results.push(outcomes.to_vec());
            if outcomes
                .iter()
                .all(|outcome| *outcome == SolverOutcome::Unsat)
            {
                DepthAction::Explored
            } else {
                DepthAction::StopDeepening
            }
        },
        |_, _| panic!("incremental solver should not fall back to batch mode"),
        |_, _, _| panic!("incremental solver should not fall back to batch mode"),
    );

    assert_eq!(max_depth, None);
    assert_eq!(
        seen_results,
        vec![vec![SolverOutcome::Unsat, SolverOutcome::Unknown]],
        "the second property should inherit only the remaining depth budget"
    );

    let stdin_log = fs::read_to_string(&stdin_log_path).expect("stdin log should exist");
    assert_eq!(
        stdin_log.matches("(check-sat)").count(),
        3,
        "the runner should begin the second query after the startup probe and before the shared depth budget expires"
    );
}
