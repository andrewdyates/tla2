// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use super::*;

pub(super) fn simple_net() -> PetriNet {
    // p0 -> t0 -> p1, initial marking [3, 0]
    PetriNet {
        name: Some("test".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: "t0".to_string(),
            name: None,
            inputs: vec![Arc {
                place: PlaceIdx(0),
                weight: 1,
            }],
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 1,
            }],
        }],
        initial_marking: vec![3, 0],
    }
}

pub(super) fn prefire_guard_net() -> PetriNet {
    PetriNet {
        name: Some("prefire-guard".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: "t0".to_string(),
            name: None,
            inputs: vec![Arc {
                place: PlaceIdx(0),
                weight: 1,
            }],
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 1,
            }],
        }],
        initial_marking: vec![1, 0],
    }
}

pub(super) fn prefire_overflow_net() -> PetriNet {
    PetriNet {
        name: Some("prefire-overflow".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p2".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "q0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "q1".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t_over".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: u64::MAX,
                }],
            },
            TransitionInfo {
                id: "t_cycle_fwd".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "t_cycle_back".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "q_enable".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(4),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "q_goal".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(4),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![2, 0, 0, 0, 1],
    }
}

pub(super) fn query_slice_budget_net() -> PetriNet {
    PetriNet {
        name: Some("reachability-query-slice-budget".to_string()),
        places: vec![
            PlaceInfo {
                id: "r0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "r1".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i0_l".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i0_r".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i1_l".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i1_r".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i2_l".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i2_r".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "i0_f".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i0_b".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i1_f".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(4),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(5),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i1_b".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(5),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(4),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i2_f".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(6),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(7),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i2_b".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(7),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(6),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "t0".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "t1".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "t2".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![],
            },
        ],
        initial_marking: vec![1, 1, 1, 0, 1, 0, 1, 0],
    }
}

pub(super) fn make_ef_prop(id: &str, pred: StatePredicate) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Reachability(ReachabilityFormula {
            quantifier: PathQuantifier::EF,
            predicate: pred,
        }),
    }
}

pub(super) fn make_ag_prop(id: &str, pred: StatePredicate) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Reachability(ReachabilityFormula {
            quantifier: PathQuantifier::AG,
            predicate: pred,
        }),
    }
}

pub(super) fn default_config() -> ExplorationConfig {
    ExplorationConfig::new(10_000)
}

pub(super) fn parallel_config() -> ExplorationConfig {
    ExplorationConfig::new(10_000).with_workers(4)
}

pub(super) fn parallel_budget_config(max_states: usize) -> ExplorationConfig {
    ExplorationConfig::new(max_states).with_workers(4)
}

pub(super) fn check_reachability_properties_unsliced(
    net: &PetriNet,
    properties: &[Property],
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    let (prepared, mut trackers) = prepare_trackers(net, properties);
    let max_bmc_depth;
    if !trackers.is_empty() {
        max_bmc_depth = super::super::super::reachability_bmc::run_bmc_seeding(
            net,
            &mut trackers,
            config.deadline(),
        );
        if trackers.iter().all(|tracker| tracker.verdict.is_some()) {
            return assemble_results(&prepared, &trackers, true, false);
        }
    } else {
        max_bmc_depth = None;
    }

    if !trackers.is_empty() {
        super::super::super::reachability_lp::run_lp_seeding(net, &mut trackers);
        if trackers.iter().all(|tracker| tracker.verdict.is_some()) {
            return assemble_results(&prepared, &trackers, true, false);
        }
    }

    // Mirror Phase 2c: PDR seeding (matches production pipeline order).
    if trackers.iter().any(|tracker| tracker.verdict.is_none()) {
        super::super::super::reachability_pdr::run_pdr_seeding(
            net,
            &mut trackers,
            config.deadline(),
        );
        if trackers.iter().all(|tracker| tracker.verdict.is_some()) {
            return assemble_results(&prepared, &trackers, true, false);
        }
    }

    // Mirror Phase 2d: k-induction seeding (matches production pipeline order).
    if trackers.iter().any(|tracker| tracker.verdict.is_none()) {
        super::super::super::kinduction::run_kinduction_seeding(
            net,
            &mut trackers,
            config.deadline(),
            max_bmc_depth,
        );
        if trackers.iter().all(|tracker| tracker.verdict.is_some()) {
            return assemble_results(&prepared, &trackers, true, false);
        }
    }

    let reduced = reduce_reachability_queries(net, &trackers)
        .expect("query-protected reduction should succeed");
    let (result, trackers) = explore_reachability_on_reduced_net(net, &reduced, trackers, config)
        .expect("reduced-net exploration should not overflow");
    assemble_results(&prepared, &trackers, result.completed, false)
}

pub(super) fn write_fake_solver_script(dir: &Path, name: &str, body: &str) -> PathBuf {
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

pub(super) fn with_z4_path<T>(path: &Path, f: impl FnOnce() -> T) -> T {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    let _guard = LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .expect("z4 env lock should not be poisoned");
    let previous = std::env::var("Z4_PATH").ok();
    std::env::set_var("Z4_PATH", path);
    let result = f();
    match previous {
        Some(value) => std::env::set_var("Z4_PATH", value),
        None => std::env::remove_var("Z4_PATH"),
    }
    result
}

/// P0(1) --T0--> P1: fires once then deadlocks. State space has 2 markings.
pub(super) fn linear_deadlock_net() -> PetriNet {
    PetriNet {
        name: Some("linear-deadlock".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: "T0".into(),
            name: None,
            inputs: vec![Arc {
                place: PlaceIdx(0),
                weight: 1,
            }],
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 1,
            }],
        }],
        initial_marking: vec![1, 0],
    }
}
