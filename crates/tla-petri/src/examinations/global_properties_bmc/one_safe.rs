// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Instant;

use crate::petri_net::PetriNet;

use super::super::bmc_runner::{emit_bmc_preamble, emit_kinduction_preamble};
use super::super::smt_encoding::find_z4;
use super::{run_bmc_and_kinduction, BmcKindConfig};

/// Run BMC + k-induction for the OneSafe examination.
///
/// Returns `Some(true)` if 1-safety is proved (k-induction),
/// `Some(false)` if a violation is found (BMC witness),
/// `None` if inconclusive.
pub(crate) fn run_one_safe_bmc(net: &PetriNet, deadline: Option<Instant>) -> Option<bool> {
    let z4_path = find_z4()?;

    run_bmc_and_kinduction(
        &z4_path,
        net,
        deadline,
        &BmcKindConfig {
            exam_name: "OneSafe",
            bmc_sat_value: false,
            kind_unsat_value: true,
        },
        encode_one_safe_bmc_script,
        encode_one_safe_kinduction_script,
    )
}

pub(super) fn encode_one_safe_bmc_script(net: &PetriNet, depth: usize) -> String {
    let np = net.num_places();
    let mut s = String::with_capacity(4096);
    emit_bmc_preamble(&mut s, net, depth);

    // Goal: OR over steps 0..=depth of (OR over places: m > 1)
    s.push_str("(assert (or");
    for step in 0..=depth {
        for place in 0..np {
            s.push_str(&format!(" (>= m_{}_{} 2)", step, place));
        }
    }
    s.push_str("))\n");
    s.push_str("(check-sat)\n(exit)\n");
    s
}

pub(super) fn encode_one_safe_kinduction_script(net: &PetriNet, depth: usize) -> String {
    let np = net.num_places();
    let mut s = String::with_capacity(4096);
    emit_kinduction_preamble(&mut s, net, depth);

    // Hypothesis: all places <= 1 at steps 0..depth-1
    for step in 0..depth {
        for place in 0..np {
            s.push_str(&format!("(assert (<= m_{}_{} 1))\n", step, place));
        }
    }

    // Check: some place > 1 at step depth
    if np == 1 {
        s.push_str(&format!("(assert (>= m_{}_0 2))\n", depth));
    } else {
        s.push_str("(assert (or");
        for place in 0..np {
            s.push_str(&format!(" (>= m_{}_{} 2)", depth, place));
        }
        s.push_str("))\n");
    }

    s.push_str("(check-sat)\n(exit)\n");
    s
}
