// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MCC examination dispatch.
//!
//! Maps examination names to exploration observers and formats output.

use std::path::Path;

use crate::error::PnmlError;
use crate::explorer::ExplorationConfig;
use crate::model::PropertyAliases;
use crate::petri_net::PetriNet;

#[path = "examination_kind.rs"]
mod examination_kind;
#[path = "examination_non_property.rs"]
mod examination_non_property;
#[path = "examination_plan.rs"]
mod examination_plan;

pub use self::examination_kind::Examination;
pub use crate::output::Verdict;

#[cfg(test)]
pub(crate) use self::examination_non_property::{
    deadlock_verdict, liveness_verdict, one_safe_verdict, quasi_liveness_verdict,
    stable_marking_verdict, state_space_stats,
};

// ---------------------------------------------------------------------------
// Typed result model
// ---------------------------------------------------------------------------

/// The value produced by one MCC examination formula or metric.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExaminationValue {
    /// Boolean verdict (TRUE / FALSE / CANNOT_COMPUTE).
    Verdict(Verdict),
    /// Numeric upper bound (or `None` for CANNOT_COMPUTE).
    OptionalBound(Option<u64>),
    /// State-space statistics (or `None` for CANNOT_COMPUTE).
    StateSpace(Option<StateSpaceReport>),
}

/// State-space statistics reported by the StateSpace examination.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct StateSpaceReport {
    /// Total unique reachable markings.
    pub states: usize,
    /// Total transition firings explored.
    pub edges: u64,
    /// Maximum tokens in any single place.
    pub max_token_in_place: u64,
    /// Maximum sum of tokens across all places.
    pub max_token_sum: u64,
}

impl StateSpaceReport {
    /// Create a new state-space report.
    #[must_use]
    pub fn new(states: usize, edges: u64, max_token_in_place: u64, max_token_sum: u64) -> Self {
        Self {
            states,
            edges,
            max_token_in_place,
            max_token_sum,
        }
    }
}

/// One result record from an MCC examination.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExaminationRecord {
    /// Fully-qualified MCC formula identifier (e.g. `"ModelA-PT-001-CTLFireability-03"`).
    pub formula_id: String,
    /// The examination value.
    pub value: ExaminationValue,
}

impl ExaminationRecord {
    /// Create a new examination record.
    #[must_use]
    pub fn new(formula_id: String, value: ExaminationValue) -> Self {
        Self { formula_id, value }
    }

    /// Render this record as an MCC `FORMULA` output line.
    #[must_use]
    pub fn to_mcc_line(&self) -> String {
        match &self.value {
            ExaminationValue::Verdict(v) => {
                format!("FORMULA {} {} TECHNIQUES EXPLICIT", self.formula_id, v)
            }
            ExaminationValue::OptionalBound(Some(b)) => {
                format!("FORMULA {} {} TECHNIQUES EXPLICIT", self.formula_id, b)
            }
            ExaminationValue::OptionalBound(None) => {
                format!(
                    "FORMULA {} CANNOT_COMPUTE TECHNIQUES EXPLICIT",
                    self.formula_id
                )
            }
            ExaminationValue::StateSpace(Some(ss)) => {
                format!(
                    "FORMULA {} {} {} {} {} TECHNIQUES EXPLICIT",
                    self.formula_id, ss.states, ss.edges, ss.max_token_in_place, ss.max_token_sum,
                )
            }
            ExaminationValue::StateSpace(None) => {
                format!(
                    "FORMULA {} CANNOT_COMPUTE TECHNIQUES EXPLICIT",
                    self.formula_id
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Public collector API
// ---------------------------------------------------------------------------

/// Collect examination results as typed records without printing.
///
/// Returns structured [`ExaminationRecord`] values for all 13 MCC examination
/// kinds. Property-based examinations (UpperBounds, Reachability*, CTL*, LTL*)
/// parse their XML from `model_dir`. Non-property examinations ignore
/// `model_dir`.
///
/// Returns `Err(PnmlError)` only for real API/load failures (missing XML, XML
/// parse error, IO error). Computational incompleteness is represented as
/// `CANNOT_COMPUTE` inside the records.
pub fn collect_examination_with_dir(
    net: &PetriNet,
    model_name: &str,
    model_dir: &Path,
    examination: Examination,
    config: &ExplorationConfig,
) -> Result<Vec<ExaminationRecord>, PnmlError> {
    let aliases = PropertyAliases::identity(net);
    collect_examination_core(
        net,
        model_name,
        model_dir,
        &aliases,
        examination,
        config,
        false,
    )
}

pub(crate) fn collect_examination_core(
    net: &PetriNet,
    model_name: &str,
    model_dir: &Path,
    aliases: &PropertyAliases,
    examination: Examination,
    config: &ExplorationConfig,
    flush: bool,
) -> Result<Vec<ExaminationRecord>, PnmlError> {
    match examination {
        // -- Non-property examinations (single record each) --
        Examination::ReachabilityDeadlock => {
            let v = examination_non_property::deadlock_verdict(net, config);
            Ok(vec![ExaminationRecord {
                formula_id: format!("{model_name}-ReachabilityDeadlock"),
                value: ExaminationValue::Verdict(v),
            }])
        }
        Examination::OneSafe => {
            let colored_groups = aliases.colored_place_groups();
            let v = examination_non_property::one_safe_verdict(net, config, &colored_groups);
            Ok(vec![ExaminationRecord {
                formula_id: format!("{model_name}-OneSafe"),
                value: ExaminationValue::Verdict(v),
            }])
        }
        Examination::QuasiLiveness => {
            let v = examination_non_property::quasi_liveness_verdict(net, config);
            Ok(vec![ExaminationRecord {
                formula_id: format!("{model_name}-QuasiLiveness"),
                value: ExaminationValue::Verdict(v),
            }])
        }
        Examination::StableMarking => {
            let colored_groups = aliases.colored_place_groups();
            let v = examination_non_property::stable_marking_verdict(net, config, &colored_groups);
            Ok(vec![ExaminationRecord {
                formula_id: format!("{model_name}-StableMarking"),
                value: ExaminationValue::Verdict(v),
            }])
        }
        Examination::Liveness => {
            let v = examination_non_property::liveness_verdict(net, config);
            Ok(vec![ExaminationRecord {
                formula_id: format!("{model_name}-Liveness"),
                value: ExaminationValue::Verdict(v),
            }])
        }
        Examination::StateSpace => {
            let stats = examination_non_property::state_space_stats(net, config);
            Ok(vec![ExaminationRecord {
                formula_id: format!("{model_name}-StateSpace"),
                value: ExaminationValue::StateSpace(stats.map(|s| StateSpaceReport {
                    states: s.states,
                    edges: s.edges,
                    max_token_in_place: s.max_token_in_place,
                    max_token_sum: s.max_token_sum,
                })),
            }])
        }

        // -- Property examinations (one record per property) --
        Examination::UpperBounds => {
            let properties = crate::property_xml::parse_properties(model_dir, "UpperBounds")?;
            let results =
                crate::examinations::upper_bounds::check_upper_bounds_properties_with_aliases(
                    net,
                    &properties,
                    aliases,
                    config,
                );
            Ok(results
                .into_iter()
                .map(|(id, bound)| ExaminationRecord {
                    formula_id: id,
                    value: ExaminationValue::OptionalBound(bound),
                })
                .collect())
        }
        Examination::ReachabilityCardinality | Examination::ReachabilityFireability => {
            let exam_name = examination.as_str();
            let properties = crate::property_xml::parse_properties(model_dir, exam_name)?;
            let results = if flush {
                crate::examinations::reachability::check_reachability_properties_with_flush(
                    net,
                    &properties,
                    aliases,
                    config,
                )
            } else {
                crate::examinations::reachability::check_reachability_properties_with_aliases(
                    net,
                    &properties,
                    aliases,
                    config,
                )
            };
            Ok(results
                .into_iter()
                .map(|(id, verdict)| ExaminationRecord {
                    formula_id: id,
                    value: ExaminationValue::Verdict(verdict),
                })
                .collect())
        }
        Examination::CTLCardinality | Examination::CTLFireability => {
            let exam_name = examination.as_str();
            let properties = crate::property_xml::parse_properties(model_dir, exam_name)?;
            let results = if flush {
                crate::examinations::ctl::check_ctl_properties_with_flush(
                    net,
                    &properties,
                    aliases,
                    config,
                )
            } else {
                crate::examinations::ctl::check_ctl_properties_with_aliases(
                    net,
                    &properties,
                    aliases,
                    config,
                )
            };
            Ok(results
                .into_iter()
                .map(|(id, verdict)| ExaminationRecord {
                    formula_id: id,
                    value: ExaminationValue::Verdict(verdict),
                })
                .collect())
        }
        Examination::LTLCardinality | Examination::LTLFireability => {
            let exam_name = examination.as_str();
            let properties = crate::property_xml::parse_properties(model_dir, exam_name)?;
            let results = if flush {
                crate::examinations::ltl::check_ltl_properties_with_flush(
                    net,
                    &properties,
                    aliases,
                    config,
                )
            } else {
                crate::examinations::ltl::check_ltl_properties_with_aliases(
                    net,
                    &properties,
                    aliases,
                    config,
                )
            };
            Ok(results
                .into_iter()
                .map(|(id, verdict)| ExaminationRecord {
                    formula_id: id,
                    value: ExaminationValue::Verdict(verdict),
                })
                .collect())
        }
    }
}

// ---------------------------------------------------------------------------
// Compatibility helpers (existing public API)
// ---------------------------------------------------------------------------

/// Check UpperBounds properties and return `(property_id, optional_bound)` pairs.
///
/// Returns `Err` if the property XML cannot be parsed, or `Ok(results)` with
/// one entry per property. Each entry is `(id, Some(bound))` for resolved
/// properties or `(id, None)` for unresolved ones.
pub fn check_upper_bounds(
    net: &PetriNet,
    model_dir: &Path,
    config: &ExplorationConfig,
) -> Result<Vec<(String, Option<u64>)>, PnmlError> {
    let records =
        collect_examination_with_dir(net, "", model_dir, Examination::UpperBounds, config)?;
    Ok(records
        .into_iter()
        .map(|r| {
            let bound = match r.value {
                ExaminationValue::OptionalBound(b) => b,
                _ => None,
            };
            (r.formula_id, bound)
        })
        .collect())
}

/// Check reachability properties and return `(property_id, verdict_string)` pairs.
///
/// The `examination` parameter selects which reachability variant to check
/// (e.g., `ReachabilityCardinality` or `ReachabilityFireability`).
/// Verdict strings are `"TRUE"`, `"FALSE"`, or `"CANNOT_COMPUTE"`.
pub fn check_reachability(
    net: &PetriNet,
    model_dir: &Path,
    examination: Examination,
    config: &ExplorationConfig,
) -> Result<Vec<(String, String)>, PnmlError> {
    let records = collect_examination_with_dir(net, "", model_dir, examination, config)?;
    Ok(records
        .into_iter()
        .map(|r| {
            let verdict_str = match r.value {
                ExaminationValue::Verdict(v) => v.to_string(),
                _ => "CANNOT_COMPUTE".to_string(),
            };
            (r.formula_id, verdict_str)
        })
        .collect())
}

// ---------------------------------------------------------------------------
// Print wrappers (existing public API)
// ---------------------------------------------------------------------------

/// Run an examination on a Petri net and print MCC-format output to stdout.
///
/// For property-based examinations (UpperBounds), use
/// [`run_examination_with_dir`] instead. This function prints
/// `CANNOT_COMPUTE` for examinations that require model-directory property XML.
pub fn run_examination(
    net: &PetriNet,
    model_name: &str,
    examination: Examination,
    config: &ExplorationConfig,
) {
    if examination.needs_property_xml() {
        let exam_name = examination.as_str();
        eprintln!("{exam_name} requires model directory; use --examination with model dir");
        println!(
            "{}",
            crate::output::cannot_compute_line(model_name, exam_name)
        );
        return;
    }
    // Non-property examinations: collect and print.
    // `model_dir` is unused for non-property examinations — use a dummy path.
    let dummy = Path::new(".");
    match collect_examination_with_dir(net, model_name, dummy, examination, config) {
        Ok(records) => {
            for record in &records {
                println!("{}", record.to_mcc_line());
            }
        }
        Err(error) => {
            eprintln!("{}: CANNOT_COMPUTE ({error})", examination.as_str());
            println!(
                "{}",
                crate::output::cannot_compute_line(model_name, examination.as_str())
            );
        }
    }
}

/// Run an examination with access to the model directory.
///
/// Required for property-based examinations that read `<Examination>.xml`.
pub fn run_examination_with_dir(
    net: &PetriNet,
    model_name: &str,
    model_dir: &Path,
    examination: Examination,
    config: &ExplorationConfig,
) {
    let aliases = PropertyAliases::identity(net);
    match collect_examination_core(
        net,
        model_name,
        model_dir,
        &aliases,
        examination,
        config,
        true,
    ) {
        Ok(records) => {
            for record in &records {
                println!("{}", record.to_mcc_line());
            }
        }
        Err(error) => {
            let exam_name = examination.as_str();
            eprintln!("Warning: failed to parse {exam_name}.xml: {error}");
            println!(
                "{}",
                crate::output::cannot_compute_line(model_name, exam_name)
            );
        }
    }
}

#[cfg(test)]
#[path = "examination_tests.rs"]
mod tests;
