// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;
use crate::petri_net::PetriNet;
use crate::simplification_report::SimplificationReport;

use super::diagnostics::{ColoredExecutionDiagnostics, ColoredPropertyDiagnostic};
use super::{PreparedModel, PropertyAliases, SourceNetKind};

pub(super) fn collect_examination_for_model(
    model: &PreparedModel,
    examination: crate::examination::Examination,
    config: &crate::explorer::ExplorationConfig,
) -> Result<Vec<crate::examination::ExaminationRecord>, PnmlError> {
    let (records, _) = collect_examination_for_model_inner(model, examination, config, false)?;
    Ok(records)
}

pub(super) fn collect_examination_for_model_inner(
    model: &PreparedModel,
    examination: crate::examination::Examination,
    config: &crate::explorer::ExplorationConfig,
    flush: bool,
) -> Result<
    (
        Vec<crate::examination::ExaminationRecord>,
        ColoredExecutionDiagnostics,
    ),
    PnmlError,
> {
    if model.source_kind() == SourceNetKind::SymmetricNet
        && matches!(examination, crate::examination::Examination::StateSpace)
    {
        // MCC StateSpace must report exact counts. The current colored-model
        // lane unfolds through an unsound skeleton for some families
        // (for example BridgeAndVehicles-COL), so publishing numeric counts
        // is worse than failing closed.
        return Ok((
            vec![crate::examination::ExaminationRecord::new(
                format!("{}-StateSpace", model.model_name()),
                crate::examination::ExaminationValue::StateSpace(None),
            )],
            ColoredExecutionDiagnostics::default(),
        ));
    }

    if model.source_kind() == SourceNetKind::SymmetricNet
        && matches!(examination, crate::examination::Examination::UpperBounds)
        && model.colored_source.is_some()
    {
        return collect_with_colored_relevance(model, examination, config);
    }

    let records = crate::examination::collect_examination_core(
        model.net(),
        model.model_name(),
        model.model_dir(),
        model.aliases(),
        examination,
        config,
        flush,
    )?;
    Ok((records, ColoredExecutionDiagnostics::default()))
}

pub(super) fn collect_simplification_report_for_model(
    model: &PreparedModel,
    examination: crate::examination::Examination,
) -> Result<SimplificationReport, PnmlError> {
    let xml_name = examination.property_xml_name()?;
    let properties = crate::property_xml::parse_properties(model.model_dir(), xml_name)?;
    let run = crate::formula_simplify::simplify_properties_with_report(
        model.net(),
        &properties,
        model.aliases(),
    );
    Ok(run.report)
}

fn collect_with_colored_relevance(
    model: &PreparedModel,
    examination: crate::examination::Examination,
    config: &crate::explorer::ExplorationConfig,
) -> Result<
    (
        Vec<crate::examination::ExaminationRecord>,
        ColoredExecutionDiagnostics,
    ),
    PnmlError,
> {
    let colored_source = model.colored_source.as_ref().expect("checked by caller");
    let exam_name = examination.as_str();
    let properties = crate::property_xml::parse_properties(model.model_dir(), exam_name)?;

    let mut records = Vec::with_capacity(properties.len());
    let mut diagnostics = ColoredExecutionDiagnostics::default();

    for property in &properties {
        let refs = crate::colored_relevance::extract_refs(&property.formula);
        let has_refs = !refs.places.is_empty() || !refs.transitions.is_empty();
        let mut diagnostic = ColoredPropertyDiagnostic::new(property.id.clone());

        let (net, aliases) = if has_refs {
            let mut reduced = colored_source.clone();
            let report = crate::colored_relevance::reduce(&mut reduced, &property.formula);
            if report.is_reduction() {
                diagnostic.set_reduction(report.places_removed, report.transitions_removed);
            }
            match crate::unfold::unfold_to_pt(&reduced) {
                Ok(unfolded) => (unfolded.net, unfolded.aliases),
                Err(error) => {
                    diagnostic.set_fallback_reason(error.to_string());
                    (model.net().clone(), model.aliases().clone())
                }
            }
        } else {
            (model.net().clone(), model.aliases().clone())
        };

        let one_property = std::slice::from_ref(property);
        let property_records =
            run_single_property_exam(&net, one_property, &aliases, config, examination);
        records.extend(property_records);
        diagnostics.push(diagnostic);
    }

    Ok((records, diagnostics))
}

fn run_single_property_exam(
    net: &PetriNet,
    properties: &[crate::property_xml::Property],
    aliases: &PropertyAliases,
    config: &crate::explorer::ExplorationConfig,
    examination: crate::examination::Examination,
) -> Vec<crate::examination::ExaminationRecord> {
    use crate::examination::{Examination, ExaminationRecord, ExaminationValue};

    match examination {
        Examination::UpperBounds => {
            crate::examinations::upper_bounds::check_upper_bounds_properties_with_aliases(
                net, properties, aliases, config,
            )
            .into_iter()
            .map(|(id, bound)| ExaminationRecord::new(id, ExaminationValue::OptionalBound(bound)))
            .collect()
        }
        Examination::ReachabilityCardinality | Examination::ReachabilityFireability => {
            crate::examinations::reachability::check_reachability_properties_with_aliases(
                net, properties, aliases, config,
            )
            .into_iter()
            .map(|(id, verdict)| ExaminationRecord::new(id, ExaminationValue::Verdict(verdict)))
            .collect()
        }
        Examination::CTLCardinality | Examination::CTLFireability => {
            crate::examinations::ctl::check_ctl_properties_with_aliases(
                net, properties, aliases, config,
            )
            .into_iter()
            .map(|(id, verdict)| ExaminationRecord::new(id, ExaminationValue::Verdict(verdict)))
            .collect()
        }
        Examination::LTLCardinality | Examination::LTLFireability => {
            crate::examinations::ltl::check_ltl_properties_with_aliases(
                net, properties, aliases, config,
            )
            .into_iter()
            .map(|(id, verdict)| ExaminationRecord::new(id, ExaminationValue::Verdict(verdict)))
            .collect()
        }
        _ => Vec::new(),
    }
}
