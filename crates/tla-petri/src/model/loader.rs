// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::Path;

use crate::error::PnmlError;

use super::diagnostics::ColoredLoadDiagnostics;
use super::{PreparedModel, PropertyAliases, SourceNetKind};

pub(super) fn load_model_dir(path: impl AsRef<Path>) -> Result<PreparedModel, PnmlError> {
    let dir = path.as_ref();
    let model_name = model_name_from_dir(dir);

    match crate::parser::parse_pnml_dir(dir) {
        Ok(net) => Ok(build_pt_model(dir, model_name, net)),
        Err(PnmlError::UnsupportedNetType { .. }) => build_colored_model(dir, model_name),
        Err(error) => Err(error),
    }
}

#[cfg(test)]
pub(crate) fn load_model_dir_no_colored_reduce(
    path: impl AsRef<Path>,
) -> Result<PreparedModel, PnmlError> {
    let dir = path.as_ref();
    let model_name = model_name_from_dir(dir);
    let colored = crate::hlpnml::parse_hlpnml_dir(dir)?;
    let colored_snapshot = colored.clone();
    let unfolded = crate::unfold::unfold_to_pt(&colored)?;
    Ok(PreparedModel::new(
        model_name,
        dir.to_path_buf(),
        SourceNetKind::SymmetricNet,
        unfolded.net,
        unfolded.aliases,
        Some(colored_snapshot),
        None,
    ))
}

fn model_name_from_dir(dir: &Path) -> String {
    dir.file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("unknown")
        .to_string()
}

fn build_pt_model(
    dir: &Path,
    model_name: String,
    net: crate::petri_net::PetriNet,
) -> PreparedModel {
    PreparedModel::new(
        model_name,
        dir.to_path_buf(),
        SourceNetKind::Pt,
        net.clone(),
        PropertyAliases::identity(&net),
        None,
        None,
    )
}

fn build_colored_model(dir: &Path, model_name: String) -> Result<PreparedModel, PnmlError> {
    let mut colored = crate::hlpnml::parse_hlpnml_dir(dir)?;
    let col_report = crate::colored_reduce::reduce_colored(&mut colored);
    let dead_report = crate::colored_dead_transitions::reduce(&mut colored);
    let colored_load_diagnostics = ColoredLoadDiagnostics::new(
        col_report.collapsed_places.len(),
        col_report.places_saved(),
        dead_report.transitions_removed,
    );
    let colored_snapshot = colored.clone();
    let unfolded = crate::unfold::unfold_to_pt(&colored)?;
    Ok(PreparedModel::new(
        model_name,
        dir.to_path_buf(),
        SourceNetKind::SymmetricNet,
        unfolded.net,
        unfolded.aliases,
        Some(colored_snapshot),
        Some(colored_load_diagnostics),
    ))
}
