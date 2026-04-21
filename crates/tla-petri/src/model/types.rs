// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::{Path, PathBuf};

use crate::hlpnml::ColoredNet;
use crate::petri_net::PetriNet;

use super::aliases::PropertyAliases;
use super::diagnostics::ColoredLoadDiagnostics;

/// The kind of source net that was loaded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SourceNetKind {
    /// Standard Place/Transition net (`ptnet` type attribute).
    Pt,
    /// Colored symmetric net (`symmetricnet` type attribute).
    SymmetricNet,
}

/// A model directory fully prepared for MCC examination execution.
///
/// Wraps a [`PetriNet`] with the model name, directory path, source
/// net kind, and property alias tables. Created by [`super::load_model_dir`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PreparedModel {
    model_name: String,
    model_dir: PathBuf,
    source_kind: SourceNetKind,
    net: PetriNet,
    pub(crate) aliases: PropertyAliases,
    pub(crate) colored_source: Option<ColoredNet>,
    colored_load_diagnostics: Option<ColoredLoadDiagnostics>,
}

impl PreparedModel {
    pub(super) fn new(
        model_name: String,
        model_dir: PathBuf,
        source_kind: SourceNetKind,
        net: PetriNet,
        aliases: PropertyAliases,
        colored_source: Option<ColoredNet>,
        colored_load_diagnostics: Option<ColoredLoadDiagnostics>,
    ) -> Self {
        Self {
            model_name,
            model_dir,
            source_kind,
            net,
            aliases,
            colored_source,
            colored_load_diagnostics,
        }
    }

    /// The model name (derived from the directory name).
    #[must_use]
    pub fn model_name(&self) -> &str {
        &self.model_name
    }

    /// The model directory path.
    #[must_use]
    pub fn model_dir(&self) -> &Path {
        &self.model_dir
    }

    /// The kind of source net that was loaded.
    #[must_use]
    pub fn source_kind(&self) -> SourceNetKind {
        self.source_kind
    }

    /// The executable P/T net (after unfolding for colored nets).
    #[must_use]
    pub fn net(&self) -> &PetriNet {
        &self.net
    }

    #[must_use]
    pub(crate) fn aliases(&self) -> &PropertyAliases {
        &self.aliases
    }

    #[must_use]
    pub(super) fn colored_load_diagnostics(&self) -> Option<&ColoredLoadDiagnostics> {
        self.colored_load_diagnostics.as_ref()
    }
}
