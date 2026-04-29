// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Supported MCC examination kinds and string conversions.

use crate::error::PnmlError;
use crate::reduction::ReductionMode;

/// Supported MCC examinations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Examination {
    ReachabilityDeadlock,
    ReachabilityCardinality,
    ReachabilityFireability,
    CTLCardinality,
    CTLFireability,
    LTLCardinality,
    LTLFireability,
    StateSpace,
    OneSafe,
    QuasiLiveness,
    StableMarking,
    UpperBounds,
    Liveness,
}

impl Examination {
    /// All 13 MCC examination kinds, in canonical order.
    pub const ALL: [Examination; 13] = [
        Self::ReachabilityDeadlock,
        Self::ReachabilityCardinality,
        Self::ReachabilityFireability,
        Self::CTLCardinality,
        Self::CTLFireability,
        Self::LTLCardinality,
        Self::LTLFireability,
        Self::StateSpace,
        Self::UpperBounds,
        Self::OneSafe,
        Self::QuasiLiveness,
        Self::StableMarking,
        Self::Liveness,
    ];

    /// Parse an examination name (as used by MCC).
    pub fn from_name(name: &str) -> Result<Self, PnmlError> {
        match name {
            "ReachabilityDeadlock" => Ok(Self::ReachabilityDeadlock),
            "ReachabilityCardinality" => Ok(Self::ReachabilityCardinality),
            "ReachabilityFireability" => Ok(Self::ReachabilityFireability),
            "CTLCardinality" => Ok(Self::CTLCardinality),
            "CTLFireability" => Ok(Self::CTLFireability),
            "LTLCardinality" => Ok(Self::LTLCardinality),
            "LTLFireability" => Ok(Self::LTLFireability),
            "StateSpace" => Ok(Self::StateSpace),
            "OneSafe" => Ok(Self::OneSafe),
            "QuasiLiveness" => Ok(Self::QuasiLiveness),
            "StableMarking" => Ok(Self::StableMarking),
            "UpperBounds" => Ok(Self::UpperBounds),
            "Liveness" => Ok(Self::Liveness),
            _ => Err(PnmlError::UnknownExamination(name.into())),
        }
    }

    /// Returns the MCC examination name string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ReachabilityDeadlock => "ReachabilityDeadlock",
            Self::ReachabilityCardinality => "ReachabilityCardinality",
            Self::ReachabilityFireability => "ReachabilityFireability",
            Self::CTLCardinality => "CTLCardinality",
            Self::CTLFireability => "CTLFireability",
            Self::LTLCardinality => "LTLCardinality",
            Self::LTLFireability => "LTLFireability",
            Self::StateSpace => "StateSpace",
            Self::OneSafe => "OneSafe",
            Self::QuasiLiveness => "QuasiLiveness",
            Self::StableMarking => "StableMarking",
            Self::UpperBounds => "UpperBounds",
            Self::Liveness => "Liveness",
        }
    }

    /// Returns true if this examination requires property XML files from
    /// the model directory (e.g., UpperBounds.xml, ReachabilityCardinality.xml).
    #[must_use]
    pub fn needs_property_xml(self) -> bool {
        self.property_xml_name().is_ok()
    }

    /// Returns the MCC property XML stem for property examinations,
    /// or an error for non-property examinations (e.g., StateSpace, OneSafe).
    pub fn property_xml_name(self) -> Result<&'static str, PnmlError> {
        match self {
            Self::UpperBounds => Ok("UpperBounds"),
            Self::ReachabilityCardinality => Ok("ReachabilityCardinality"),
            Self::ReachabilityFireability => Ok("ReachabilityFireability"),
            Self::CTLCardinality => Ok("CTLCardinality"),
            Self::CTLFireability => Ok("CTLFireability"),
            Self::LTLCardinality => Ok("LTLCardinality"),
            Self::LTLFireability => Ok("LTLFireability"),
            _ => Err(PnmlError::ExaminationDoesNotUsePropertyXml {
                examination: self.as_str().to_string(),
            }),
        }
    }

    /// Returns the query-aware structural reduction mode for this examination.
    ///
    /// Different temporal logics tolerate different structural reduction rules.
    /// This follows Tapaal's approach: reachability allows all rules, CTL/LTL
    /// progressively restrict which rules are applied.
    ///
    /// # Reduction safety by examination type
    ///
    /// - **Reachability** examinations: all rules safe (only markings matter)
    /// - **CTL** examinations: next-free CTL rules (no agglomeration)
    /// - **LTL** examinations: stutter-insensitive rules (LTL without X)
    /// - **Non-property** examinations (StateSpace, OneSafe, etc.): reachability
    ///   mode since they examine the full state space or structural properties
    #[must_use]
    pub(crate) fn reduction_mode(self) -> ReductionMode {
        match self {
            // Reachability examinations: all reductions are sound.
            Self::ReachabilityDeadlock
            | Self::ReachabilityCardinality
            | Self::ReachabilityFireability => ReductionMode::Reachability,

            // CTL examinations: formulas may contain EX/AX. Use next-free CTL
            // as the conservative default — callers that detect absence of
            // next-step operators can upgrade to the more permissive mode.
            Self::CTLCardinality | Self::CTLFireability => ReductionMode::NextFreeCTL,

            // LTL examinations: assume stutter-insensitive (no X operator).
            // Callers that detect X in the formula should downgrade to
            // StutterSensitiveLTL.
            Self::LTLCardinality | Self::LTLFireability => ReductionMode::StutterInsensitiveLTL,

            // Non-property examinations: state space / structural analysis.
            // UpperBounds needs exact markings (reachability-equivalent).
            // OneSafe has its own dedicated semantics lane.
            // QuasiLiveness/StableMarking/Liveness examine global properties.
            Self::StateSpace
            | Self::OneSafe
            | Self::QuasiLiveness
            | Self::StableMarking
            | Self::UpperBounds
            | Self::Liveness => ReductionMode::Reachability,
        }
    }
}
