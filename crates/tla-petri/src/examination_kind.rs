// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Supported MCC examination kinds and string conversions.

use crate::error::PnmlError;

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
}
