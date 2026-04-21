// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::features::StaticFeatures;

use super::LogicCategory;

impl LogicCategory {
    /// Upgrade a logic category to its DT-combined variant when datatypes
    /// are declared but the user specified a non-DT logic (#3223).
    pub(crate) fn with_datatypes(self) -> Self {
        match self {
            // Already DT variants
            Self::QfDt
            | Self::DtAuflia
            | Self::DtAuflra
            | Self::DtAuflira
            | Self::DtUfbv
            | Self::DtAufbv
            | Self::DtAx
            | Self::Ufdt
            | Self::Ufdtlia
            | Self::Ufdtlra
            | Self::Ufdtlira
            | Self::Ufdtnia
            | Self::Ufdtnra
            | Self::Ufdtnira
            | Self::Aufdt
            | Self::Aufdtlia
            | Self::Aufdtlira => self,
            // LIA -> DT+AUFLIA
            Self::QfLia
            | Self::QfUflia
            | Self::QfAuflia
            | Self::Lia
            | Self::Uflia
            | Self::Auflia => Self::DtAuflia,
            // LRA -> DT+AUFLRA
            Self::QfLra
            | Self::QfUflra
            | Self::QfAuflra
            | Self::Lra
            | Self::Uflra
            | Self::Auflra => Self::DtAuflra,
            // LIRA -> DT+AUFLIRA (#5402, #5888)
            Self::QfLira | Self::QfAuflira | Self::Lira | Self::Nira | Self::Auflira => {
                Self::DtAuflira
            }
            // UF / propositional -> QF_DT
            Self::QfUf | Self::Uf | Self::Propositional => Self::QfDt,
            // BV -> DT+UFBV (DT needs UF for selectors/constructors)
            Self::QfBv | Self::QfUfbv => Self::DtUfbv,
            // ABV/AUFBV -> DT+AUFBV
            Self::QfAbv | Self::QfAufbv => Self::DtAufbv,
            // Arrays -> DT+AX
            Self::QfAx => Self::DtAx,
            // BV+LIA (conversion functions) -> unsupported (#5503)
            Self::QfBvLia => Self::Other,
            // BV+LIA (independent) -> DT+AUFLIA (BV as UF, #5356)
            Self::QfBvLiaIndep => Self::DtAuflia,
            // FP + DT: not supported yet
            Self::QfFp | Self::QfBvfp => Self::Other,
            // Fallthrough: DT + unsupported theory combinations (NIA, NRA, strings)
            // must NOT silently solve without DT axioms — return Other to produce
            // an unsupported-logic error rather than unsound results (#5430).
            _ => Self::Other,
        }
    }

    /// Narrow a combined UF/array arithmetic logic to its pure arithmetic
    /// equivalent when the live assertion footprint has no UF or array terms (#6300).
    ///
    /// The declared `set-logic` is an upper bound. When the live formula uses a
    /// strict subset of theories, dispatching through the combined solver adds
    /// unnecessary overhead and can lose completeness (e.g., the AUFLIA split-loop
    /// returns unknown for a pure integer-gap constraint that the LIA solver handles).
    ///
    /// Must be called **after** `with_datatypes()` and **before** `with_nonlinear()`
    /// so that DT-bearing formulas keep their combined path and nonlinear promotion
    /// sees the narrowed category.
    pub(crate) fn narrow_linear_combo_with_features(self, features: &StaticFeatures) -> Self {
        // Only narrow when the live footprint has no UF and no array terms.
        if features.has_uf || features.has_arrays {
            return self;
        }
        match self {
            // QF UF/AUF + Int -> QF_LIA
            Self::QfUflia | Self::QfAuflia if features.has_int && !features.has_real => Self::QfLia,
            // Quantified UF/AUF + Int -> LIA
            Self::Uflia | Self::Auflia if features.has_int && !features.has_real => Self::Lia,

            // QF UF/AUF + Real -> QF_LRA
            Self::QfUflra | Self::QfAuflra if features.has_real && !features.has_int => Self::QfLra,
            // Quantified UF/AUF + Real -> LRA
            Self::Uflra | Self::Auflra if features.has_real && !features.has_int => Self::Lra,

            // QF AUF + mixed Int/Real -> QF_LIRA
            Self::QfAuflira if features.has_int && features.has_real => Self::QfLira,
            // Quantified AUF + mixed Int/Real -> LIRA
            Self::Auflira if features.has_int && features.has_real => Self::Lira,

            // Everything else — no narrowing
            _ => self,
        }
    }

    /// Widen a pure arithmetic logic to its UF-combined equivalent when the
    /// live assertion footprint contains uninterpreted function applications
    /// (#7442).
    ///
    /// Consumers may declare a narrow logic (e.g., `QF_LIA`) but then add
    /// UF terms via `declare-fun`. Without widening, the pure LIA solver
    /// cannot reason about UF equalities and returns `unknown`. This method
    /// upgrades to the UF-combined variant so the EUF solver handles UF terms.
    ///
    /// Must be called **after** `narrow_linear_combo_with_features()` and
    /// **before** `with_nonlinear()` so that narrowed categories get widened
    /// back when UF is present, and nonlinear promotion sees the correct base.
    pub(crate) fn widen_with_uf(self, features: &StaticFeatures) -> Self {
        if !features.has_uf {
            return self;
        }
        match self {
            // Already has UF — no widening needed
            Self::QfUf
            | Self::QfUflia
            | Self::QfUflra
            | Self::QfAuflia
            | Self::QfAuflra
            | Self::QfAuflira
            | Self::QfUfbv
            | Self::QfAufbv
            | Self::QfUfnia
            | Self::QfUfnra
            | Self::QfUfnira
            | Self::Uf
            | Self::Uflia
            | Self::Uflra
            | Self::Auflia
            | Self::Auflra
            | Self::Auflira
            | Self::Ufnia
            | Self::Ufnra
            | Self::Ufnira
            // Quantified DT logics already have UF (#7150)
            | Self::Ufdt
            | Self::Ufdtlia
            | Self::Ufdtlra
            | Self::Ufdtlira
            | Self::Ufdtnia
            | Self::Ufdtnra
            | Self::Ufdtnira
            | Self::Aufdt
            | Self::Aufdtlia
            | Self::Aufdtlira => self,

            // QF pure Int -> QF UF + Int
            Self::QfLia => Self::QfUflia,
            // QF pure Real -> QF UF + Real
            Self::QfLra => Self::QfUflra,
            // QF mixed Int+Real -> QF AUF + Int + Real (AUFLIA subsumes UFLIRA)
            Self::QfLira => Self::QfAuflira,
            // QF arrays -> QF arrays + UF
            Self::QfAx => Self::QfAuflia,

            // QF nonlinear -> QF UF + nonlinear
            Self::QfNia => Self::QfUfnia,
            Self::QfNra => Self::QfUfnra,
            Self::QfNira => Self::QfUfnira,

            // QF BV -> QF UF + BV
            Self::QfBv => Self::QfUfbv,
            Self::QfAbv => Self::QfAufbv,

            // Quantified pure Int -> quantified UF + Int
            Self::Lia => Self::Uflia,
            // Quantified pure Real -> quantified UF + Real
            Self::Lra => Self::Uflra,
            // Quantified mixed -> quantified AUF + mixed
            Self::Lira => Self::Auflira,
            // Quantified nonlinear -> quantified UF + nonlinear
            Self::Nia => Self::Ufnia,
            Self::Nra => Self::Ufnra,
            Self::Nira => Self::Ufnira,

            // Everything else — no widening (DT, strings, seq, BV+LIA, etc.)
            _ => self,
        }
    }

    /// Upgrade a linear logic to its nonlinear equivalent when the formula
    /// contains nonlinear terms despite the declared logic being linear (#6086).
    ///
    /// Called once before the dispatch match to prevent false SAT from linear
    /// solvers receiving nonlinear formulas. Mirrors `with_datatypes()`.
    pub(crate) fn with_nonlinear(self, features: &StaticFeatures) -> Self {
        let nl_int = features.has_nonlinear_int;
        let nl_real = features.has_nonlinear_real;
        if !nl_int && !nl_real {
            return self;
        }
        match self {
            // Already nonlinear — no upgrade needed
            Self::QfNia
            | Self::QfNra
            | Self::QfNira
            | Self::QfUfnia
            | Self::QfUfnra
            | Self::QfUfnira
            | Self::QfSnia
            | Self::Nia
            | Self::Nra
            | Self::Nira
            | Self::Ufnia
            | Self::Ufnra
            | Self::Ufnira
            // Quantified DT nonlinear variants (#7150)
            | Self::Ufdtnia
            | Self::Ufdtnra
            | Self::Ufdtnira => self,

            // QF linear Int -> QF nonlinear Int
            Self::QfLia if nl_int => Self::QfNia,
            // QF linear Real -> QF nonlinear Real
            Self::QfLra if nl_real => Self::QfNra,
            // QF mixed Int+Real -> QF nonlinear mixed
            Self::QfLira if nl_int || nl_real => Self::QfNira,

            // QF UF + linear -> QF UF + nonlinear
            Self::QfUflia if nl_int => Self::QfUfnia,
            Self::QfUflra if nl_real => Self::QfUfnra,

            // QF AUF + linear -> QF UF + nonlinear (arrays handled via UF)
            Self::QfAuflia if nl_int => Self::QfUfnia,
            Self::QfAuflra if nl_real => Self::QfUfnra,
            Self::QfAuflira if nl_int || nl_real => Self::QfUfnira,

            // DT + nonlinear -> Other (no combined DT+NIA/NRA solver; #6088).
            // with_datatypes() runs first. If we still see a DT variant with
            // nonlinear terms, routing to QfNia/QfNra would drop DT axioms.
            Self::DtAuflia if nl_int => Self::Other,
            Self::DtAuflra if nl_real => Self::Other,
            Self::DtAuflira if nl_int || nl_real => Self::Other,

            // Quantified DT + linear -> quantified DT + nonlinear (#7150)
            Self::Ufdtlia if nl_int => Self::Ufdtnia,
            Self::Ufdtlra if nl_real => Self::Ufdtnra,
            Self::Ufdtlira if nl_int || nl_real => Self::Ufdtnira,
            Self::Aufdtlia if nl_int => Self::Ufdtnia,
            Self::Aufdtlira if nl_int || nl_real => Self::Ufdtnira,

            // Quantified linear -> quantified nonlinear
            Self::Lia if nl_int => Self::Nia,
            Self::Lra if nl_real => Self::Nra,
            Self::Lira if nl_int || nl_real => Self::Nira,

            // Quantified UF/AUF + linear -> quantified UF + nonlinear
            Self::Uflia if nl_int => Self::Ufnia,
            Self::Uflra if nl_real => Self::Ufnra,
            Self::Auflia if nl_int => Self::Ufnia,
            Self::Auflra if nl_real => Self::Ufnra,
            Self::Auflira if nl_int || nl_real => Self::Ufnira,

            // Strings + linear Int -> Strings + nonlinear Int
            Self::QfSlia if nl_int => Self::QfSnia,

            // Seq + nonlinear Int: no combined Seq+NIA solver -> Other.
            Self::QfSeqlia if nl_int => Self::Other,

            // BV + nonlinear Int: no combined BV+NIA solver -> Other (#6088).
            Self::QfBvLia if nl_int => Self::Other,
            Self::QfBvLiaIndep if nl_int => Self::Other,

            // Non-arithmetic logics — no upgrade needed
            _ => self,
        }
    }
}
