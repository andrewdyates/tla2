// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::LogicCategory;

impl LogicCategory {
    /// Parse a logic string from set-logic command into a LogicCategory.
    pub(crate) fn from_logic(logic: &str) -> Self {
        match logic {
            // Pure propositional
            "QF_UF" => Self::QfUf,
            // SMT-LIB "ALL": accept and fall back to default solver selection (QF_UF).
            "ALL" => Self::QfUf,
            "QF_BOOL" | "BOOL" => Self::Propositional,
            // Arrays
            "QF_AX" => Self::QfAx,
            // Linear real arithmetic logics
            "QF_LRA" | "QF_RDL" => Self::QfLra,
            // Linear integer arithmetic logics
            "QF_LIA" | "QF_IDL" => Self::QfLia,
            // Non-linear arithmetic logics
            "QF_NIA" => Self::QfNia,
            "QF_NRA" => Self::QfNra,
            "QF_NIRA" => Self::QfNira,
            // Combined UF + LIA (very common in verification; also accepts QF_UFIDL)
            "QF_UFLIA" | "QF_UFIDL" => Self::QfUflia,
            // Combined UF + LRA
            "QF_UFLRA" => Self::QfUflra,
            // Combined Arrays + UF + LIA (very common in software verification)
            // QF_ALIA is a common alias (Arrays + LIA, UF implied)
            "QF_AUFLIA" | "QF_ALIA" => Self::QfAuflia,
            // Combined Arrays + UF + LRA
            "QF_AUFLRA" => Self::QfAuflra,
            // Mixed integer and real arithmetic
            "QF_LIRA" => Self::QfLira,
            // Combined Arrays + UF + mixed int/real arithmetic
            "QF_AUFLIRA" => Self::QfAuflira,
            // Bitvectors
            "QF_BV" => Self::QfBv,
            // Arrays + Bitvectors (important for Kani workloads)
            "QF_ABV" => Self::QfAbv,
            // UF + Bitvectors
            "QF_UFBV" => Self::QfUfbv,
            // Arrays + UF + Bitvectors (critical for Kani workloads)
            "QF_AUFBV" => Self::QfAufbv,
            // BV + integer arithmetic (internal, from infer_logic #5503)
            "_BV_LIA" => Self::QfBvLia,
            // BV + Int without conversion functions (internal, from infer_logic #5356)
            "_BV_LIA_INDEP" => Self::QfBvLiaIndep,
            // Floating-point
            "QF_FP" => Self::QfFp,
            "QF_BVFP" => Self::QfBvfp,
            // Strings
            "QF_S" => Self::QfS,
            "QF_SLIA" => Self::QfSlia,
            "QF_SNIA" => Self::QfSnia,
            // Generic sequences
            "QF_SEQ" => Self::QfSeq,
            "QF_SEQBV" => Self::QfSeqBv,
            "QF_SEQLIA" => Self::QfSeqlia,
            // Datatypes
            "QF_DT" => Self::QfDt,
            // Internal: Combined DT + arithmetic (used by ALL logic auto-detection)
            "_DT_AUFLIA" => Self::DtAuflia,
            "_DT_AUFLRA" => Self::DtAuflra,
            "_DT_UFBV" => Self::DtUfbv,
            "_DT_AUFBV" => Self::DtAufbv,
            "_DT_AUFLIRA" => Self::DtAuflira,
            "_DT_AX" => Self::DtAx,
            // QF non-linear + UF/Arrays: preserve UF information (#5984).
            // Without EUF congruence closure, NIA/NRA solvers can assign
            // inconsistent values to UF function applications (e.g., (f x)=1
            // and (f y)=2 when x=y), producing unsound SAT results.
            "QF_UFNIA" | "QF_AUFNIA" => Self::QfUfnia,
            "QF_UFNRA" | "QF_AUFNRA" => Self::QfUfnra,
            "QF_UFNIRA" | "QF_AUFNIRA" => Self::QfUfnira,
            // QF FP + LRA: route to FP solver (LRA constraints handled via combined path)
            "QF_FPLRA" => Self::QfFp,
            // Quantified logics (use E-matching + CEGQI)
            "LIA" => Self::Lia,
            "LRA" => Self::Lra,
            "NIA" => Self::Nia,
            "NRA" => Self::Nra,
            "UF" => Self::Uf,
            "UFLIA" => Self::Uflia,
            "UFLRA" => Self::Uflra,
            "AUFLIA" => Self::Auflia,
            "AUFLRA" => Self::Auflra,
            "LIRA" => Self::Lira,
            "NIRA" => Self::Nira,
            "AUFLIRA" => Self::Auflira,
            // Quantified NIA/NRA/NIRA + UF/Arrays: preserve UF information (#5984).
            // Returns Unknown (quantified non-linear not yet implemented) but the
            // logic is recognized rather than returning UnsupportedLogic error.
            "UFNIA" | "AUFNIA" => Self::Ufnia,
            "UFNRA" | "AUFNRA" => Self::Ufnra,
            "UFNIRA" | "AUFNIRA" => Self::Ufnira,
            // Quantified arrays + linear arithmetic
            "ALIA" => Self::Auflia,
            "ALRA" => Self::Auflra,
            "ALIRA" => Self::Auflira,
            // Quantified bitvectors: route to QF solver (finite domain expansion)
            "BV" => Self::QfBv,
            "ABV" => Self::QfAbv,
            "UFBV" => Self::QfUfbv,
            "AUFBV" => Self::QfAufbv,
            // Quantified datatype logics (#7150: ~9 SMT-COMP tracks)
            // Quantifier preprocessing strips quantifiers before theory dispatch,
            // so these route to the same DT-combined solvers as QF_ variants.
            "UFDT" | "DT" => Self::Ufdt,
            "UFDTLIA" | "DTLIA" => Self::Ufdtlia,
            "UFDTLRA" | "DTLRA" => Self::Ufdtlra,
            "UFDTLIRA" | "DTLIRA" => Self::Ufdtlira,
            "UFDTNIA" => Self::Ufdtnia,
            "UFDTNRA" => Self::Ufdtnra,
            "UFDTNIRA" => Self::Ufdtnira,
            "AUFDT" | "ADT" => Self::Aufdt,
            "AUFDTLIA" => Self::Aufdtlia,
            "AUFDTLIRA" => Self::Aufdtlira,
            // A-prefix non-linear DT: route to UF+DT+NL (arrays handled via UF)
            "AUFDTNIA" => Self::Ufdtnia,
            "AUFDTNRA" => Self::Ufdtnra,
            "AUFDTNIRA" => Self::Ufdtnira,
            "AUFDTLRA" => Self::Ufdtlra,
            // QF_ variants of DT logics: route to existing QF_DT / DtAuf* categories
            "QF_UFDT" => Self::QfDt,
            "QF_UFDTLIA" | "QF_DTLIA" => Self::DtAuflia,
            "QF_UFDTLRA" | "QF_DTLRA" => Self::DtAuflra,
            "QF_UFDTLIRA" | "QF_DTLIRA" => Self::DtAuflira,
            // Default to unsupported for unknown logics
            _ => Self::Other,
        }
    }
}
