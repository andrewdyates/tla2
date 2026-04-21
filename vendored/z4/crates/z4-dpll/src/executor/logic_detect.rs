// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared logic-category detection for executor solve entry points.

use z4_core::TermId;

use super::Executor;
use crate::features::StaticFeatures;
use crate::logic_detection::LogicCategory;

impl Executor {
    pub(in crate::executor) fn detect_logic_category(
        &self,
        assertions: &[TermId],
    ) -> (LogicCategory, StaticFeatures) {
        let logic = match self.ctx.logic() {
            Some("ALL") | None => {
                let features = StaticFeatures::collect(&self.ctx.terms, assertions);
                let has_datatypes = self.ctx.datatype_iter().next().is_some();

                if has_datatypes {
                    if features.has_int || features.has_real {
                        if features.has_real {
                            "_DT_AUFLRA"
                        } else {
                            "_DT_AUFLIA"
                        }
                    } else if features.has_bv || features.has_arrays {
                        if features.has_bv && features.has_arrays {
                            "_DT_AUFBV"
                        } else if features.has_bv {
                            "_DT_UFBV"
                        } else {
                            "_DT_AX"
                        }
                    } else {
                        "QF_DT"
                    }
                } else {
                    features.infer_logic()
                }
            }
            Some(logic) => {
                if logic == "QF_S" || logic == "QF_SLIA" {
                    let features = StaticFeatures::collect(&self.ctx.terms, assertions);
                    if features.has_seq && features.has_int {
                        "QF_SEQLIA"
                    } else if features.has_seq {
                        "QF_SEQ"
                    } else if logic == "QF_S" && features.has_int {
                        "QF_SLIA"
                    } else {
                        logic
                    }
                } else {
                    logic
                }
            }
        };
        let mut category = LogicCategory::from_logic(logic);

        if self.ctx.datatype_iter().next().is_some() {
            category = category.with_datatypes();
        }

        let mut features = StaticFeatures::collect(&self.ctx.terms, assertions);
        // Extend features with declared symbols so narrowing respects all
        // theories the consumer has declared, not just those in assertions (#7442).
        features.extend_with_declarations(
            self.ctx
                .symbol_iter()
                .map(|(name, info)| (name.as_str(), info.arg_sorts.as_slice(), &info.sort)),
        );
        category = category.narrow_linear_combo_with_features(&features);
        // Widen pure arithmetic logics to UF-combined variants when UF terms
        // are present. Consumers may declare QF_LIA but add UF terms via
        // declare-fun; without widening, the LIA solver returns unknown (#7442).
        category = category.widen_with_uf(&features);
        category = category.with_nonlinear(&features);

        if !features.has_int
            && !features.has_real
            && !features.has_bv
            && !features.has_arrays
            && !features.has_uf
            && !features.has_strings
            && !features.has_seq
        {
            category = match category {
                LogicCategory::QfLia
                | LogicCategory::QfLra
                | LogicCategory::QfLira
                | LogicCategory::Lia
                | LogicCategory::Lra
                | LogicCategory::Lira => LogicCategory::Propositional,
                other => other,
            };
        }

        if features.has_seq
            && !matches!(
                category,
                LogicCategory::QfSeq
                    | LogicCategory::QfSeqBv
                    | LogicCategory::QfSeqlia
                    | LogicCategory::QfS
                    | LogicCategory::QfSlia
                    | LogicCategory::QfSnia
            )
        {
            category = if features.has_int {
                LogicCategory::QfSeqlia
            } else {
                LogicCategory::QfSeq
            };
        }

        (category, features)
    }
}
