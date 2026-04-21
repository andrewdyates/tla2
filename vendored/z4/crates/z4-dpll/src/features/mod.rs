// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Static feature analysis for SMT formulas.
//!
//! This module provides automatic logic detection when `set-logic` is not specified.
//! It analyzes formula features (sorts, symbols, quantifiers) to infer the
//! appropriate logic for solving.
//!
//! Based on Z3's approach: `reference/z3/src/ast/static_features.cpp`

use std::collections::HashSet;
use z4_core::{
    term::{Symbol, TermData},
    Sort, TermId, TermStore,
};

/// Static features detected from a formula.
///
/// These features determine which theories are needed to solve the formula,
/// enabling automatic logic detection when `set-logic` is not specified.
#[derive(Default, Debug, Clone)]
pub(crate) struct StaticFeatures {
    /// Formula contains Int-sorted terms
    pub has_int: bool,
    /// Formula contains Real-sorted terms
    pub has_real: bool,
    /// Formula contains BitVec-sorted terms
    pub has_bv: bool,
    /// Formula contains Array-sorted terms
    pub has_arrays: bool,
    /// Formula contains String-sorted terms
    pub has_strings: bool,
    /// Formula contains generic Seq-sorted terms (not String)
    pub has_seq: bool,
    /// Formula contains RegLan-sorted terms or regex operators
    pub has_regex: bool,
    /// Formula contains FloatingPoint-sorted terms
    pub has_fpa: bool,
    /// Formula contains uninterpreted functions (arity > 0)
    pub has_uf: bool,
    /// Formula contains quantifiers (forall/exists)
    pub has_quantifiers: bool,
    /// Formula contains non-linear Int arithmetic (* with ≥2 non-constant Int args)
    pub has_nonlinear_int: bool,
    /// Formula contains non-linear Real arithmetic (* with ≥2 non-constant Real args)
    pub has_nonlinear_real: bool,
    /// Formula contains BV↔Int conversion functions (bv2nat, int2bv)
    pub has_bv_int_conversion: bool,
    /// Formula contains integer div/mod operations.
    /// These prevent CEGQI bound extraction from converging (#6889).
    pub has_int_div_mod: bool,
    /// Number of non-UF theories used
    pub num_theories: usize,
}

impl StaticFeatures {
    /// Collect features from a set of terms.
    ///
    /// Walks all terms reachable from `root_ids` and detects which theories
    /// are required based on sorts and operations used.
    pub(crate) fn collect(terms: &TermStore, root_ids: &[TermId]) -> Self {
        let mut features = Self::default();
        let mut visited = HashSet::new();

        for &id in root_ids {
            features.collect_term(terms, id, &mut visited);
        }

        // Count non-UF theories
        features.num_theories = [
            features.has_int,
            features.has_real,
            features.has_bv,
            features.has_arrays,
            features.has_strings,
            features.has_seq,
            features.has_fpa,
        ]
        .iter()
        .filter(|&&x| x)
        .count();

        features
    }

    /// Extend feature detection with declared function/constant symbols (#7442).
    ///
    /// `StaticFeatures::collect` walks only assertion term trees. When a consumer
    /// declares UF functions or array-sorted constants via `declare-fun` /
    /// `declare-const` but the assertion tree happens not to contain those terms
    /// (e.g., after push/pop), `collect` misses the UF/array requirement. This
    /// causes `narrow_linear_combo_with_features` to incorrectly strip UF/array
    /// support (e.g., AUFLIA → LIA), breaking formulas that need those theories.
    ///
    /// This method scans declared symbol sorts to ensure the features reflect
    /// all theories that the consumer has declared, not just those visible in
    /// the current assertion tree.
    pub(crate) fn extend_with_declarations<'a>(
        &mut self,
        symbols: impl Iterator<Item = (&'a str, &'a [Sort], &'a Sort)>,
    ) {
        for (name, arg_sorts, ret_sort) in symbols {
            // Non-builtin symbols with arguments are UF
            if !arg_sorts.is_empty() && !is_builtin_symbol_name(name) {
                self.has_uf = true;
            }
            // Check return sort and argument sorts for theory features
            self.detect_sort_theory(ret_sort);
            for sort in arg_sorts {
                self.detect_sort_theory(sort);
            }
        }
        // Recount theories after extension
        self.num_theories = [
            self.has_int,
            self.has_real,
            self.has_bv,
            self.has_arrays,
            self.has_strings,
            self.has_seq,
            self.has_fpa,
        ]
        .iter()
        .filter(|&&x| x)
        .count();
    }

    fn collect_term(&mut self, terms: &TermStore, id: TermId, visited: &mut HashSet<TermId>) {
        if !visited.insert(id) {
            return;
        }

        // Check sort - detect which theory is needed
        let term_sort = terms.sort(id);
        self.detect_sort_theory(term_sort);

        // Check term structure for UF/quantifiers
        match terms.get(id) {
            TermData::App(sym, args) => {
                // Check for UF (uninterpreted function applications).
                // Nullary UF applications (declare-fun f () Int) are App nodes with
                // empty args — they must also set has_uf to prevent incorrect logic
                // narrowing (e.g., AUFLIA → LIA) which strips UF support (#6498).
                if !is_builtin_symbol(sym) {
                    self.has_uf = true;
                }

                let name = sym.name();
                if name == "bv2nat" || name == "int2bv" {
                    self.has_bv_int_conversion = true;
                }
                if is_regex_symbol_name(name) {
                    self.has_regex = true;
                    // Regex belongs to the SMT-LIB strings family.
                    self.has_strings = true;
                }

                // Detect non-linear arithmetic:
                // - Multiplication: * with ≥2 non-constant arguments
                // - Real division: / with non-constant divisor (see below)
                if name == "*" && args.len() >= 2 {
                    let non_const_count = args
                        .iter()
                        .filter(|&&arg| !matches!(terms.get(arg), TermData::Const(_)))
                        .count();
                    if non_const_count >= 2 {
                        // Result sort determines Int vs Real non-linearity
                        match term_sort {
                            Sort::Int => self.has_nonlinear_int = true,
                            Sort::Real => self.has_nonlinear_real = true,
                            _ => {}
                        }
                    }
                }
                // Integer div/mod: these create opaque auxiliary variables
                // in LIA preprocessing that prevent CEGQI bound extraction
                // from converging (#6889). Detected separately from nonlinear
                // so CEGQI can bail early without upgrading the logic.
                if (name == "div" || name == "mod") && matches!(term_sort, Sort::Int) {
                    self.has_int_div_mod = true;
                }
                // Real division "/" by a non-constant IS genuinely nonlinear
                // (x/y = x * (1/y)), so detect it for NRA routing.
                // Integer "div"/"mod" are excluded — they create opaque terms
                // that LIA treats as fresh variables. Detecting them upgrades
                // QF_AUFLIA → QF_UFNIA which returns Unknown immediately (#6165).
                if name == "/"
                    && args.len() >= 2
                    && !matches!(terms.get(args[1]), TermData::Const(_))
                {
                    match term_sort {
                        Sort::Int => self.has_nonlinear_int = true,
                        Sort::Real => self.has_nonlinear_real = true,
                        _ => {}
                    }
                }

                // Recurse into children
                for &child in args {
                    self.collect_term(terms, child, visited);
                }
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                self.has_quantifiers = true;
                // Check variable sorts
                for (_name, sort) in vars {
                    self.detect_sort_theory(sort);
                }
                self.collect_term(terms, *body, visited);
            }
            TermData::Not(inner) => {
                self.collect_term(terms, *inner, visited);
            }
            TermData::Ite(cond, then_term, else_term) => {
                self.collect_term(terms, *cond, visited);
                self.collect_term(terms, *then_term, visited);
                self.collect_term(terms, *else_term, visited);
            }
            TermData::Let(bindings, body) => {
                for (_name, term) in bindings {
                    self.collect_term(terms, *term, visited);
                }
                self.collect_term(terms, *body, visited);
            }
            TermData::Const(_) | TermData::Var(_, _) => {
                // No children to recurse into
            }
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in collect_term(): {other:?}"),
        }
    }

    fn detect_sort_theory(&mut self, sort: &Sort) {
        match sort {
            Sort::Int => self.has_int = true,
            Sort::Real => self.has_real = true,
            Sort::BitVec(_) => self.has_bv = true,
            Sort::Array(arr) => {
                self.has_arrays = true;
                // Recurse into array index/element sorts
                self.detect_sort_theory(&arr.index_sort);
                self.detect_sort_theory(&arr.element_sort);
            }
            Sort::String => self.has_strings = true,
            Sort::RegLan => {
                self.has_regex = true;
                self.has_strings = true;
            }
            Sort::FloatingPoint(_, _) => self.has_fpa = true,
            Sort::Seq(elem) => {
                // Generic sequence sort — distinct from String theory
                self.has_seq = true;
                self.detect_sort_theory(elem);
            }
            Sort::Uninterpreted(_) | Sort::Datatype(_) | Sort::Bool => {
                // Pure UF or propositional - no theory flag needed
            }
            // All current Sort variants handled above (#5692).
            other => unreachable!("unhandled Sort variant in detect_sort_theory(): {other:?}"),
        }
    }
}

mod logic_inference;

/// Built-in SMT-LIB operator names that should NOT trigger `has_uf`.
const BUILTIN_SYMBOLS: &[&str] = &[
    // Boolean
    "and",
    "or",
    "not",
    "xor",
    "=>",
    "ite",
    "=",
    "distinct",
    // Arithmetic + conversions
    "+",
    "-",
    "*",
    "/",
    "div",
    "mod",
    "abs",
    "<",
    "<=",
    ">",
    ">=",
    "to_real",
    "to_int",
    "is_int",
    // Bitvectors
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvsdiv",
    "bvurem",
    "bvsrem",
    "bvneg",
    "bvand",
    "bvor",
    "bvxor",
    "bvnot",
    "bvshl",
    "bvlshr",
    "bvashr",
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
    "concat",
    "extract",
    "repeat",
    "zero_extend",
    "sign_extend",
    "rotate_left",
    "rotate_right",
    "bvcomp",
    "bv2nat",
    "int2bv",
    // Arrays
    "select",
    "store",
    "const-array",
    // Sequences (#7442: prevent misclassification as UF)
    "seq.len",
    "seq.unit",
    "seq.empty",
    "seq.++",
    "seq.nth",
    "seq.contains",
    "seq.extract",
    "seq.prefixof",
    "seq.suffixof",
    "seq.indexof",
    "seq.last_indexof",
    "seq.replace",
    // Strings
    "str.++",
    "str.len",
    "str.at",
    "str.substr",
    "str.contains",
    "str.prefixof",
    "str.suffixof",
    "str.indexof",
    "str.replace",
    "str.replace_all",
    "str.replace_re",
    "str.replace_re_all",
    "str.to_int",
    "str.to.int",
    "int.to.str",
    "str.from_int",
    "str.to_code",
    "str.from_code",
    "str.to_lower",
    "str.to_upper",
    "str.is_digit",
    "str.<",
    "str.<=",
];

/// Check if a symbol is a built-in SMT-LIB operator.
fn is_builtin_symbol(sym: &Symbol) -> bool {
    is_builtin_symbol_name(sym.name())
}

/// Check if a symbol name is a built-in SMT-LIB operator (#7442).
fn is_builtin_symbol_name(name: &str) -> bool {
    is_regex_symbol_name(name) || BUILTIN_SYMBOLS.contains(&name)
}

fn is_regex_symbol_name(name: &str) -> bool {
    matches!(
        name,
        "str.to_re"
            | "str.to.re"
            | "str.in_re"
            | "str.in.re"
            | "re.++"
            | "re.union"
            | "re.inter"
            | "re.*"
            | "re.+"
            | "re.opt"
            | "re.range"
            | "re.comp"
            | "re.diff"
            | "re.none"
            | "re.all"
            | "re.allchar"
    )
}

#[cfg(test)]
mod tests;
