// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use hashbrown::HashMap;
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::command::{Constant as ParsedConstant, Term as ParsedTerm};
use crate::sexp::{PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};
use z4_core::{Constant, Sort, Symbol, TermData, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    /// Elaborate a parsed term into the term store.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(crate) fn elaborate_term(
        &mut self,
        term: &ParsedTerm,
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match term {
            ParsedTerm::Const(c) => self.elaborate_constant(c),
            ParsedTerm::Symbol(name) => {
                // Check local environment first (let bindings, quantifier vars)
                if let Some(&id) = env.get(name) {
                    return Ok(id);
                }
                // Check function definitions FIRST (expand nullary define-fun)
                // This must come before the symbols check to properly expand
                // definitions like (define-fun my_eq () Bool (= a b))
                if let Some((params, body)) = self.fun_defs.get(name).cloned() {
                    if params.is_empty() {
                        // It's a nullary function, just expand the body
                        let term = self.elaborate_term(&body, env)?;
                        // SMT-LIB implicit Int->Real coercion for define-fun:
                        // (define-fun x () Real 0) — the numeral `0` elaborates
                        // as Int but the declared sort is Real. Coerce to match.
                        // Without this, downstream mk_eq panics on sort mismatch
                        // and release builds produce false-UNSAT (#6812).
                        if let Some(info) = self.symbols.get(name) {
                            if info.sort == Sort::Real && *self.terms.sort(term) == Sort::Int {
                                return Ok(self.coerce_int_to_real(term));
                            }
                        }
                        return Ok(term);
                    }
                }
                // Check global symbols
                if let Some(info) = self.symbols.get(name) {
                    if let Some(id) = info.term {
                        return Ok(id);
                    }
                    // It's a declared function with no definition - create a variable
                    return Ok(self.terms.mk_var(name, info.sort.clone()));
                }
                // Handle bitvector numerals: (_ bvN W) where N is value and W is width
                // SMT-LIB 2.6 Section 3.5 defines this as an alternative to #x and #b forms
                // This fixes #924: parser rejects bitvector numeral syntax
                if let Some(inner) = name.strip_prefix("(_ bv").and_then(|s| s.strip_suffix(')')) {
                    let parts: Vec<&str> = inner.split_whitespace().collect();
                    if parts.len() == 2 {
                        if let (Ok(value), Ok(width)) =
                            (parts[0].parse::<BigInt>(), parts[1].parse::<u32>())
                        {
                            return Ok(self.terms.mk_bitvec(value, width));
                        }
                    }
                }
                // Handle negative numeric literals: -1, -42, -3.14, etc.
                // In SMT-LIB these should be (- 1), (- 42) but many benchmarks
                // use the shorthand -1, -42 which the lexer parses as symbols
                if let Some(abs_str) = name.strip_prefix('-') {
                    if !abs_str.is_empty() {
                        // Check for negative integer
                        if abs_str.chars().all(|c| c.is_ascii_digit()) {
                            let abs_value: BigInt = abs_str
                                .parse()
                                .map_err(|_| ElaborateError::InvalidConstant(name.clone()))?;
                            let neg_value = -abs_value;
                            return Ok(self.terms.mk_int(neg_value));
                        }
                        // Check for negative decimal (e.g., -3.14)
                        if abs_str.contains('.')
                            && abs_str.chars().all(|c| c.is_ascii_digit() || c == '.')
                            && abs_str.chars().filter(|&c| c == '.').count() == 1
                        {
                            // Parse as rational and negate
                            let parts: Vec<&str> = abs_str.split('.').collect();
                            if parts.len() == 2 {
                                let int_part: BigInt = parts[0]
                                    .parse()
                                    .map_err(|_| ElaborateError::InvalidConstant(name.clone()))?;
                                let frac_str = parts[1];
                                let frac_part: BigInt = frac_str
                                    .parse()
                                    .map_err(|_| ElaborateError::InvalidConstant(name.clone()))?;
                                let denom = BigInt::from(10).pow(frac_str.len() as u32);
                                let numer = int_part * &denom + frac_part;
                                let rational = BigRational::new(-numer, denom);
                                return Ok(self.terms.mk_rational(rational));
                            }
                        }
                    }
                }
                // FP indexed nullary constants (#4127): (_ +zero eb sb), (_ -zero eb sb),
                // (_ +oo eb sb), (_ -oo eb sb), (_ NaN eb sb)
                if let Some(inner) = name.strip_prefix("(_ ").and_then(|s| s.strip_suffix(')')) {
                    let parts: Vec<&str> = inner.split_whitespace().collect();
                    if parts.len() == 3 {
                        if let (Ok(eb), Ok(sb)) = (parts[1].parse::<u32>(), parts[2].parse::<u32>())
                        {
                            let fp_sort = Sort::FloatingPoint(eb, sb);
                            match parts[0] {
                                "+zero" | "-zero" | "+oo" | "-oo" | "NaN" => {
                                    return Ok(self.terms.mk_app(
                                        Symbol::indexed(parts[0], vec![eb, sb]),
                                        vec![],
                                        fp_sort,
                                    ));
                                }
                                _ => {}
                            }
                        }
                    }
                }
                // Regex nullary constants: re.none, re.all, re.allchar
                // SMT-LIB 2.6 Section 3.6.4 defines these as RegLan constants.
                if matches!(name.as_str(), "re.none" | "re.all" | "re.allchar") {
                    return Ok(self.terms.mk_app(Symbol::named(name), vec![], Sort::RegLan));
                }
                // FP rounding mode constants (#4127)
                if matches!(
                    name.as_str(),
                    "RNE"
                        | "RNA"
                        | "RTP"
                        | "RTN"
                        | "RTZ"
                        | "roundNearestTiesToEven"
                        | "roundNearestTiesToAway"
                        | "roundTowardPositive"
                        | "roundTowardNegative"
                        | "roundTowardZero"
                ) {
                    // Store rounding mode as a named app with Bool sort.
                    // The FP solver matches on the symbol name, not the sort.
                    let short_name = match name.as_str() {
                        "roundNearestTiesToEven" => "RNE",
                        "roundNearestTiesToAway" => "RNA",
                        "roundTowardPositive" => "RTP",
                        "roundTowardNegative" => "RTN",
                        "roundTowardZero" => "RTZ",
                        other => other,
                    };
                    return Ok(self
                        .terms
                        .mk_app(Symbol::named(short_name), vec![], Sort::Bool));
                }
                Err(ElaborateError::UndefinedSymbol(name.clone()))
            }
            ParsedTerm::App(name, args) => self.elaborate_app(name, args, env),
            ParsedTerm::IndexedApp(name, indices, args) => {
                self.elaborate_indexed_app(name, indices, args, env)
            }
            ParsedTerm::QualifiedApp(name, sort, args) => {
                self.elaborate_qualified_app(name, sort, args, env)
            }
            ParsedTerm::Let(bindings, body) => {
                let mut new_env = env.clone();
                for (name, value) in bindings {
                    let value_id = self.elaborate_term(value, &new_env)?;
                    new_env.insert(name.clone(), value_id);
                }
                self.elaborate_term(body, &new_env)
            }
            ParsedTerm::Forall(bindings, body) => {
                // Elaborate quantifier bindings and body
                // Create fresh variables for the bound variables
                let mut new_env = env.clone();
                let mut vars: Vec<(String, Sort)> = Vec::new();
                for (name, sort) in bindings {
                    let sort = self.elaborate_sort(sort)?;
                    let var = self.terms.mk_fresh_var(name, sort.clone());
                    new_env.insert(name.clone(), var);
                    let fresh_name = match self.terms.get(var) {
                        TermData::Var(fresh_name, _) => fresh_name.clone(),
                        other => {
                            return Err(ElaborateError::Unsupported(format!(
                                "quantifier binding is not a Var: {other:?}"
                            )));
                        }
                    };
                    vars.push((fresh_name, sort));
                }
                let (body_id, triggers) =
                    self.elaborate_quantifier_body_with_triggers(body, &new_env)?;
                Ok(self.terms.mk_forall_with_triggers(vars, body_id, triggers))
            }
            ParsedTerm::Exists(bindings, body) => {
                // Elaborate quantifier bindings and body
                let mut new_env = env.clone();
                let mut vars: Vec<(String, Sort)> = Vec::new();
                for (name, sort) in bindings {
                    let sort = self.elaborate_sort(sort)?;
                    let var = self.terms.mk_fresh_var(name, sort.clone());
                    new_env.insert(name.clone(), var);
                    let fresh_name = match self.terms.get(var) {
                        TermData::Var(fresh_name, _) => fresh_name.clone(),
                        other => {
                            return Err(ElaborateError::Unsupported(format!(
                                "quantifier binding is not a Var: {other:?}"
                            )));
                        }
                    };
                    vars.push((fresh_name, sort));
                }
                let (body_id, triggers) =
                    self.elaborate_quantifier_body_with_triggers(body, &new_env)?;
                Ok(self.terms.mk_exists_with_triggers(vars, body_id, triggers))
            }
            ParsedTerm::Annotated(inner, annotations) => {
                // Elaborate the inner term
                let term_id = self.elaborate_term(inner, env)?;

                self.process_term_annotations(term_id, annotations);

                Ok(term_id)
            }
        })
    }

    pub(super) fn process_term_annotations(
        &mut self,
        term_id: TermId,
        annotations: &[(String, crate::sexp::SExpr)],
    ) {
        // Track :named for get-assignment and get-unsat-core.
        for (keyword, value) in annotations {
            if keyword != ":named" {
                continue;
            }

            if let crate::sexp::SExpr::Symbol(name) = value {
                self.named_terms.insert(name.clone(), term_id);
                // Track in current scope for proper cleanup on pop.
                if let Some(scope) = self.scopes.last_mut() {
                    scope.named_terms.push(name.clone());
                }
            }
        }
    }

    fn elaborate_quantifier_body_with_triggers(
        &mut self,
        body: &ParsedTerm,
        env: &HashMap<String, TermId>,
    ) -> Result<(TermId, Vec<Vec<TermId>>)> {
        let ParsedTerm::Annotated(inner, annotations) = body else {
            return Ok((self.elaborate_term(body, env)?, Vec::new()));
        };

        let triggers = self.elaborate_user_triggers_from_annotations(annotations, env)?;
        let body_id = self.elaborate_term(inner, env)?;
        self.process_term_annotations(body_id, annotations);
        Ok((body_id, triggers))
    }

    fn elaborate_user_triggers_from_annotations(
        &mut self,
        annotations: &[(String, crate::sexp::SExpr)],
        env: &HashMap<String, TermId>,
    ) -> Result<Vec<Vec<TermId>>> {
        let mut triggers = Vec::new();

        for (keyword, value) in annotations {
            if keyword != ":pattern" {
                continue;
            }

            let crate::sexp::SExpr::List(terms) = value else {
                return Err(ElaborateError::Unsupported(format!(
                    ":pattern expects a list of terms, got {value}"
                )));
            };

            if terms.is_empty() {
                return Err(ElaborateError::Unsupported(
                    ":pattern multi-pattern must be non-empty".to_string(),
                ));
            }

            let mut multi_trigger = Vec::with_capacity(terms.len());
            for term_sexp in terms {
                let term = ParsedTerm::from_sexp(term_sexp).map_err(|e| {
                    ElaborateError::Unsupported(format!("invalid :pattern term: {e}"))
                })?;
                multi_trigger.push(self.elaborate_term(&term, env)?);
            }
            triggers.push(multi_trigger);
        }

        Ok(triggers)
    }

    /// Elaborate a constant
    fn elaborate_constant(&mut self, constant: &ParsedConstant) -> Result<TermId> {
        match constant {
            ParsedConstant::True => Ok(self.terms.true_term()),
            ParsedConstant::False => Ok(self.terms.false_term()),
            ParsedConstant::Numeral(s) => {
                let value: BigInt = s
                    .parse()
                    .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                Ok(self.terms.mk_int(value))
            }
            ParsedConstant::Decimal(s) => {
                // Parse as rational
                let parts: Vec<&str> = s.split('.').collect();
                if parts.len() == 2 {
                    let int_part: BigInt = parts[0]
                        .parse()
                        .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                    let frac_str = parts[1];
                    let frac_part: BigInt = frac_str
                        .parse()
                        .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                    let denom = BigInt::from(10).pow(frac_str.len() as u32);
                    let numer = int_part * &denom + frac_part;
                    let rational = BigRational::new(numer, denom);
                    Ok(self.terms.mk_rational(rational))
                } else {
                    let value: BigInt = s
                        .parse()
                        .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                    Ok(self.terms.mk_rational(BigRational::from(value)))
                }
            }
            ParsedConstant::Hexadecimal(s) => {
                // #xABCD -> bitvector
                let hex = s.trim_start_matches("#x");
                let value = BigInt::parse_bytes(hex.as_bytes(), 16)
                    .ok_or_else(|| ElaborateError::InvalidConstant(s.clone()))?;
                let width = (hex.len() * 4) as u32;
                Ok(self.terms.mk_bitvec(value, width))
            }
            ParsedConstant::Binary(s) => {
                // #b1010 -> bitvector
                let bin = s.trim_start_matches("#b");
                let value = BigInt::parse_bytes(bin.as_bytes(), 2)
                    .ok_or_else(|| ElaborateError::InvalidConstant(s.clone()))?;
                let width = bin.len() as u32;
                Ok(self.terms.mk_bitvec(value, width))
            }
            ParsedConstant::String(s) => Ok(self.terms.mk_string(s.clone())),
        }
    }

    pub(super) fn promote_int_consts_to_real(&mut self, args: &mut [TermId]) -> Result<()> {
        for arg in args {
            if *self.terms.sort(*arg) != Sort::Int {
                continue;
            }
            // SMT-LIB implicit Int->Real coercion: coerce_int_to_real
            // constant-folds Int literals to Rational, rebuilds ITE with
            // coerced branches, and wraps other Int terms in to_real
            // (needed for mixed Int/Real logics like QF_LIRA).
            *arg = self.coerce_int_to_real(*arg);
        }
        Ok(())
    }

    /// Coerce an Int-sorted term to Real. Constants are converted directly.
    /// ITE terms are rebuilt with coerced branches. Other terms are wrapped
    /// in `to_real`.
    pub(super) fn coerce_int_to_real(&mut self, term: TermId) -> TermId {
        match self.terms.get(term).clone() {
            TermData::Const(Constant::Int(n)) => self.terms.mk_rational(BigRational::from(n)),
            TermData::Ite(cond, then_br, else_br) => {
                let then_real = self.coerce_int_to_real(then_br);
                let else_real = self.coerce_int_to_real(else_br);
                self.terms.mk_ite(cond, then_real, else_real)
            }
            _ => self.terms.mk_to_real(term),
        }
    }

    pub(super) fn maybe_promote_numeric_args(&mut self, args: &mut [TermId]) -> Result<()> {
        let has_real = args.iter().any(|&id| *self.terms.sort(id) == Sort::Real);
        let has_int = args.iter().any(|&id| *self.terms.sort(id) == Sort::Int);
        if has_real && has_int {
            // SMT-LIB numerals are usable in both Int and Real contexts. If we see a mix
            // of Int/Real in a numeric operator, treat Int constants as Real constants.
            self.promote_int_consts_to_real(args)?;
        }
        Ok(())
    }

    /// Coerce BV width mismatches in equality/distinct args (#5115).
    /// Competition benchmarks (MCMPC family) use `(= #x1 ((_ extract N N) x))`
    /// where `#x1` is BitVec(4) and extract produces BitVec(1). SMT-LIB
    /// strictly requires same-sort `=` args, but Z3/Bitwuzla/CVC5 handle this.
    /// Zero-extend the narrower operand to match the wider one.
    pub(super) fn maybe_coerce_bv_widths(&mut self, args: &mut [TermId]) {
        if args.len() != 2 {
            return;
        }
        let w0 = match self.terms.sort(args[0]) {
            Sort::BitVec(bv) => bv.width,
            _ => return,
        };
        let w1 = match self.terms.sort(args[1]) {
            Sort::BitVec(bv) => bv.width,
            _ => return,
        };
        if w0 == w1 {
            return;
        }
        if w0 < w1 {
            args[0] = self.terms.mk_bvzero_extend(w1 - w0, args[0]);
        } else {
            args[1] = self.terms.mk_bvzero_extend(w0 - w1, args[1]);
        }
    }

    pub(super) fn expect_exact_arity(
        &self,
        name: &str,
        args: &[TermId],
        expected: usize,
    ) -> Result<()> {
        if args.len() == expected {
            Ok(())
        } else {
            Err(ElaborateError::InvalidConstant(format!(
                "{name} requires {expected} arguments"
            )))
        }
    }

    pub(super) fn expect_min_arity(&self, name: &str, args: &[TermId], min: usize) -> Result<()> {
        if args.len() >= min {
            Ok(())
        } else {
            Err(ElaborateError::InvalidConstant(format!(
                "{name} requires at least {min} arguments"
            )))
        }
    }

    pub(super) fn expect_arg_sort(&self, arg: TermId, expected: &Sort) -> Result<()> {
        let actual = self.terms.sort(arg).clone();
        if &actual == expected {
            Ok(())
        } else {
            Err(ElaborateError::SortMismatch {
                expected: expected.to_string(),
                actual: actual.to_string(),
            })
        }
    }

    pub(super) fn expect_all_args_sort(&self, args: &[TermId], expected: &Sort) -> Result<()> {
        for &arg in args {
            self.expect_arg_sort(arg, expected)?;
        }
        Ok(())
    }
}
