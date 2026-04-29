// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type analysis engine for `tla2 typecheck`.
//!
//! Walks the TIR expression tree to detect type-level inconsistencies:
//! - Arithmetic on non-integer operands
//! - Boolean operators on non-boolean operands
//! - Function application on non-function values
//! - Set membership with non-set RHS
//! - Annotation-vs-inferred type mismatches
//!
//! Part of #3750: Apalache Gap 2.

use tla_tir::{TirExpr, TirLetDef, TirModule, TirType};

use super::{AnnotationInfo, LocationInfo, OperatorTypeInfo, TypecheckError};

// ---------------------------------------------------------------------------
// Annotation type parser
// ---------------------------------------------------------------------------

/// Parse an Apalache-style `@type:` annotation string into a `TirType`.
///
/// Supported syntax (subset of Apalache Snowcat grammar):
///   Bool, Int, Str, Set(T), Seq(T), T -> U, <<T, U>>, [field: T, ...]
///   Parenthesized types for grouping: (Int -> Bool)
///   Type variables: lowercase identifiers like `a`, `b` map to `TirType::Var`
///   Variant types: `Tag1(T1) | Tag2(T2)`
///
/// Returns `None` if the annotation cannot be parsed.
pub(super) fn parse_type_annotation(s: &str) -> Option<TirType> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    let mut parser = TypeAnnotationParser::new(s);
    let ty = parser.parse_top_level()?;
    // Ensure we consumed everything
    parser.skip_ws();
    if parser.pos < parser.input.len() {
        return None;
    }
    Some(ty)
}

struct TypeAnnotationParser<'a> {
    input: &'a [u8],
    pos: usize,
    /// Map from type variable name to variable id (consistent within one annotation).
    var_map: std::collections::HashMap<String, u32>,
    /// Next type variable id to allocate.
    next_var: u32,
}

impl<'a> TypeAnnotationParser<'a> {
    fn new(s: &'a str) -> Self {
        Self {
            input: s.as_bytes(),
            pos: 0,
            var_map: std::collections::HashMap::new(),
            next_var: 0,
        }
    }

    /// Allocate or reuse a type variable id for a given name.
    fn get_or_create_var(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.var_map.get(name) {
            id
        } else {
            let id = self.next_var;
            self.next_var += 1;
            self.var_map.insert(name.to_string(), id);
            id
        }
    }

    /// Parse top-level: first try variant syntax `Tag(T) | Tag(T)`,
    /// then fall back to normal type parsing.
    fn parse_top_level(&mut self) -> Option<TirType> {
        // Try to parse as variant: `Tag1(T1) | Tag2(T2) | ...`
        let save = self.pos;
        let save_var_map = self.var_map.clone();
        let save_next_var = self.next_var;
        if let Some(variant) = self.try_parse_variant() {
            return Some(variant);
        }
        // Restore on failure.
        self.pos = save;
        self.var_map = save_var_map;
        self.next_var = save_next_var;

        // Normal type parsing.
        self.parse_type()
    }

    /// Try to parse a variant type: `Tag1(T1) | Tag2(T2) | ...`
    ///
    /// Each case is `UpperIdent(Type)`. Returns `None` if the input doesn't
    /// match variant syntax, allowing the caller to fall back.
    fn try_parse_variant(&mut self) -> Option<TirType> {
        let mut cases = Vec::new();

        let first = self.parse_variant_case()?;
        cases.push(first);

        // Must have at least one `|` to be a variant.
        self.skip_ws();
        if self.pos >= self.input.len() || self.input[self.pos] != b'|' {
            return None; // Not a variant — only one case without `|`.
        }

        while self.pos < self.input.len() && self.input[self.pos] == b'|' {
            self.pos += 1; // consume `|`
            let case = self.parse_variant_case()?;
            cases.push(case);
            self.skip_ws();
        }

        Some(TirType::Variant(cases))
    }

    /// Parse a single variant case: `Tag(Type)` where Tag is an uppercase identifier.
    fn parse_variant_case(&mut self) -> Option<(String, TirType)> {
        self.skip_ws();
        let save = self.pos;
        let tag = self.read_ident()?;
        // Tag must start with uppercase and NOT be a type keyword.
        if !tag.chars().next().map_or(false, |c| c.is_uppercase())
            || matches!(
                tag.as_str(),
                "Bool" | "Int" | "Str" | "Set" | "Seq" | "BOOLEAN" | "STRING"
            )
        {
            self.pos = save;
            return None;
        }
        if !self.eat(b'(') {
            self.pos = save;
            return None;
        }
        let payload = self.parse_type()?;
        if !self.eat(b')') {
            self.pos = save;
            return None;
        }
        Some((tag, payload))
    }

    fn skip_ws(&mut self) {
        while self.pos < self.input.len() && self.input[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_ws();
        self.input.get(self.pos).copied()
    }

    fn eat(&mut self, ch: u8) -> bool {
        self.skip_ws();
        if self.pos < self.input.len() && self.input[self.pos] == ch {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_str(&mut self, s: &str) -> bool {
        self.skip_ws();
        let bytes = s.as_bytes();
        if self.pos + bytes.len() <= self.input.len()
            && &self.input[self.pos..self.pos + bytes.len()] == bytes
        {
            // Ensure the match is not a prefix of a longer identifier
            let end = self.pos + bytes.len();
            if end < self.input.len()
                && (self.input[end].is_ascii_alphanumeric() || self.input[end] == b'_')
            {
                return false;
            }
            self.pos += bytes.len();
            true
        } else {
            false
        }
    }

    fn read_ident(&mut self) -> Option<String> {
        self.skip_ws();
        let start = self.pos;
        while self.pos < self.input.len()
            && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_')
        {
            self.pos += 1;
        }
        if self.pos > start {
            Some(
                std::str::from_utf8(&self.input[start..self.pos])
                    .ok()?
                    .to_string(),
            )
        } else {
            None
        }
    }

    /// Parse a type expression, handling `->` and `=>` at the lowest precedence.
    ///
    /// `->` is the TLA+ function type: `Int -> Bool` means `[Int -> Bool]`.
    /// `=>` is the Apalache operator type: `(Int, Bool) => Str` means an
    /// operator taking Int and Bool and returning Str. We map this to
    /// `Func(Tuple(Int, Bool), Str)` for compatibility.
    fn parse_type(&mut self) -> Option<TirType> {
        let lhs = self.parse_atom()?;

        self.skip_ws();
        // Check for `=>` (Apalache operator type)
        if self.pos + 1 < self.input.len()
            && self.input[self.pos] == b'='
            && self.input[self.pos + 1] == b'>'
        {
            self.pos += 2;
            let rhs = self.parse_type()?;
            // `(T, U) => V` maps to Func(Tuple(T, U), V)
            // Single-arg `T => V` maps to Func(T, V)
            return Some(TirType::Func(Box::new(lhs), Box::new(rhs)));
        }

        // Check for `->` (function type)
        if self.pos + 1 < self.input.len()
            && self.input[self.pos] == b'-'
            && self.input[self.pos + 1] == b'>'
        {
            self.pos += 2;
            let rhs = self.parse_type()?;
            Some(TirType::Func(Box::new(lhs), Box::new(rhs)))
        } else {
            Some(lhs)
        }
    }

    /// Parse an atomic type (non-arrow).
    fn parse_atom(&mut self) -> Option<TirType> {
        self.skip_ws();

        // Parenthesized type or tuple: (T) or (T -> U) or (T, U, V) for multi-arg operator
        if self.peek() == Some(b'(') {
            self.pos += 1;
            let first = self.parse_type()?;

            // Check for comma-separated list: (T, U) => V is Apalache multi-arg operator
            if self.peek() == Some(b',') {
                let mut args = vec![first];
                while self.eat(b',') {
                    args.push(self.parse_type()?);
                }
                if !self.eat(b')') {
                    return None;
                }
                // (T, U) by itself is a tuple type in parentheses
                // But if followed by => or ->, the tuple is the domain of a function
                // We return a Tuple and let the caller handle =>
                return Some(TirType::Tuple(args));
            }

            if !self.eat(b')') {
                return None;
            }
            return Some(first);
        }

        // Tuple: <<T, U, ...>>
        if self.pos + 1 < self.input.len()
            && self.input[self.pos] == b'<'
            && self.input[self.pos + 1] == b'<'
        {
            self.pos += 2;
            let mut elems = Vec::new();
            if !(self.pos + 1 < self.input.len()
                && self.input[self.pos] == b'>'
                && self.input[self.pos + 1] == b'>')
            {
                elems.push(self.parse_type()?);
                while self.eat(b',') {
                    elems.push(self.parse_type()?);
                }
            }
            self.skip_ws();
            if self.pos + 1 < self.input.len()
                && self.input[self.pos] == b'>'
                && self.input[self.pos + 1] == b'>'
            {
                self.pos += 2;
            } else {
                return None;
            }
            return Some(TirType::Tuple(elems));
        }

        // Record: [field: T, ...] or function type [T -> U]
        if self.peek() == Some(b'[') {
            self.pos += 1;
            self.skip_ws();

            // Check if this is a function type [T -> U] by looking ahead.
            // Save full parser state since speculative parsing may allocate type variables.
            let save = self.pos;
            let save_vm = self.var_map.clone();
            let save_nv = self.next_var;
            if let Some(first) = self.parse_type() {
                self.skip_ws();
                if self.pos + 1 < self.input.len()
                    && self.input[self.pos] == b'-'
                    && self.input[self.pos + 1] == b'>'
                {
                    // [T -> U] function set type
                    self.pos += 2;
                    let rng = self.parse_type()?;
                    if !self.eat(b']') {
                        return None;
                    }
                    return Some(TirType::Func(Box::new(first), Box::new(rng)));
                }
                // Not a function type; restore full parser state
                self.pos = save;
                self.var_map = save_vm;
                self.next_var = save_nv;
            } else {
                self.pos = save;
                self.var_map = save_vm;
                self.next_var = save_nv;
            }

            // Record: [field: T, ...] or open record [field: T, ...rowvar]
            let mut fields = Vec::new();
            let mut row_var: Option<u32> = None;
            self.skip_ws();
            if self.peek() != Some(b']') {
                loop {
                    self.skip_ws();
                    // Check for `...varname` (open record row variable) or `]`
                    if self.pos + 2 < self.input.len()
                        && self.input[self.pos] == b'.'
                        && self.input[self.pos + 1] == b'.'
                        && self.input[self.pos + 2] == b'.'
                    {
                        self.pos += 3; // consume `...`
                        let row_name = self.read_ident()?;
                        row_var = Some(self.get_or_create_var(&row_name));
                        break;
                    }
                    let fname = self.read_ident()?;
                    if !self.eat(b':') {
                        return None;
                    }
                    let fty = self.parse_type()?;
                    fields.push((tla_core::intern_name(&fname), fty));
                    if !self.eat(b',') {
                        break;
                    }
                }
            }
            if !self.eat(b']') {
                return None;
            }
            if let Some(rv) = row_var {
                return Some(TirType::OpenRecord(fields, rv));
            }
            return Some(TirType::Record(fields));
        }

        // Named types: Bool, Int, Str, Set(T), Seq(T), or type variable
        if self.eat_str("Bool") {
            return Some(TirType::Bool);
        }
        if self.eat_str("Int") {
            return Some(TirType::Int);
        }
        if self.eat_str("Str") {
            return Some(TirType::Str);
        }
        if self.eat_str("BOOLEAN") {
            return Some(TirType::Set(Box::new(TirType::Bool)));
        }
        if self.eat_str("STRING") {
            return Some(TirType::Set(Box::new(TirType::Str)));
        }
        if self.eat_str("Set") {
            if !self.eat(b'(') {
                return None;
            }
            let inner = self.parse_type()?;
            if !self.eat(b')') {
                return None;
            }
            return Some(TirType::Set(Box::new(inner)));
        }
        if self.eat_str("Seq") {
            if !self.eat(b'(') {
                return None;
            }
            let inner = self.parse_type()?;
            if !self.eat(b')') {
                return None;
            }
            return Some(TirType::Seq(Box::new(inner)));
        }

        // Apalache type variables (lowercase identifiers like `a`, `b`, etc.)
        // are mapped to `TirType::Var` with consistent ids within one annotation.
        let save = self.pos;
        if let Some(ident) = self.read_ident() {
            if ident.chars().next().map_or(false, |c| c.is_lowercase()) {
                let var_id = self.get_or_create_var(&ident);
                return Some(TirType::Var(var_id));
            }
            // Unknown type name — restore and fail
            self.pos = save;
        }

        None
    }
}

// ---------------------------------------------------------------------------
// Type error detection via TIR walk
// ---------------------------------------------------------------------------

/// Accumulated type analysis results.
pub(super) struct AnalysisResult {
    /// Type errors detected during TIR walk.
    pub errors: Vec<TypecheckError>,
    /// LET-definition type info (name, params, body type).
    pub let_defs: Vec<OperatorTypeInfo>,
}

/// Run type analysis on a TIR module.
///
/// This walks every operator body and all nested LET definitions, checking for
/// type-level inconsistencies. It also compares `@type:` annotations (parsed
/// into `TirType`) against the inferred TIR types for matching operators.
pub(super) fn analyze_module(
    tir_module: &TirModule,
    annotations: &[AnnotationInfo],
    file_path: &str,
) -> AnalysisResult {
    let mut errors = Vec::new();
    let mut let_defs = Vec::new();

    // Walk each top-level operator body
    for op in &tir_module.operators {
        walk_expr(&op.body.node, &mut errors, &mut let_defs);
    }

    // Check annotations vs inferred types
    check_annotation_mismatches(tir_module, annotations, file_path, &mut errors);

    AnalysisResult { errors, let_defs }
}

/// Walk a TIR expression tree, collecting type errors and LET definition types.
fn walk_expr(
    expr: &TirExpr,
    errors: &mut Vec<TypecheckError>,
    let_defs: &mut Vec<OperatorTypeInfo>,
) {
    match expr {
        TirExpr::ArithBinOp { left, right, .. } => {
            check_expected_type(&left.node, &TirType::Int, "arithmetic operand", errors);
            check_expected_type(&right.node, &TirType::Int, "arithmetic operand", errors);
            walk_expr(&left.node, errors, let_defs);
            walk_expr(&right.node, errors, let_defs);
        }
        TirExpr::ArithNeg(inner) => {
            check_expected_type(&inner.node, &TirType::Int, "arithmetic negation", errors);
            walk_expr(&inner.node, errors, let_defs);
        }
        TirExpr::BoolBinOp { left, right, .. } => {
            check_expected_type(&left.node, &TirType::Bool, "boolean operand", errors);
            check_expected_type(&right.node, &TirType::Bool, "boolean operand", errors);
            walk_expr(&left.node, errors, let_defs);
            walk_expr(&right.node, errors, let_defs);
        }
        TirExpr::BoolNot(inner) => {
            check_expected_type(&inner.node, &TirType::Bool, "boolean negation", errors);
            walk_expr(&inner.node, errors, let_defs);
        }
        TirExpr::In { elem, set } => {
            check_is_set_type(&set.node, "\\in RHS", errors);
            check_set_membership_consistency(&elem.node, &set.node, errors);
            walk_expr(&elem.node, errors, let_defs);
            walk_expr(&set.node, errors, let_defs);
        }
        TirExpr::Subseteq { left, right } => {
            check_is_set_type(&left.node, "\\subseteq LHS", errors);
            check_is_set_type(&right.node, "\\subseteq RHS", errors);
            walk_expr(&left.node, errors, let_defs);
            walk_expr(&right.node, errors, let_defs);
        }
        TirExpr::FuncApply { func, arg } => {
            check_is_func_type(&func.node, "function application", errors);
            check_func_apply_consistency(&func.node, &arg.node, errors);
            walk_expr(&func.node, errors, let_defs);
            walk_expr(&arg.node, errors, let_defs);
        }
        TirExpr::Domain(inner) => {
            check_is_func_type(&inner.node, "DOMAIN operand", errors);
            walk_expr(&inner.node, errors, let_defs);
        }
        TirExpr::RecordAccess { record, field } => {
            let ty = record.node.ty();
            if !matches!(
                ty,
                TirType::Record(_) | TirType::OpenRecord(_, _) | TirType::Dyn | TirType::Var(_)
            ) {
                errors.push(TypecheckError {
                    message: format!(
                        "record access `.{}` on non-record type: {}",
                        field.name,
                        super::format_tir_type(&ty),
                    ),
                    location: None,
                });
            }
            walk_expr(&record.node, errors, let_defs);
        }
        TirExpr::If { cond, then_, else_ } => {
            check_expected_type(&cond.node, &TirType::Bool, "IF condition", errors);
            walk_expr(&cond.node, errors, let_defs);
            walk_expr(&then_.node, errors, let_defs);
            walk_expr(&else_.node, errors, let_defs);
        }
        TirExpr::Range { lo, hi } => {
            check_expected_type(&lo.node, &TirType::Int, "range lower bound", errors);
            check_expected_type(&hi.node, &TirType::Int, "range upper bound", errors);
            walk_expr(&lo.node, errors, let_defs);
            walk_expr(&hi.node, errors, let_defs);
        }
        TirExpr::Forall { vars, body } | TirExpr::Exists { vars, body } => {
            check_expected_type(&body.node, &TirType::Bool, "quantifier body", errors);
            for v in vars {
                if let Some(d) = &v.domain {
                    walk_expr(&d.node, errors, let_defs);
                }
            }
            walk_expr(&body.node, errors, let_defs);
        }
        TirExpr::Choose { var, body } => {
            check_expected_type(&body.node, &TirType::Bool, "CHOOSE predicate", errors);
            if let Some(d) = &var.domain {
                walk_expr(&d.node, errors, let_defs);
            }
            walk_expr(&body.node, errors, let_defs);
        }
        TirExpr::Let { defs, body } => {
            for def in defs {
                collect_let_def(def, let_defs);
                walk_expr(&def.body.node, errors, let_defs);
            }
            walk_expr(&body.node, errors, let_defs);
        }
        TirExpr::Case { arms, other } => {
            for arm in arms {
                check_expected_type(&arm.guard.node, &TirType::Bool, "CASE guard", errors);
                walk_expr(&arm.guard.node, errors, let_defs);
                walk_expr(&arm.body.node, errors, let_defs);
            }
            if let Some(other) = other {
                walk_expr(&other.node, errors, let_defs);
            }
        }
        TirExpr::SetBinOp { left, right, .. } => {
            check_is_set_type(&left.node, "set binary op LHS", errors);
            check_is_set_type(&right.node, "set binary op RHS", errors);
            check_set_binop_consistency(&left.node, &right.node, errors);
            walk_expr(&left.node, errors, let_defs);
            walk_expr(&right.node, errors, let_defs);
        }
        TirExpr::Powerset(inner) => {
            check_is_set_type(&inner.node, "SUBSET operand", errors);
            walk_expr(&inner.node, errors, let_defs);
        }
        TirExpr::BigUnion(inner) => {
            // UNION expects Set(Set(T))
            walk_expr(&inner.node, errors, let_defs);
        }
        TirExpr::KSubset { base, k } => {
            check_is_set_type(&base.node, "KSubset base", errors);
            walk_expr(&base.node, errors, let_defs);
            walk_expr(&k.node, errors, let_defs);
        }
        TirExpr::SetFilter { var, body } => {
            check_expected_type(&body.node, &TirType::Bool, "set filter predicate", errors);
            if let Some(d) = &var.domain {
                walk_expr(&d.node, errors, let_defs);
            }
            walk_expr(&body.node, errors, let_defs);
        }
        TirExpr::SetBuilder { body, vars } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    walk_expr(&d.node, errors, let_defs);
                }
            }
            walk_expr(&body.node, errors, let_defs);
        }
        TirExpr::SetEnum(elems) => {
            for e in elems {
                walk_expr(&e.node, errors, let_defs);
            }
        }
        TirExpr::FuncDef { vars, body } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    walk_expr(&d.node, errors, let_defs);
                }
            }
            walk_expr(&body.node, errors, let_defs);
        }
        TirExpr::FuncSet { domain, range } => {
            walk_expr(&domain.node, errors, let_defs);
            walk_expr(&range.node, errors, let_defs);
        }
        TirExpr::Record(fields) | TirExpr::RecordSet(fields) => {
            for (_, expr) in fields {
                walk_expr(&expr.node, errors, let_defs);
            }
        }
        TirExpr::Tuple(elems) | TirExpr::Times(elems) => {
            for e in elems {
                walk_expr(&e.node, errors, let_defs);
            }
        }
        TirExpr::Except { base, specs } => {
            walk_expr(&base.node, errors, let_defs);
            for spec in specs {
                walk_expr(&spec.value.node, errors, let_defs);
                for path_elem in &spec.path {
                    if let tla_tir::TirExceptPathElement::Index(idx) = path_elem {
                        walk_expr(&idx.node, errors, let_defs);
                    }
                }
            }
        }
        TirExpr::Cmp { left, right, .. } => {
            walk_expr(&left.node, errors, let_defs);
            walk_expr(&right.node, errors, let_defs);
        }
        TirExpr::Unchanged(inner) | TirExpr::Prime(inner) => {
            walk_expr(&inner.node, errors, let_defs);
        }
        TirExpr::ActionSubscript {
            action, subscript, ..
        } => {
            walk_expr(&action.node, errors, let_defs);
            walk_expr(&subscript.node, errors, let_defs);
        }
        TirExpr::Always(inner) | TirExpr::Eventually(inner) | TirExpr::Enabled(inner) => {
            walk_expr(&inner.node, errors, let_defs);
        }
        TirExpr::LeadsTo { left, right }
        | TirExpr::WeakFair {
            vars: left,
            action: right,
        }
        | TirExpr::StrongFair {
            vars: left,
            action: right,
        } => {
            walk_expr(&left.node, errors, let_defs);
            walk_expr(&right.node, errors, let_defs);
        }
        TirExpr::Apply { op, args } => {
            walk_expr(&op.node, errors, let_defs);
            for a in args {
                walk_expr(&a.node, errors, let_defs);
            }
        }
        TirExpr::Lambda { body, .. } => {
            walk_expr(&body.node, errors, let_defs);
        }
        TirExpr::Label { body, .. } => {
            walk_expr(&body.node, errors, let_defs);
        }
        TirExpr::OperatorRef(op_ref) => {
            for seg in &op_ref.path {
                for a in &seg.args {
                    walk_expr(&a.node, errors, let_defs);
                }
            }
            for a in &op_ref.args {
                walk_expr(&a.node, errors, let_defs);
            }
        }
        // Leaf nodes: no children to walk
        TirExpr::Const { .. } | TirExpr::Name(_) | TirExpr::ExceptAt | TirExpr::OpRef(_) => {}
    }
}

fn collect_let_def(def: &TirLetDef, let_defs: &mut Vec<OperatorTypeInfo>) {
    let_defs.push(OperatorTypeInfo {
        name: def.name.clone(),
        params: def.params.clone(),
        body_type: super::format_tir_type(&def.body.node.ty()),
    });
}

/// Check that an expression's inferred type matches an expected type.
///
/// Reports an error if the inferred type is concrete (not Dyn) and differs
/// from the expected type. Dyn is treated as a wildcard — it matches anything.
fn check_expected_type(
    expr: &TirExpr,
    expected: &TirType,
    context: &str,
    errors: &mut Vec<TypecheckError>,
) {
    let actual = expr.ty();
    if actual == TirType::Dyn
        || *expected == TirType::Dyn
        || matches!(actual, TirType::Var(_))
        || matches!(expected, TirType::Var(_))
    {
        return; // Dyn/Var is the "unknown" type — no constraint violation
    }
    if actual != *expected {
        errors.push(TypecheckError {
            message: format!(
                "type mismatch in {}: expected {}, found {}",
                context,
                super::format_tir_type(expected),
                super::format_tir_type(&actual),
            ),
            location: None,
        });
    }
}

/// Check that an expression has a set type.
fn check_is_set_type(expr: &TirExpr, context: &str, errors: &mut Vec<TypecheckError>) {
    let ty = expr.ty();
    if matches!(ty, TirType::Set(_) | TirType::Dyn | TirType::Var(_)) {
        return;
    }
    errors.push(TypecheckError {
        message: format!(
            "expected set type in {}, found {}",
            context,
            super::format_tir_type(&ty),
        ),
        location: None,
    });
}

/// Check that an expression has a function type (or Dyn/Var).
fn check_is_func_type(expr: &TirExpr, context: &str, errors: &mut Vec<TypecheckError>) {
    let ty = expr.ty();
    if matches!(ty, TirType::Func(_, _) | TirType::Dyn | TirType::Var(_)) {
        return;
    }
    errors.push(TypecheckError {
        message: format!(
            "expected function type in {}, found {}",
            context,
            super::format_tir_type(&ty),
        ),
        location: None,
    });
}

/// Compare `@type:` annotations against the TIR-inferred types for each operator.
fn check_annotation_mismatches(
    tir_module: &TirModule,
    annotations: &[AnnotationInfo],
    file_path: &str,
    errors: &mut Vec<TypecheckError>,
) {
    for ann in annotations {
        let parsed = match parse_type_annotation(&ann.annotation) {
            Some(ty) => ty,
            None => {
                errors.push(TypecheckError {
                    message: format!(
                        "could not parse @type annotation for `{}`: `{}`",
                        ann.operator, ann.annotation,
                    ),
                    location: Some(LocationInfo {
                        file: file_path.to_string(),
                        line: ann.line,
                        column: 0,
                    }),
                });
                continue;
            }
        };

        // Find the matching TIR operator
        if let Some(op) = tir_module.operators.iter().find(|o| o.name == ann.operator) {
            let inferred = op.body.node.ty();
            if !types_compatible(&parsed, &inferred) {
                errors.push(TypecheckError {
                    message: format!(
                        "annotation mismatch for `{}`: annotated {}, inferred {}",
                        ann.operator,
                        super::format_tir_type(&parsed),
                        super::format_tir_type(&inferred),
                    ),
                    location: Some(LocationInfo {
                        file: file_path.to_string(),
                        line: ann.line,
                        column: 0,
                    }),
                });
            }
        }
        // If the operator isn't found in TIR, it might have been filtered out;
        // not an error in the type system.
    }
}

/// Check structural compatibility between two types.
///
/// `Dyn` and `Var` are compatible with any type (they represent unknown/polymorphic).
/// Uses structural subtyping for records (field name + type compatibility).
fn types_compatible(a: &TirType, b: &TirType) -> bool {
    if *a == TirType::Dyn
        || *b == TirType::Dyn
        || matches!(a, TirType::Var(_))
        || matches!(b, TirType::Var(_))
    {
        return true;
    }
    match (a, b) {
        (TirType::Bool, TirType::Bool)
        | (TirType::Int, TirType::Int)
        | (TirType::Str, TirType::Str) => true,
        (TirType::Set(a_inner), TirType::Set(b_inner)) => types_compatible(a_inner, b_inner),
        (TirType::Seq(a_inner), TirType::Seq(b_inner)) => types_compatible(a_inner, b_inner),
        (TirType::Func(a_dom, a_range), TirType::Func(b_dom, b_range)) => {
            types_compatible(a_dom, b_dom) && types_compatible(a_range, b_range)
        }
        (TirType::Tuple(a_elems), TirType::Tuple(b_elems)) => {
            a_elems.len() == b_elems.len()
                && a_elems
                    .iter()
                    .zip(b_elems.iter())
                    .all(|(a, b)| types_compatible(a, b))
        }
        (TirType::Record(a_fields), TirType::Record(b_fields)) => {
            // Structural subtyping: same field names, compatible field types.
            // Order-independent: both sorted by NameId.
            a_fields.len() == b_fields.len()
                && a_fields.iter().all(|(a_id, a_ty)| {
                    b_fields
                        .iter()
                        .find(|(b_id, _)| *b_id == *a_id)
                        .map_or(false, |(_, b_ty)| types_compatible(a_ty, b_ty))
                })
        }
        // OpenRecord is compatible with Record if known fields match
        (TirType::OpenRecord(a_fields, _), TirType::Record(b_fields))
        | (TirType::Record(b_fields), TirType::OpenRecord(a_fields, _)) => {
            a_fields.iter().all(|(a_id, a_ty)| {
                b_fields
                    .iter()
                    .find(|(b_id, _)| *b_id == *a_id)
                    .map_or(false, |(_, b_ty)| types_compatible(a_ty, b_ty))
            })
        }
        (TirType::OpenRecord(a_fields, _), TirType::OpenRecord(b_fields, _)) => {
            // Both open: shared fields must be compatible
            a_fields.iter().all(|(a_id, a_ty)| {
                b_fields
                    .iter()
                    .find(|(b_id, _)| *b_id == *a_id)
                    .map_or(true, |(_, b_ty)| types_compatible(a_ty, b_ty))
            })
        }
        (TirType::Variant(a_cases), TirType::Variant(b_cases)) => {
            // Same tags, compatible payloads
            a_cases.len() == b_cases.len()
                && a_cases.iter().all(|(a_tag, a_ty)| {
                    b_cases
                        .iter()
                        .find(|(b_tag, _)| *b_tag == *a_tag)
                        .map_or(false, |(_, b_ty)| types_compatible(a_ty, b_ty))
                })
        }
        _ => false,
    }
}

/// Check type consistency of a set membership expression.
///
/// If `elem \in set_expr`, the element type should be compatible with the
/// set's element type.
fn check_set_membership_consistency(
    elem: &TirExpr,
    set: &TirExpr,
    errors: &mut Vec<TypecheckError>,
) {
    let elem_ty = elem.ty();
    let set_ty = set.ty();

    if elem_ty == TirType::Dyn
        || set_ty == TirType::Dyn
        || matches!(elem_ty, TirType::Var(_))
        || matches!(set_ty, TirType::Var(_))
    {
        return;
    }
    if let TirType::Set(inner) = &set_ty {
        if **inner != TirType::Dyn
            && !matches!(inner.as_ref(), TirType::Var(_))
            && !types_compatible(&elem_ty, inner)
        {
            errors.push(TypecheckError {
                message: format!(
                    "set membership type mismatch: element has type {}, but set has element type {}",
                    super::format_tir_type(&elem_ty),
                    super::format_tir_type(inner),
                ),
                location: None,
            });
        }
    }
}

/// Check function application type consistency.
///
/// If `f[x]` and `f : D -> R`, then `x` should be compatible with `D`.
fn check_func_apply_consistency(func: &TirExpr, arg: &TirExpr, errors: &mut Vec<TypecheckError>) {
    let func_ty = func.ty();
    let arg_ty = arg.ty();

    if func_ty == TirType::Dyn
        || arg_ty == TirType::Dyn
        || matches!(func_ty, TirType::Var(_))
        || matches!(arg_ty, TirType::Var(_))
    {
        return;
    }
    if let TirType::Func(domain, _) = &func_ty {
        if **domain != TirType::Dyn
            && !matches!(domain.as_ref(), TirType::Var(_))
            && !types_compatible(&arg_ty, domain)
        {
            errors.push(TypecheckError {
                message: format!(
                    "function application type mismatch: argument has type {}, but function domain is {}",
                    super::format_tir_type(&arg_ty),
                    super::format_tir_type(domain),
                ),
                location: None,
            });
        }
    }
}

/// Check that set binary operations have compatible element types.
fn check_set_binop_consistency(left: &TirExpr, right: &TirExpr, errors: &mut Vec<TypecheckError>) {
    let lt = left.ty();
    let rt = right.ty();

    if let (TirType::Set(l_inner), TirType::Set(r_inner)) = (&lt, &rt) {
        if **l_inner != TirType::Dyn
            && **r_inner != TirType::Dyn
            && !matches!(l_inner.as_ref(), TirType::Var(_))
            && !matches!(r_inner.as_ref(), TirType::Var(_))
            && !types_compatible(l_inner, r_inner)
        {
            errors.push(TypecheckError {
                message: format!(
                    "set operation element type mismatch: left has {}, right has {}",
                    super::format_tir_type(l_inner),
                    super::format_tir_type(r_inner),
                ),
                location: None,
            });
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_bool_type() {
        assert_eq!(parse_type_annotation("Bool"), Some(TirType::Bool));
    }

    #[test]
    fn parse_int_type() {
        assert_eq!(parse_type_annotation("Int"), Some(TirType::Int));
    }

    #[test]
    fn parse_str_type() {
        assert_eq!(parse_type_annotation("Str"), Some(TirType::Str));
    }

    #[test]
    fn parse_set_type() {
        assert_eq!(
            parse_type_annotation("Set(Int)"),
            Some(TirType::Set(Box::new(TirType::Int))),
        );
    }

    #[test]
    fn parse_seq_type() {
        assert_eq!(
            parse_type_annotation("Seq(Bool)"),
            Some(TirType::Seq(Box::new(TirType::Bool))),
        );
    }

    #[test]
    fn parse_nested_set() {
        assert_eq!(
            parse_type_annotation("Set(Set(Int))"),
            Some(TirType::Set(Box::new(TirType::Set(Box::new(TirType::Int))))),
        );
    }

    #[test]
    fn parse_function_type() {
        assert_eq!(
            parse_type_annotation("Int -> Bool"),
            Some(TirType::Func(
                Box::new(TirType::Int),
                Box::new(TirType::Bool)
            )),
        );
    }

    #[test]
    fn parse_function_type_with_set() {
        assert_eq!(
            parse_type_annotation("Int -> Set(Int)"),
            Some(TirType::Func(
                Box::new(TirType::Int),
                Box::new(TirType::Set(Box::new(TirType::Int)))
            )),
        );
    }

    #[test]
    fn parse_parenthesized_function() {
        assert_eq!(
            parse_type_annotation("(Int -> Bool)"),
            Some(TirType::Func(
                Box::new(TirType::Int),
                Box::new(TirType::Bool)
            )),
        );
    }

    #[test]
    fn parse_tuple_type() {
        assert_eq!(
            parse_type_annotation("<<Int, Bool>>"),
            Some(TirType::Tuple(vec![TirType::Int, TirType::Bool])),
        );
    }

    #[test]
    fn parse_record_type() {
        let ty = parse_type_annotation("[x: Int, y: Bool]");
        assert!(ty.is_some());
        if let Some(TirType::Record(fields)) = ty {
            assert_eq!(fields.len(), 2);
        } else {
            panic!("expected Record type");
        }
    }

    #[test]
    fn parse_type_variable_as_var() {
        // Apalache type variables like `a` should map to TirType::Var
        assert_eq!(parse_type_annotation("a"), Some(TirType::Var(0)));
    }

    #[test]
    fn parse_polymorphic_function() {
        // `a -> b` should parse as Var(0) -> Var(1)
        assert_eq!(
            parse_type_annotation("a -> b"),
            Some(TirType::Func(
                Box::new(TirType::Var(0)),
                Box::new(TirType::Var(1))
            )),
        );
    }

    #[test]
    fn parse_same_type_var_reused() {
        // `a -> a` should use the same variable id for both occurrences
        assert_eq!(
            parse_type_annotation("a -> a"),
            Some(TirType::Func(
                Box::new(TirType::Var(0)),
                Box::new(TirType::Var(0))
            )),
        );
    }

    #[test]
    fn parse_empty_returns_none() {
        assert_eq!(parse_type_annotation(""), None);
    }

    #[test]
    fn parse_garbage_returns_none() {
        assert_eq!(parse_type_annotation("!!!"), None);
    }

    #[test]
    fn types_compatible_dyn_wildcard() {
        assert!(types_compatible(&TirType::Dyn, &TirType::Int));
        assert!(types_compatible(&TirType::Bool, &TirType::Dyn));
    }

    #[test]
    fn types_compatible_same() {
        assert!(types_compatible(&TirType::Int, &TirType::Int));
        assert!(types_compatible(&TirType::Bool, &TirType::Bool));
    }

    #[test]
    fn types_incompatible_different() {
        assert!(!types_compatible(&TirType::Int, &TirType::Bool));
        assert!(!types_compatible(&TirType::Str, &TirType::Int));
    }

    #[test]
    fn types_compatible_nested_set() {
        assert!(types_compatible(
            &TirType::Set(Box::new(TirType::Int)),
            &TirType::Set(Box::new(TirType::Int)),
        ));
        assert!(!types_compatible(
            &TirType::Set(Box::new(TirType::Int)),
            &TirType::Set(Box::new(TirType::Bool)),
        ));
    }

    #[test]
    fn types_compatible_func_with_dyn_range() {
        assert!(types_compatible(
            &TirType::Func(Box::new(TirType::Int), Box::new(TirType::Dyn)),
            &TirType::Func(Box::new(TirType::Int), Box::new(TirType::Bool)),
        ));
    }

    #[test]
    fn parse_apalache_operator_annotation() {
        // `Set(a) => a` is the Apalache operator type syntax using =>
        // We don't support => directly, but we handle -> for function types
        // This tests that simple annotations parse correctly
        let ty = parse_type_annotation("Set(Int) -> Int");
        assert_eq!(
            ty,
            Some(TirType::Func(
                Box::new(TirType::Set(Box::new(TirType::Int))),
                Box::new(TirType::Int),
            )),
        );
    }

    // --- New tests for expanded type inference depth ---

    #[test]
    fn parse_apalache_fat_arrow_operator() {
        // Apalache uses `=>` for operator types: `(Int, Bool) => Str`
        let ty = parse_type_annotation("Int => Bool");
        assert_eq!(
            ty,
            Some(TirType::Func(
                Box::new(TirType::Int),
                Box::new(TirType::Bool),
            )),
        );
    }

    #[test]
    fn parse_apalache_multi_arg_operator() {
        // (Int, Bool) => Str
        let ty = parse_type_annotation("(Int, Bool) => Str");
        assert_eq!(
            ty,
            Some(TirType::Func(
                Box::new(TirType::Tuple(vec![TirType::Int, TirType::Bool])),
                Box::new(TirType::Str),
            )),
        );
    }

    #[test]
    fn parse_apalache_set_to_elem() {
        // Set(a) => a is the common Apalache pattern (polymorphic)
        // Both `a` occurrences should map to the same Var id.
        let ty = parse_type_annotation("Set(a) => a");
        assert_eq!(
            ty,
            Some(TirType::Func(
                Box::new(TirType::Set(Box::new(TirType::Var(0)))),
                Box::new(TirType::Var(0)),
            )),
        );
    }

    #[test]
    fn parse_nested_function_type() {
        // Int -> (Bool -> Str) — right-associative arrow
        let ty = parse_type_annotation("Int -> Bool -> Str");
        assert_eq!(
            ty,
            Some(TirType::Func(
                Box::new(TirType::Int),
                Box::new(TirType::Func(
                    Box::new(TirType::Bool),
                    Box::new(TirType::Str),
                )),
            )),
        );
    }

    #[test]
    fn parse_deeply_nested_set() {
        // Set(Set(Set(Int)))
        let ty = parse_type_annotation("Set(Set(Set(Int)))");
        assert_eq!(
            ty,
            Some(TirType::Set(Box::new(TirType::Set(Box::new(
                TirType::Set(Box::new(TirType::Int))
            ))))),
        );
    }

    #[test]
    fn parse_set_of_tuple() {
        // Set(<<Int, Bool>>)
        let ty = parse_type_annotation("Set(<<Int, Bool>>)");
        assert_eq!(
            ty,
            Some(TirType::Set(Box::new(TirType::Tuple(vec![
                TirType::Int,
                TirType::Bool
            ])))),
        );
    }

    #[test]
    fn parse_seq_of_record() {
        // Seq([x: Int, y: Bool])
        let ty = parse_type_annotation("Seq([x: Int, y: Bool])");
        assert!(ty.is_some());
        if let Some(TirType::Seq(inner)) = &ty {
            if let TirType::Record(fields) = inner.as_ref() {
                assert_eq!(fields.len(), 2);
            } else {
                panic!("expected Record inside Seq");
            }
        } else {
            panic!("expected Seq type");
        }
    }

    #[test]
    fn parse_function_type_set_domain_range() {
        // Set(Int) -> Set(Bool)
        let ty = parse_type_annotation("Set(Int) -> Set(Bool)");
        assert_eq!(
            ty,
            Some(TirType::Func(
                Box::new(TirType::Set(Box::new(TirType::Int))),
                Box::new(TirType::Set(Box::new(TirType::Bool))),
            )),
        );
    }

    #[test]
    fn parse_boolean_constant_type() {
        // BOOLEAN = Set(Bool) in Apalache
        let ty = parse_type_annotation("BOOLEAN");
        assert_eq!(ty, Some(TirType::Set(Box::new(TirType::Bool))));
    }

    #[test]
    fn parse_string_constant_type() {
        // STRING = Set(Str) in Apalache
        let ty = parse_type_annotation("STRING");
        assert_eq!(ty, Some(TirType::Set(Box::new(TirType::Str))));
    }

    #[test]
    fn types_compatible_record_with_dyn_fields() {
        let id_x = tla_core::intern_name("x");
        let id_y = tla_core::intern_name("y");
        let r1 = TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Dyn)]);
        let r2 = TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Bool)]);
        // Dyn field should be compatible with any concrete field
        assert!(types_compatible(&r1, &r2));
    }

    #[test]
    fn types_compatible_nested_record_in_set() {
        let id_x = tla_core::intern_name("x");
        let r1 = TirType::Set(Box::new(TirType::Record(vec![(id_x, TirType::Int)])));
        let r2 = TirType::Set(Box::new(TirType::Record(vec![(id_x, TirType::Int)])));
        assert!(types_compatible(&r1, &r2));
    }

    #[test]
    fn types_compatible_func_of_records() {
        let id_x = tla_core::intern_name("x");
        let f1 = TirType::Func(
            Box::new(TirType::Record(vec![(id_x, TirType::Int)])),
            Box::new(TirType::Bool),
        );
        let f2 = TirType::Func(
            Box::new(TirType::Record(vec![(id_x, TirType::Dyn)])),
            Box::new(TirType::Bool),
        );
        assert!(types_compatible(&f1, &f2));
    }

    // --- Variant type parsing ---

    #[test]
    fn parse_variant_type() {
        let ty = parse_type_annotation("Some(Int) | None(Bool)");
        assert_eq!(
            ty,
            Some(TirType::Variant(vec![
                ("Some".to_string(), TirType::Int),
                ("None".to_string(), TirType::Bool),
            ]))
        );
    }

    #[test]
    fn parse_variant_with_type_vars() {
        let ty = parse_type_annotation("Just(a) | Nothing(Bool)");
        assert_eq!(
            ty,
            Some(TirType::Variant(vec![
                ("Just".to_string(), TirType::Var(0)),
                ("Nothing".to_string(), TirType::Bool),
            ]))
        );
    }

    // --- Open record parsing ---

    #[test]
    fn parse_open_record() {
        let ty = parse_type_annotation("[x: Int, ...r]");
        assert!(ty.is_some());
        if let Some(TirType::OpenRecord(fields, row)) = &ty {
            assert_eq!(fields.len(), 1);
            assert_eq!(row, &0); // first type variable allocated
        } else {
            panic!("expected OpenRecord, got {:?}", ty);
        }
    }

    // --- Var-based type variable compatibility ---

    #[test]
    fn types_compatible_var_is_wildcard() {
        assert!(types_compatible(&TirType::Var(0), &TirType::Int));
        assert!(types_compatible(&TirType::Bool, &TirType::Var(1)));
        assert!(types_compatible(&TirType::Var(0), &TirType::Var(1)));
    }

    #[test]
    fn types_compatible_open_record_with_closed() {
        let id_x = tla_core::intern_name("x");
        let id_y = tla_core::intern_name("y");
        let open = TirType::OpenRecord(vec![(id_x, TirType::Int)], 0);
        let closed = TirType::Record(vec![(id_x, TirType::Int), (id_y, TirType::Bool)]);
        // Open record should be compatible: its known fields match.
        assert!(types_compatible(&open, &closed));
    }

    #[test]
    fn types_compatible_variant() {
        let v1 = TirType::Variant(vec![
            ("A".to_string(), TirType::Int),
            ("B".to_string(), TirType::Bool),
        ]);
        let v2 = TirType::Variant(vec![
            ("A".to_string(), TirType::Int),
            ("B".to_string(), TirType::Bool),
        ]);
        assert!(types_compatible(&v1, &v2));
    }

    #[test]
    fn types_incompatible_variant_different_tags() {
        let v1 = TirType::Variant(vec![("A".to_string(), TirType::Int)]);
        let v2 = TirType::Variant(vec![("B".to_string(), TirType::Int)]);
        assert!(!types_compatible(&v1, &v2));
    }
}
