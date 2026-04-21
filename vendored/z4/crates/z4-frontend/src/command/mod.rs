// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB commands
//!
//! Represents and parses SMT-LIB 2.6 commands.

mod datatype;
mod term;

pub use datatype::{ConstructorDec, DatatypeDec, SelectorDec, SortDec};
pub use term::{Constant, Term};

use crate::sexp::{ParseError, SExpr};

/// An SMT-LIB sort
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Sort {
    /// A simple sort (Bool, Int, Real, etc.)
    Simple(String),
    /// A parameterized sort (Array Int Int, BitVec 32, etc.)
    Parameterized(String, Vec<Self>),
    /// An indexed sort (_ BitVec 32)
    Indexed(String, Vec<String>),
}

impl Sort {
    /// Parse a sort from an S-expression
    pub fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        match sexp {
            SExpr::Symbol(name) => Ok(Self::Simple(name.clone())),
            SExpr::List(items) if !items.is_empty() => {
                // Check for indexed identifier (_ name index+)
                if items[0].is_symbol("_") && items.len() >= 2 {
                    let name = items[1]
                        .as_symbol()
                        .ok_or_else(|| ParseError::new("Expected symbol in indexed sort"))?;
                    let indices: Result<Vec<_>, _> = items[2..]
                        .iter()
                        .map(|s| match s {
                            SExpr::Numeral(n) => Ok(n.clone()),
                            SExpr::Symbol(s) => Ok(s.clone()),
                            _ => Err(ParseError::new(
                                "Expected numeral or symbol in indexed sort",
                            )),
                        })
                        .collect();
                    Ok(Self::Indexed(name.to_string(), indices?))
                } else {
                    // Parameterized sort
                    let name = items[0]
                        .as_symbol()
                        .ok_or_else(|| ParseError::new("Expected symbol as sort constructor"))?;
                    let params: Result<Vec<_>, _> =
                        items[1..].iter().map(Self::from_sexp).collect();
                    Ok(Self::Parameterized(name.to_string(), params?))
                }
            }
            _ => Err(ParseError::new(format!("Invalid sort: {sexp}"))),
        }
    }
}

/// A function declaration: (name, parameters, return sort)
/// Used in define-funs-rec for mutually recursive function definitions.
pub(crate) type FuncDeclaration = (String, Vec<(String, Sort)>, Sort);

/// An SMT-LIB command
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum Command {
    /// `(set-logic <symbol>)`
    SetLogic(String),
    /// `(set-option <keyword> <value>)`
    SetOption(String, SExpr),
    /// `(set-info <keyword> <value>)`
    SetInfo(String, SExpr),
    /// `(declare-sort <symbol> <numeral>)`
    DeclareSort(String, u32),
    /// `(define-sort <symbol> (<symbol>*) <sort>)`
    DefineSort(String, Vec<String>, Sort),
    /// `(declare-datatype <symbol> <datatype_dec>)`
    DeclareDatatype(String, DatatypeDec),
    /// `(declare-datatypes (<sort_dec>+) (<datatype_dec>+))`
    DeclareDatatypes(Vec<SortDec>, Vec<DatatypeDec>),
    /// `(declare-fun <symbol> (<sort>*) <sort>)`
    DeclareFun(String, Vec<Sort>, Sort),
    /// `(declare-const <symbol> <sort>)`
    DeclareConst(String, Sort),
    /// `(define-fun <symbol> (<sorted_var>*) <sort> <term>)`
    DefineFun(String, Vec<(String, Sort)>, Sort, Term),
    /// `(define-fun-rec <symbol> (<sorted_var>*) <sort> <term>)`
    DefineFunRec(String, Vec<(String, Sort)>, Sort, Term),
    /// `(define-funs-rec (<func_dec>+) (<term>+))`
    /// where `func_dec = (<symbol> (<sorted_var>*) <sort>)`
    DefineFunsRec(Vec<FuncDeclaration>, Vec<Term>),
    /// `(assert <term>)`
    Assert(Term),
    /// `(maximize <term>)` - Z3 optimization extension
    Maximize(Term),
    /// `(minimize <term>)` - Z3 optimization extension
    Minimize(Term),
    /// `(check-sat)`
    CheckSat,
    /// `(check-sat-assuming (<literal>*))`
    CheckSatAssuming(Vec<Term>),
    /// `(get-model)`
    GetModel,
    /// `(get-objectives)` - Z3 optimization extension
    GetObjectives,
    /// `(get-value (<term>+))`
    GetValue(Vec<Term>),
    /// `(get-unsat-core)`
    GetUnsatCore,
    /// `(get-unsat-assumptions)`
    GetUnsatAssumptions,
    /// `(get-proof)`
    GetProof,
    /// `(get-assertions)`
    GetAssertions,
    /// `(get-assignment)`
    GetAssignment,
    /// `(get-info <keyword>)`
    GetInfo(String),
    /// `(get-option <keyword>)`
    GetOption(String),
    /// `(push <numeral>)`
    Push(u32),
    /// `(pop <numeral>)`
    Pop(u32),
    /// `(reset)`
    Reset,
    /// `(reset-assertions)`
    ResetAssertions,
    /// `(exit)`
    Exit,
    /// `(echo <string>)`
    Echo(String),
    /// `(simplify <term>)` - Z3 extension
    Simplify(Term),
}

impl Command {
    /// Parse a command from an S-expression
    pub fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("Command must be a list"))?;

        if items.is_empty() {
            return Err(ParseError::new("Empty command"));
        }

        let cmd = items[0]
            .as_symbol()
            .ok_or_else(|| ParseError::new("Command name must be a symbol"))?;

        match cmd {
            "set-logic" => {
                let logic = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("set-logic requires logic name"))?;
                Ok(Self::SetLogic(logic.to_string()))
            }
            "set-option" => {
                if items.len() < 3 {
                    return Err(ParseError::new("set-option requires keyword and value"));
                }
                let keyword = match &items[1] {
                    SExpr::Keyword(k) => k.clone(),
                    _ => return Err(ParseError::new("set-option requires keyword")),
                };
                Ok(Self::SetOption(keyword, items[2].clone()))
            }
            "set-info" => {
                if items.len() < 3 {
                    return Err(ParseError::new("set-info requires keyword and value"));
                }
                let keyword = match &items[1] {
                    SExpr::Keyword(k) => k.clone(),
                    _ => return Err(ParseError::new("set-info requires keyword")),
                };
                Ok(Self::SetInfo(keyword, items[2].clone()))
            }
            "declare-sort" => {
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-sort requires name"))?;
                let arity = items
                    .get(2)
                    .and_then(|s| s.as_numeral())
                    .and_then(|n| n.parse::<u32>().ok())
                    .unwrap_or(0);
                Ok(Self::DeclareSort(name.to_string(), arity))
            }
            "define-sort" => {
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("define-sort requires name"))?;
                let params = items
                    .get(2)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("define-sort requires parameter list"))?;
                let param_names: Result<Vec<_>, _> = params
                    .iter()
                    .map(|p| {
                        p.as_symbol()
                            .map(String::from)
                            .ok_or_else(|| ParseError::new("sort parameter must be symbol"))
                    })
                    .collect();
                let sort = items
                    .get(3)
                    .ok_or_else(|| ParseError::new("define-sort requires sort definition"))?;
                Ok(Self::DefineSort(
                    name.to_string(),
                    param_names?,
                    Sort::from_sexp(sort)?,
                ))
            }
            "declare-datatype" => {
                // (declare-datatype name datatype_dec)
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-datatype requires name"))?;
                let datatype_dec = items.get(2).ok_or_else(|| {
                    ParseError::new("declare-datatype requires datatype declaration")
                })?;
                Ok(Self::DeclareDatatype(
                    name.to_string(),
                    DatatypeDec::from_sexp(datatype_dec)?,
                ))
            }
            "declare-datatypes" => {
                // (declare-datatypes ((name1 arity1) ...) (datatype_dec1 ...))
                let sort_decs = items.get(1).and_then(|s| s.as_list()).ok_or_else(|| {
                    ParseError::new("declare-datatypes requires sort declarations")
                })?;
                let datatype_decs = items.get(2).and_then(|s| s.as_list()).ok_or_else(|| {
                    ParseError::new("declare-datatypes requires datatype declarations")
                })?;

                if sort_decs.len() != datatype_decs.len() {
                    return Err(ParseError::new(
                        "declare-datatypes: number of sort declarations must match datatype declarations",
                    ));
                }

                let sorts: Result<Vec<_>, _> = sort_decs.iter().map(SortDec::from_sexp).collect();
                let datatypes: Result<Vec<_>, _> =
                    datatype_decs.iter().map(DatatypeDec::from_sexp).collect();

                Ok(Self::DeclareDatatypes(sorts?, datatypes?))
            }
            "declare-fun" => {
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-fun requires name"))?;
                let args = items
                    .get(2)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("declare-fun requires argument sorts"))?;
                let arg_sorts: Result<Vec<_>, _> = args.iter().map(Sort::from_sexp).collect();
                let ret = items
                    .get(3)
                    .ok_or_else(|| ParseError::new("declare-fun requires return sort"))?;
                Ok(Self::DeclareFun(
                    name.to_string(),
                    arg_sorts?,
                    Sort::from_sexp(ret)?,
                ))
            }
            "declare-const" => {
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-const requires name"))?;
                let sort = items
                    .get(2)
                    .ok_or_else(|| ParseError::new("declare-const requires sort"))?;
                Ok(Self::DeclareConst(name.to_string(), Sort::from_sexp(sort)?))
            }
            "define-fun" => Self::parse_define_fun(items),
            "define-fun-rec" => Self::parse_define_fun_rec(items),
            "define-funs-rec" => Self::parse_define_funs_rec(items),
            "assert" => {
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("assert requires term"))?;
                Ok(Self::Assert(Term::from_sexp(term)?))
            }
            "maximize" => {
                if items.len() != 2 {
                    return Err(ParseError::new("maximize requires exactly one term"));
                }
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("maximize requires term"))?;
                Ok(Self::Maximize(Term::from_sexp(term)?))
            }
            "minimize" => {
                if items.len() != 2 {
                    return Err(ParseError::new("minimize requires exactly one term"));
                }
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("minimize requires term"))?;
                Ok(Self::Minimize(Term::from_sexp(term)?))
            }
            "check-sat" => Ok(Self::CheckSat),
            "check-sat-assuming" => {
                let lits = items
                    .get(1)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("check-sat-assuming requires literal list"))?;
                let terms: Result<Vec<_>, _> = lits.iter().map(Term::from_sexp).collect();
                Ok(Self::CheckSatAssuming(terms?))
            }
            "get-model" => Ok(Self::GetModel),
            "get-objectives" => Ok(Self::GetObjectives),
            "get-value" => {
                let terms = items
                    .get(1)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("get-value requires term list"))?;
                let parsed: Result<Vec<_>, _> = terms.iter().map(Term::from_sexp).collect();
                Ok(Self::GetValue(parsed?))
            }
            "get-unsat-core" => Ok(Self::GetUnsatCore),
            "get-unsat-assumptions" => Ok(Self::GetUnsatAssumptions),
            "get-proof" => Ok(Self::GetProof),
            "get-assertions" => Ok(Self::GetAssertions),
            "get-assignment" => Ok(Self::GetAssignment),
            "get-info" => {
                let keyword = match items.get(1) {
                    Some(SExpr::Keyword(k)) => k.clone(),
                    _ => return Err(ParseError::new("get-info requires keyword")),
                };
                Ok(Self::GetInfo(keyword))
            }
            "get-option" => {
                let keyword = match items.get(1) {
                    Some(SExpr::Keyword(k)) => k.clone(),
                    _ => return Err(ParseError::new("get-option requires keyword")),
                };
                Ok(Self::GetOption(keyword))
            }
            "push" => {
                let n = items
                    .get(1)
                    .and_then(|s| s.as_numeral())
                    .and_then(|n| n.parse::<u32>().ok())
                    .unwrap_or(1);
                Ok(Self::Push(n))
            }
            "pop" => {
                let n = items
                    .get(1)
                    .and_then(|s| s.as_numeral())
                    .and_then(|n| n.parse::<u32>().ok())
                    .unwrap_or(1);
                Ok(Self::Pop(n))
            }
            "reset" => Ok(Self::Reset),
            "reset-assertions" => Ok(Self::ResetAssertions),
            "exit" => Ok(Self::Exit),
            "echo" => {
                let msg = match items.get(1) {
                    Some(SExpr::String(s)) => s.clone(),
                    _ => return Err(ParseError::new("echo requires string")),
                };
                Ok(Self::Echo(msg))
            }
            "simplify" => {
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("simplify requires term"))?;
                Ok(Self::Simplify(Term::from_sexp(term)?))
            }
            _ => Err(ParseError::new(format!("Unknown command: {cmd}"))),
        }
    }

    fn parse_define_fun(items: &[SExpr]) -> Result<Self, ParseError> {
        let name = items
            .get(1)
            .and_then(|s| s.as_symbol())
            .ok_or_else(|| ParseError::new("define-fun requires name"))?;
        let sorted_vars = Self::parse_sorted_var_list(items.get(2), "define-fun")?;
        let ret_sort = items
            .get(3)
            .ok_or_else(|| ParseError::new("define-fun requires return sort"))?;
        let body = items
            .get(4)
            .ok_or_else(|| ParseError::new("define-fun requires body"))?;
        Ok(Self::DefineFun(
            name.to_string(),
            sorted_vars,
            Sort::from_sexp(ret_sort)?,
            Term::from_sexp(body)?,
        ))
    }

    fn parse_define_fun_rec(items: &[SExpr]) -> Result<Self, ParseError> {
        let name = items
            .get(1)
            .and_then(|s| s.as_symbol())
            .ok_or_else(|| ParseError::new("define-fun-rec requires name"))?;
        let sorted_vars = Self::parse_sorted_var_list(items.get(2), "define-fun-rec")?;
        let ret_sort = items
            .get(3)
            .ok_or_else(|| ParseError::new("define-fun-rec requires return sort"))?;
        let body = items
            .get(4)
            .ok_or_else(|| ParseError::new("define-fun-rec requires body"))?;
        Ok(Self::DefineFunRec(
            name.to_string(),
            sorted_vars,
            Sort::from_sexp(ret_sort)?,
            Term::from_sexp(body)?,
        ))
    }

    fn parse_define_funs_rec(items: &[SExpr]) -> Result<Self, ParseError> {
        // (define-funs-rec ((f1 ((x T)) T) (f2 ((y T)) T)) (body1 body2))
        let func_decs = items
            .get(1)
            .and_then(|s| s.as_list())
            .ok_or_else(|| ParseError::new("define-funs-rec requires function declarations"))?;
        let bodies = items
            .get(2)
            .and_then(|s| s.as_list())
            .ok_or_else(|| ParseError::new("define-funs-rec requires function bodies"))?;

        if func_decs.len() != bodies.len() {
            return Err(ParseError::new(
                "define-funs-rec: number of declarations must match number of bodies",
            ));
        }

        let mut declarations = Vec::new();
        for func_dec in func_decs {
            let dec_list = func_dec
                .as_list()
                .ok_or_else(|| ParseError::new("function declaration must be a list"))?;
            if dec_list.len() != 3 {
                return Err(ParseError::new(
                    "function declaration must be (name ((param sort)*) sort)",
                ));
            }
            let name = dec_list[0]
                .as_symbol()
                .ok_or_else(|| ParseError::new("function name must be symbol"))?;
            let sorted_vars =
                Self::parse_sorted_var_list(Some(&dec_list[1]), "define-funs-rec parameter")?;
            let ret_sort = Sort::from_sexp(&dec_list[2])?;
            declarations.push((name.to_string(), sorted_vars, ret_sort));
        }

        let parsed_bodies: Result<Vec<_>, _> = bodies.iter().map(Term::from_sexp).collect();
        Ok(Self::DefineFunsRec(declarations, parsed_bodies?))
    }

    /// Parse a list of sorted variables `((name sort) ...)` from an S-expression.
    fn parse_sorted_var_list(
        sexp: Option<&SExpr>,
        context: &str,
    ) -> Result<Vec<(String, Sort)>, ParseError> {
        let params = sexp
            .and_then(|s| s.as_list())
            .ok_or_else(|| ParseError::new(format!("{context} requires parameter list")))?;
        let mut sorted_vars = Vec::new();
        for param in params {
            let param_list = param
                .as_list()
                .ok_or_else(|| ParseError::new("parameter must be (name sort)"))?;
            if param_list.len() != 2 {
                return Err(ParseError::new("parameter must be (name sort)"));
            }
            let var_name = param_list[0]
                .as_symbol()
                .ok_or_else(|| ParseError::new("parameter name must be symbol"))?;
            let var_sort = Sort::from_sexp(&param_list[1])?;
            sorted_vars.push((var_name.to_string(), var_sort));
        }
        Ok(sorted_vars)
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
