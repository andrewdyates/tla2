// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB datatype declaration types and parsing.

use crate::sexp::{ParseError, SExpr};

use super::Sort;

/// A selector declaration in a datatype constructor: (name, sort)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SelectorDec {
    /// The selector name (accessor function)
    pub name: String,
    /// The sort of the field
    pub sort: Sort,
}

/// A constructor declaration in a datatype: (name, selectors)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorDec {
    /// The constructor name
    pub name: String,
    /// The selectors (fields) of this constructor
    pub selectors: Vec<SelectorDec>,
}

/// A datatype declaration: list of constructors
/// Note: Parametric datatypes (par ...) are not yet supported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DatatypeDec {
    /// The constructors for this datatype
    pub constructors: Vec<ConstructorDec>,
}

/// A sort declaration for declare-datatypes: (name, arity)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SortDec {
    /// The sort name
    pub name: String,
    /// The arity (0 for non-parametric sorts)
    pub arity: u32,
}

impl SelectorDec {
    /// Parse a selector declaration: (name sort)
    pub(crate) fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("selector must be a list"))?;
        if items.len() != 2 {
            return Err(ParseError::new("selector must be (name sort)"));
        }
        let name = items[0]
            .as_symbol()
            .ok_or_else(|| ParseError::new("selector name must be symbol"))?;
        let sort = Sort::from_sexp(&items[1])?;
        Ok(Self {
            name: name.to_string(),
            sort,
        })
    }
}

impl ConstructorDec {
    /// Parse a constructor declaration: (name selector*)
    pub(crate) fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("constructor must be a list"))?;
        if items.is_empty() {
            return Err(ParseError::new("constructor requires name"));
        }
        let name = items[0]
            .as_symbol()
            .ok_or_else(|| ParseError::new("constructor name must be symbol"))?;
        let selectors: Result<Vec<_>, _> = items[1..].iter().map(SelectorDec::from_sexp).collect();
        Ok(Self {
            name: name.to_string(),
            selectors: selectors?,
        })
    }
}

impl DatatypeDec {
    /// Parse a datatype declaration: (constructor+) or (par (...) (constructor+))
    pub(crate) fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("datatype declaration must be a list"))?;
        if items.is_empty() {
            return Err(ParseError::new(
                "datatype requires at least one constructor",
            ));
        }

        // Check for parametric datatype
        if items[0].is_symbol("par") {
            return Err(ParseError::new(
                "parametric datatypes (par ...) are not yet supported",
            ));
        }

        // Non-parametric: list of constructors
        let constructors: Result<Vec<_>, _> = items.iter().map(ConstructorDec::from_sexp).collect();
        Ok(Self {
            constructors: constructors?,
        })
    }
}

impl SortDec {
    /// Parse a sort declaration: (name arity)
    pub(crate) fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("sort declaration must be a list"))?;
        if items.len() != 2 {
            return Err(ParseError::new("sort declaration must be (name arity)"));
        }
        let name = items[0]
            .as_symbol()
            .ok_or_else(|| ParseError::new("sort name must be symbol"))?;
        let arity = items[1]
            .as_numeral()
            .and_then(|n| n.parse::<u32>().ok())
            .ok_or_else(|| ParseError::new("sort arity must be numeral"))?;
        Ok(Self {
            name: name.to_string(),
            arity,
        })
    }
}
