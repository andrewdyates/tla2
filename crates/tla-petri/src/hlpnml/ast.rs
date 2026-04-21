// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// A colored Petri net parsed from HLPNML.
#[derive(Debug, Clone)]
pub(crate) struct ColoredNet {
    pub name: Option<String>,
    pub sorts: Vec<ColorSort>,
    pub variables: Vec<VariableDecl>,
    pub places: Vec<ColoredPlace>,
    pub transitions: Vec<ColoredTransition>,
    pub arcs: Vec<ColoredArc>,
}

/// A color sort definition.
#[derive(Debug, Clone)]
pub(crate) enum ColorSort {
    /// The singleton dot sort.
    Dot { id: String, name: String },
    /// Cyclic enumeration: ordered constants with wraparound.
    CyclicEnum {
        id: String,
        name: String,
        constants: Vec<ColorConstant>,
    },
    /// Cartesian product of component sorts.
    Product {
        id: String,
        name: String,
        components: Vec<String>,
    },
}

impl ColorSort {
    pub(crate) fn id(&self) -> &str {
        match self {
            ColorSort::Dot { id, .. }
            | ColorSort::CyclicEnum { id, .. }
            | ColorSort::Product { id, .. } => id,
        }
    }

    pub(crate) fn name(&self) -> &str {
        match self {
            ColorSort::Dot { name, .. }
            | ColorSort::CyclicEnum { name, .. }
            | ColorSort::Product { name, .. } => name,
        }
    }
}

/// A named constant in a cyclic enumeration.
#[derive(Debug, Clone)]
pub(crate) struct ColorConstant {
    pub id: String,
    pub name: String,
}

/// A variable declaration bound to a sort.
#[derive(Debug, Clone)]
pub(crate) struct VariableDecl {
    pub id: String,
    #[cfg_attr(not(test), allow(dead_code))]
    pub name: String,
    pub sort_id: String,
}

/// A colored place with type and optional initial marking.
#[derive(Debug, Clone)]
pub(crate) struct ColoredPlace {
    pub id: String,
    pub name: Option<String>,
    pub sort_id: String,
    pub initial_marking: Option<ColorExpr>,
}

/// A colored transition with optional guard.
#[derive(Debug, Clone)]
pub(crate) struct ColoredTransition {
    pub id: String,
    pub name: Option<String>,
    pub guard: Option<GuardExpr>,
}

/// A colored arc with inscription expression.
#[derive(Debug, Clone)]
pub(crate) struct ColoredArc {
    #[cfg_attr(not(test), allow(dead_code))]
    pub id: String,
    pub source: String,
    pub target: String,
    pub inscription: ColorExpr,
}

/// A multiset expression (arc inscription or initial marking).
#[derive(Debug, Clone)]
pub(crate) enum ColorExpr {
    /// `<all><usersort .../></all>` — all colors of a sort.
    All { sort_id: String },
    /// `<numberof>` — multiplicity `count` of a color term.
    NumberOf { count: u64, color: Box<ColorTerm> },
    /// `<add>` — multiset union.
    Add(Vec<ColorExpr>),
}

/// A single-color term (resolves to one color value per binding).
#[derive(Debug, Clone)]
pub(crate) enum ColorTerm {
    /// `<variable refvariable="..."/>` — bound variable.
    Variable(String),
    /// `<tuple>` — product-sort value from component terms.
    Tuple(Vec<ColorTerm>),
    /// `<predecessor>` — cyclic predecessor.
    Predecessor(Box<ColorTerm>),
    /// `<successor>` — cyclic successor.
    Successor(Box<ColorTerm>),
    /// `<useroperator declaration="..."/>` — named constant.
    UserConstant(String),
    /// `<dotconstant/>` — the single dot value.
    DotConstant,
}

/// A guard expression on a transition.
#[derive(Debug, Clone)]
pub(crate) enum GuardExpr {
    And(Vec<GuardExpr>),
    Or(Vec<GuardExpr>),
    Not(Box<GuardExpr>),
    Equality(Box<ColorTerm>, Box<ColorTerm>),
    Inequality(Box<ColorTerm>, Box<ColorTerm>),
    LessThan(Box<ColorTerm>, Box<ColorTerm>),
    LessThanOrEqual(Box<ColorTerm>, Box<ColorTerm>),
    GreaterThan(Box<ColorTerm>, Box<ColorTerm>),
    GreaterThanOrEqual(Box<ColorTerm>, Box<ColorTerm>),
    True,
}
