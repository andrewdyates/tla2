// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Data types for SPECIFICATION formula extraction.

use tla_core::SyntaxNode;

/// Result of extracting Init/Next from a SPECIFICATION formula
#[derive(Debug, Clone)]
pub struct SpecFormula {
    /// Name of the Init predicate
    pub init: String,
    /// Name of the Next relation (may be a simple name or an inline expression text)
    pub next: String,
    /// The syntax node for the Next relation when it's an inline expression
    /// (e.g., `\E n \in Node: Next(n)` instead of just `Next`)
    pub next_node: Option<SyntaxNode>,
    /// Variables expression (if found)
    pub vars: Option<String>,
    /// Fairness constraints (if any)
    pub fairness: Vec<FairnessConstraint>,
    /// Whether the spec uses `[A]_v` form (stuttering allowed) or `<<A>>_v` form
    /// (stuttering forbidden).
    ///
    /// This captures the temporal formula's next-step semantics only. TLA2 and
    /// TLC still decide whether to report no-successor states via
    /// `CHECK_DEADLOCK` / CLI flags rather than this field alone.
    /// Defaults to `true` (stuttering allowed), the most common TLA+ pattern.
    pub stuttering_allowed: bool,
}

/// A fairness constraint
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum FairnessConstraint {
    /// Weak fairness: WF_vars(Action)
    Weak {
        vars: String,
        action: String,
        /// The action expression's syntax node (for inline expressions)
        action_node: Option<SyntaxNode>,
    },
    /// Strong fairness: SF_vars(Action)
    Strong {
        vars: String,
        action: String,
        /// The action expression's syntax node (for inline expressions)
        action_node: Option<SyntaxNode>,
    },
    /// Temporal formula reference (for complex fairness like \A p: WF_vars(Action(p)))
    /// The named operator's body will be converted to LiveExpr during liveness checking.
    TemporalRef {
        /// Name of the operator containing the temporal formula
        op_name: String,
    },
    /// Inline quantified temporal formula (for complex fairness in spec bodies)
    /// This handles cases like `\A c \in Clients: WF_vars(Action(c))` that appear
    /// directly in the spec body rather than in a separate operator.
    QuantifiedTemporal {
        /// The syntax node containing the quantified temporal formula
        node: SyntaxNode,
    },
}

/// Conjunct in a temporal formula
#[derive(Debug)]
pub(super) enum Conjunct {
    /// An identifier (like Init)
    Ident(String),
    /// A node to analyze further
    Node(SyntaxNode),
}

/// Result of extracting an action from a subscript expression
pub(super) struct ActionExtraction {
    /// The action name or expression text
    pub name: String,
    /// The syntax node for inline expressions (None for simple identifiers)
    pub node: Option<SyntaxNode>,
    /// The vars expression
    pub vars: String,
    /// Whether stuttering is allowed (`[A]_v` = true) or forbidden (`<<A>>_v` = false).
    /// `[A]_v` uses FuncSetExpr (square brackets), `<<A>>_v` uses TupleExpr (angle brackets).
    pub stuttering_allowed: bool,
}
