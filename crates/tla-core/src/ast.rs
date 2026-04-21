// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Abstract Syntax Tree for TLA+
//!
//! This module defines the AST types used by all TLA2 tools.
//! The AST is designed to be:
//! - Complete: represents all TLA+ constructs
//! - Span-aware: every node has source location info
//! - Immutable: suitable for caching and sharing

use crate::name_intern::NameId;
use crate::span::{Span, Spanned};
use num_bigint::BigInt;
use std::collections::HashSet;

/// A TLA+ module
#[derive(Debug, Clone)]
pub struct Module {
    /// Module name
    pub name: Spanned<String>,
    /// Extended modules
    pub extends: Vec<Spanned<String>>,
    /// Module body units
    pub units: Vec<Spanned<Unit>>,
    /// Spans for lowered action subscript bodies that originated from `[A]_v` / `<<A>>_v`
    /// syntax rather than an explicitly written expanded form like `A \/ UNCHANGED v`.
    pub action_subscript_spans: HashSet<Span>,
    /// Full span of the module
    pub span: Span,
}

/// A unit in a module (top-level declaration or definition)
#[derive(Debug, Clone)]
pub enum Unit {
    /// VARIABLE x, y, z
    Variable(Vec<Spanned<String>>),

    /// CONSTANT c1, c2
    Constant(Vec<ConstantDecl>),

    /// RECURSIVE Op(_, _) - forward declaration for recursive operators
    Recursive(Vec<RecursiveDecl>),

    /// Operator definition: Op(x, y) == body
    Operator(OperatorDef),

    /// INSTANCE Module WITH substitutions
    Instance(InstanceDecl),

    /// ASSUME expression (optionally named: ASSUME Name == expr)
    Assume(AssumeDecl),

    /// THEOREM name == body (with optional proof)
    Theorem(TheoremDecl),

    /// Separator line (-----)
    Separator,
}

/// A constant declaration (may have a declared type/constraint)
#[derive(Debug, Clone)]
pub struct ConstantDecl {
    pub name: Spanned<String>,
    /// Optional arity for operator constants
    pub arity: Option<usize>,
}

/// An ASSUME declaration (optionally named)
#[derive(Debug, Clone)]
pub struct AssumeDecl {
    /// Optional name for the assume (ASSUME Name == expr)
    pub name: Option<Spanned<String>>,
    /// The assumed expression
    pub expr: Spanned<Expr>,
}

/// A recursive operator forward declaration: RECURSIVE Op(_, _)
#[derive(Debug, Clone)]
pub struct RecursiveDecl {
    pub name: Spanned<String>,
    /// Arity (number of parameters) declared by underscores
    pub arity: usize,
}

/// An operator definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperatorDef {
    pub name: Spanned<String>,
    pub params: Vec<OpParam>,
    pub body: Spanned<Expr>,
    pub local: bool,
    /// True if the operator body (transitively) contains any primed variables.
    /// Used to determine if prime bindings are needed before evaluating this operator.
    /// Computed by `compute_contains_prime` after parsing.
    pub contains_prime: bool,
    pub guards_depend_on_prime: bool,
    /// True if any parameter name appears primed in the operator body.
    /// When true, operator application must use call-by-name (expression substitution)
    /// instead of call-by-value to preserve TLA+ priming semantics.
    /// Computed by `compute_has_primed_param` after parsing. See #2662.
    pub has_primed_param: bool,
    /// True if this operator was declared with RECURSIVE.
    /// Recursive operators change arguments at each level, making per-call cache
    /// hits structurally impossible. Used for cache bypass optimizations (#3008).
    /// Computed by `compute_is_recursive` after parsing. See #2944.
    pub is_recursive: bool,
    /// Number of self-references in the operator body (#3008 Option B).
    /// count=1: single self-call, bypass cache (100% miss). count>1: double+
    /// self-call, keep cache (same-depth memoization O(2^n)→O(n)).
    /// Computed by `compute_is_recursive`. Only meaningful when `is_recursive=true`.
    pub self_call_count: u32,
}

/// An operator parameter (may be higher-order)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpParam {
    pub name: Spanned<String>,
    /// Arity > 0 means this is an operator parameter
    pub arity: usize,
}

/// An INSTANCE declaration
#[derive(Debug, Clone)]
pub struct InstanceDecl {
    pub module: Spanned<String>,
    pub substitutions: Vec<Substitution>,
    pub local: bool,
}

/// A substitution in INSTANCE ... WITH
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Substitution {
    pub from: Spanned<String>,
    pub to: Spanned<Expr>,
}

/// A theorem declaration
#[derive(Debug, Clone)]
pub struct TheoremDecl {
    pub name: Option<Spanned<String>>,
    pub body: Spanned<Expr>,
    pub proof: Option<Spanned<Proof>>,
}

/// A proof structure
#[derive(Debug, Clone)]
pub enum Proof {
    /// BY hints
    By(Vec<ProofHint>),
    /// OBVIOUS
    Obvious,
    /// OMITTED
    Omitted,
    /// Structured proof with steps
    Steps(Vec<ProofStep>),
}

/// A hint in a BY clause
#[derive(Debug, Clone)]
pub enum ProofHint {
    /// Reference to a fact/theorem
    Ref(Spanned<String>),
    /// DEF names
    Def(Vec<Spanned<String>>),
    /// Module reference
    Module(Spanned<String>),
}

/// A step in a structured proof
#[derive(Debug, Clone)]
pub struct ProofStep {
    pub level: usize,
    pub label: Option<Spanned<String>>,
    pub kind: ProofStepKind,
}

/// The kind of proof step
#[derive(Debug, Clone)]
pub enum ProofStepKind {
    /// `<n>`. assertion
    Assert(Spanned<Expr>, Option<Spanned<Proof>>),
    /// SUFFICES assertion
    Suffices(Spanned<Expr>, Option<Spanned<Proof>>),
    /// HAVE assertion
    Have(Spanned<Expr>),
    /// TAKE x \in S
    Take(Vec<BoundVar>),
    /// WITNESS expression
    Witness(Vec<Spanned<Expr>>),
    /// PICK x \in S : P
    Pick(Vec<BoundVar>, Spanned<Expr>, Option<Spanned<Proof>>),
    /// USE/HIDE
    UseOrHide { use_: bool, facts: Vec<ProofHint> },
    /// DEFINE definitions
    Define(Vec<OperatorDef>),
    /// QED
    Qed(Option<Spanned<Proof>>),
}

/// Target module for module reference expressions (M!Op)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleTarget {
    /// Simple module/instance name: M!Op
    Named(String),
    /// Parameterized instance call: IS(x, y)!Op
    /// Used when an operator is defined as: IS(x, y) == INSTANCE Inner
    Parameterized(String, Vec<Spanned<Expr>>),
    /// Chained module reference: A!B!C!D where the target is itself a ModuleRef
    /// The boxed expression is the base module reference (e.g., A!B!C in A!B!C!D)
    Chained(Box<Spanned<Expr>>),
}

impl ModuleTarget {
    /// Get the name of the module/instance (for simple or parameterized targets)
    /// For chained targets, this returns `<chained>` as the name isn't directly available
    pub fn name(&self) -> &str {
        match self {
            ModuleTarget::Named(n) => n,
            ModuleTarget::Parameterized(n, _) => n,
            ModuleTarget::Chained(_) => "<chained>",
        }
    }
}

impl std::fmt::Display for ModuleTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModuleTarget::Named(name) => write!(f, "{name}"),
            ModuleTarget::Parameterized(name, _) => write!(f, "{name}(...)"),
            ModuleTarget::Chained(base) => write!(f, "{:?}!", base.node),
        }
    }
}

/// A labeled subexpression: `P0:: expr`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprLabel {
    pub name: Spanned<String>,
    pub body: Box<Spanned<Expr>>,
}

/// TLA+ expressions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    // === Literals ===
    /// TRUE or FALSE
    Bool(bool),
    /// Integer literal
    Int(BigInt),
    /// String literal
    String(String),

    // === Names ===
    /// Identifier reference with pre-resolved NameId for O(1) lookup (Part of #2993)
    ///
    /// Contains (identifier_name, name_id). The name is kept for error messages.
    /// The NameId is pre-resolved during a lowering pass; `NameId::INVALID` means
    /// not yet resolved (e.g., during parsing or test construction).
    Ident(String, NameId),
    /// Pre-resolved state variable for O(1) lookup (Part of #188, #232)
    ///
    /// Contains (variable_name, state_array_index, name_id). The name is kept for error messages
    /// and debugging; the u16 index enables direct array access without HashMap lookup.
    /// The NameId enables O(1) shadowing checks (no HashMap lookup at evaluation time).
    ///
    /// This variant is created by an AST transformation pass after parsing, NOT by the parser.
    /// It only applies to state variables (declared in VARIABLES), not operators or constants.
    StateVar(String, u16, NameId),

    // === Operators ===
    /// Operator application: Op(args)
    Apply(Box<Spanned<Expr>>, Vec<Spanned<Expr>>),
    /// Operator reference (bare operator as value): +, -, *, \cup, etc.
    /// Used for higher-order operators like FoldFunctionOnSet(+, 0, f, S)
    OpRef(String),
    /// Module/Instance reference: M!Op or M!Op(args)
    /// Module target can be simple name (M!Op) or parameterized (IS(x,y)!Op)
    ModuleRef(ModuleTarget, String, Vec<Spanned<Expr>>),
    /// Named instance expression: INSTANCE Module WITH x <- e, ...
    /// Used in: InChan == INSTANCE Channel WITH Data <- Message, chan <- in
    InstanceExpr(String, Vec<Substitution>),
    /// Lambda: LAMBDA x, y : body
    Lambda(Vec<Spanned<String>>, Box<Spanned<Expr>>),
    /// Labeled subexpression: P0:: expr
    Label(ExprLabel),

    // === Logic ===
    /// Conjunction: A /\ B
    And(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Disjunction: A \/ B
    Or(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Negation: ~A
    Not(Box<Spanned<Expr>>),
    /// Implication: A => B
    Implies(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Equivalence: A <=> B
    Equiv(Box<Spanned<Expr>>, Box<Spanned<Expr>>),

    // === Quantifiers ===
    /// Universal: \A x \in S : P
    Forall(Vec<BoundVar>, Box<Spanned<Expr>>),
    /// Existential: \E x \in S : P
    Exists(Vec<BoundVar>, Box<Spanned<Expr>>),
    /// Choice: CHOOSE x \in S : P
    Choose(BoundVar, Box<Spanned<Expr>>),

    // === Sets ===
    /// Set enumeration: {a, b, c}
    SetEnum(Vec<Spanned<Expr>>),
    /// Set builder: {expr : x \in S, y \in T}
    SetBuilder(Box<Spanned<Expr>>, Vec<BoundVar>),
    /// Set filter: {x \in S : P}
    SetFilter(BoundVar, Box<Spanned<Expr>>),
    /// Membership: x \in S
    In(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Non-membership: x \notin S
    NotIn(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Subset: S \subseteq T
    Subseteq(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Union: S \cup T
    Union(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Intersection: S \cap T
    Intersect(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Set difference: S \ T
    SetMinus(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Powerset: SUBSET S
    Powerset(Box<Spanned<Expr>>),
    /// Big union: UNION S
    BigUnion(Box<Spanned<Expr>>),

    // === Functions ===
    /// Function definition: [x \in S |-> expr]
    FuncDef(Vec<BoundVar>, Box<Spanned<Expr>>),
    /// Function application: `f[x]`
    FuncApply(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Domain: DOMAIN f
    Domain(Box<Spanned<Expr>>),
    /// EXCEPT: [f EXCEPT ![a] = b]
    Except(Box<Spanned<Expr>>, Vec<ExceptSpec>),
    /// Function set: [S -> T]
    FuncSet(Box<Spanned<Expr>>, Box<Spanned<Expr>>),

    // === Records ===
    /// Record constructor: [a |-> 1, b |-> 2]
    Record(Vec<(Spanned<String>, Spanned<Expr>)>),
    /// Record field access: r.field
    RecordAccess(Box<Spanned<Expr>>, RecordFieldName),
    /// Record set: [a : S, b : T]
    RecordSet(Vec<(Spanned<String>, Spanned<Expr>)>),

    // === Tuples and Sequences ===
    /// Tuple: <<a, b, c>>
    Tuple(Vec<Spanned<Expr>>),
    /// Cartesian product: S \X T
    Times(Vec<Spanned<Expr>>),

    // === Temporal ===
    /// Prime: x'
    Prime(Box<Spanned<Expr>>),
    /// Always: []P
    Always(Box<Spanned<Expr>>),
    /// Eventually: <>P
    Eventually(Box<Spanned<Expr>>),
    /// Leads-to: P ~> Q
    LeadsTo(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Weak fairness: WF_vars(A)
    WeakFair(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Strong fairness: SF_vars(A)
    StrongFair(Box<Spanned<Expr>>, Box<Spanned<Expr>>),

    // === Actions ===
    /// ENABLED A
    Enabled(Box<Spanned<Expr>>),
    /// UNCHANGED <<x, y>>
    Unchanged(Box<Spanned<Expr>>),

    // === Control ===
    /// IF cond THEN a ELSE b
    If(Box<Spanned<Expr>>, Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// CASE arms [] OTHER -> default
    Case(Vec<CaseArm>, Option<Box<Spanned<Expr>>>),
    /// LET defs IN body
    Let(Vec<OperatorDef>, Box<Spanned<Expr>>),
    /// SubstIn: deferred INSTANCE substitution wrapper (TLC SubstInNode parity).
    /// Instead of eagerly rewriting the AST via apply_substitutions(),
    /// wraps the body with its substitutions for evaluation-time resolution.
    /// Part of #3056.
    SubstIn(Vec<Substitution>, Box<Spanned<Expr>>),

    // === Comparison ===
    /// Equality: a = b
    Eq(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Inequality: a /= b
    Neq(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Less than: a < b
    Lt(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Less or equal: a <= b
    Leq(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Greater than: a > b
    Gt(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Greater or equal: a >= b
    Geq(Box<Spanned<Expr>>, Box<Spanned<Expr>>),

    // === Arithmetic ===
    /// Addition: a + b
    Add(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Subtraction: a - b
    Sub(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Multiplication: a * b
    Mul(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Division: a / b
    Div(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Integer division: a \div b
    IntDiv(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Modulo: a % b
    Mod(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Exponentiation: a^b
    Pow(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    /// Unary minus: -a
    Neg(Box<Spanned<Expr>>),
    /// Range: a..b
    Range(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
}

/// A bound variable pattern
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoundPattern {
    /// Simple variable: x
    Var(Spanned<String>),
    /// Tuple pattern: <<x, y>>
    Tuple(Vec<Spanned<String>>),
}

/// A bound variable with optional domain
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundVar {
    pub name: Spanned<String>,
    /// Domain: x \in S
    pub domain: Option<Box<Spanned<Expr>>>,
    /// Pattern for destructuring (None means simple binding to `name`)
    pub pattern: Option<BoundPattern>,
}

/// A case arm in a CASE expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseArm {
    pub guard: Spanned<Expr>,
    pub body: Spanned<Expr>,
}

/// An EXCEPT specification: ![index] = value
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExceptSpec {
    pub path: Vec<ExceptPathElement>,
    pub value: Spanned<Expr>,
}

/// An element in an EXCEPT path
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExceptPathElement {
    /// Array index: `[i]`
    Index(Spanned<Expr>),
    /// Record field: .field
    Field(RecordFieldName),
}

/// A record field name with a pre-interned NameId for O(1) runtime lookup.
///
/// Stores both the original string (for error messages and pretty-printing)
/// and the interned NameId (for O(1) comparison at evaluation time).
/// Part of #3168: eliminates runtime `intern_name()` calls in the evaluator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordFieldName {
    pub name: Spanned<String>,
    pub field_id: NameId,
}

impl RecordFieldName {
    /// Create a new `RecordFieldName`, interning the name at construction time.
    pub fn new(name: Spanned<String>) -> Self {
        let field_id = crate::intern_name(&name.node);
        Self { name, field_id }
    }
}

impl From<Spanned<String>> for RecordFieldName {
    fn from(name: Spanned<String>) -> Self {
        Self::new(name)
    }
}
