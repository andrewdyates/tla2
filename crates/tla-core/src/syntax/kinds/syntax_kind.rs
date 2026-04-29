// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SyntaxKind definitions for rowan-based parsing.
//! Defines all syntax node kinds used by the lossless syntax tree. The parser produces a CST
//! (Concrete Syntax Tree) using rowan, which preserves whitespace and comments before lowering to AST.

/// All kinds of syntax nodes and tokens
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum SyntaxKind {
    // === Special ===
    /// Root node containing the entire file
    Root,
    /// Error recovery node
    Error,
    /// Whitespace (spaces, tabs, newlines)
    Whitespace,

    // === Comments ===
    /// Line comment: \* ...
    LineComment,
    /// Block comment: (* ... *)
    BlockComment,

    // === Tokens (Leaves) ===
    /// Identifier
    Ident,
    /// Integer literal
    Number,
    /// String literal
    String,

    // === Module Structure Tokens ===
    /// ---- (module start delimiter)
    ModuleStart,
    /// ==== (module end delimiter)
    ModuleEnd,
    /// MODULE keyword
    ModuleKw,
    /// EXTENDS keyword
    ExtendsKw,
    /// INSTANCE keyword
    InstanceKw,
    /// WITH keyword
    WithKw,
    /// LOCAL keyword
    LocalKw,

    // === Declaration Tokens ===
    /// VARIABLE/VARIABLES keyword
    VariableKw,
    /// CONSTANT/CONSTANTS keyword
    ConstantKw,
    /// ASSUME/ASSUMPTION keyword
    AssumeKw,
    /// THEOREM keyword
    TheoremKw,
    /// LEMMA keyword
    LemmaKw,
    /// PROPOSITION keyword
    PropositionKw,
    /// COROLLARY keyword
    CorollaryKw,
    /// AXIOM keyword
    AxiomKw,

    // === Proof Tokens ===
    /// PROOF keyword
    ProofKw,
    /// BY keyword
    ByKw,
    /// OBVIOUS keyword
    ObviousKw,
    /// OMITTED keyword
    OmittedKw,
    /// QED keyword
    QedKw,
    /// SUFFICES keyword
    SufficesKw,
    /// HAVE keyword
    HaveKw,
    /// TAKE keyword
    TakeKw,
    /// WITNESS keyword
    WitnessKw,
    /// PICK keyword
    PickKw,
    /// USE keyword
    UseKw,
    /// HIDE keyword
    HideKw,
    /// DEFINE keyword
    DefineKw,
    /// DEFS keyword
    DefsKw,
    /// DEF keyword
    DefKw,
    /// ONLY keyword
    OnlyKw,
    /// NEW keyword
    NewKw,

    // === Logic Tokens ===
    /// TRUE keyword
    TrueKw,
    /// FALSE keyword
    FalseKw,
    /// BOOLEAN keyword
    BooleanKw,
    /// IF keyword
    IfKw,
    /// THEN keyword
    ThenKw,
    /// ELSE keyword
    ElseKw,
    /// CASE keyword
    CaseKw,
    /// OTHER keyword
    OtherKw,
    /// LET keyword
    LetKw,
    /// IN keyword
    InKw,
    /// LAMBDA keyword
    LambdaKw,

    // === Quantifier Tokens ===
    /// \A or \forall
    ForallKw,
    /// \E or \exists
    ExistsKw,
    /// CHOOSE keyword
    ChooseKw,
    /// RECURSIVE keyword
    RecursiveKw,
    /// \EE temporal existential
    TemporalExistsKw,
    /// \AA temporal universal
    TemporalForallKw,

    // === Set Operator Tokens ===
    /// \in
    InOp,
    /// \notin
    NotInOp,
    /// \cup or \union
    UnionOp,
    /// \cap or \intersect
    IntersectOp,
    /// \ or \setminus
    SetMinusOp,
    /// \subseteq
    SubseteqOp,
    /// \subset
    SubsetOp,
    /// \supseteq
    SupseteqOp,
    /// \supset
    SupsetOp,
    /// \sqsubseteq
    SqsubseteqOp,
    /// \sqsupseteq
    SqsupseteqOp,
    /// SUBSET (powerset)
    PowersetKw,
    /// UNION (big union)
    BigUnionKw,
    /// INTER (big intersection)
    BigInterKw,

    // === Temporal Operator Tokens ===
    /// []
    AlwaysOp,
    /// <>
    EventuallyOp,
    /// ~>
    LeadsToOp,
    /// ENABLED keyword
    EnabledKw,
    /// UNCHANGED keyword
    UnchangedKw,
    /// WF_
    WeakFairKw,
    /// SF_
    StrongFairKw,

    // === Logical Operator Tokens ===
    /// /\ or \land
    AndOp,
    /// \/ or \lor
    OrOp,
    /// ~ or \lnot or \neg
    NotOp,
    /// =>
    ImpliesOp,
    /// <=> or \equiv
    EquivOp,

    // === Comparison Tokens ===
    /// =
    EqOp,
    /// # or /= or \neq
    NeqOp,
    /// <
    LtOp,
    /// >
    GtOp,
    /// <= or \leq
    LeqOp,
    /// >= or \geq
    GeqOp,

    // === Ordering Relations (user-definable) ===
    /// \prec
    PrecOp,
    /// \preceq
    PreceqOp,
    /// \succ
    SuccOp,
    /// \succeq
    SucceqOp,
    /// \ll
    LlOp,
    /// \gg
    GgOp,
    /// \sim
    SimOp,
    /// \simeq
    SimeqOp,
    /// \asymp
    AsympOp,
    /// \approx
    ApproxOp,
    /// \cong
    CongOp,
    /// \doteq
    DoteqOp,
    /// \propto
    ProptoOp,
    /// \cdot (action composition)
    CdotOp,

    // === Arithmetic Tokens ===
    /// +
    PlusOp,
    /// -
    MinusOp,
    /// *
    StarOp,
    /// /
    SlashOp,
    /// ^
    CaretOp,
    /// %
    PercentOp,
    /// \div
    DivOp,
    /// ..
    DotDotOp,

    // === Multi-character User-definable Operators ===
    /// ++
    PlusPlusOp,
    /// --
    MinusMinusOp,
    /// **
    StarStarOp,
    /// //
    SlashSlashOp,
    /// ^^
    CaretCaretOp,
    /// %%
    PercentPercentOp,
    /// &&
    AmpAmpOp,
    /// \oplus
    OplusOp,
    /// \ominus
    OminusOp,
    /// \otimes
    OtimesOp,
    /// \oslash
    OslashOp,
    /// \odot
    OdotOp,
    /// \uplus
    UplusOp,
    /// \sqcap
    SqcapOp,
    /// \sqcup
    SqcupOp,

    // === Definition Tokens ===
    /// ==
    DefEqOp,
    /// ::=
    ColonColonEqOp,
    /// :=
    ColonEqOp,
    /// '
    PrimeOp,
    /// \triangleq
    TriangleEqOp,

    // === Delimiter Tokens ===
    /// (
    LParen,
    /// )
    RParen,
    /// [
    LBracket,
    /// ]
    RBracket,
    /// {
    LBrace,
    /// }
    RBrace,
    /// <<
    LAngle,
    /// >>
    RAngle,
    /// ,
    Comma,
    /// ::
    ColonColon,
    /// :
    Colon,
    /// ;
    Semi,
    /// .
    Dot,
    /// _
    Underscore,
    /// @
    At,
    /// !
    Bang,
    /// |->
    MapsTo,
    /// ->
    Arrow,
    /// <-
    LArrow,
    /// |-
    Turnstile,
    /// |
    Pipe,
    /// :>
    ColonGt,
    /// <: (Apalache type annotation operator)
    LtColonOp,
    /// @@
    AtAt,
    /// $
    Dollar,
    /// $$
    DollarDollar,
    /// ?
    Question,
    /// &
    Amp,
    /// \X or \times
    TimesOp,

    // === Function Tokens ===
    /// DOMAIN keyword
    DomainKw,
    /// EXCEPT keyword
    ExceptKw,

    // === Sequence Tokens ===
    /// Append
    AppendKw,
    /// Head
    HeadKw,
    /// Tail
    TailKw,
    /// Len
    LenKw,
    /// Seq
    SeqKw,
    /// SubSeq
    SubSeqKw,
    /// SelectSeq
    SelectSeqKw,
    /// \o or \circ
    ConcatOp,

    // === Composite Nodes ===
    /// A complete TLA+ module
    Module,
    /// EXTENDS clause: EXTENDS M1, M2
    ExtendsClause,
    /// Variable declaration: VARIABLE x, y
    VariableDecl,
    /// Constant declaration: CONSTANT c1, c2
    ConstantDecl,
    /// Operator definition: Op(x, y) == body
    OperatorDef,
    /// Operator parameter
    OperatorParam,
    /// INSTANCE declaration
    InstanceDecl,
    /// Substitution in INSTANCE: x <- y
    Substitution,
    /// ASSUME statement
    AssumeStmt,
    /// THEOREM/LEMMA/PROPOSITION/COROLLARY statement
    TheoremStmt,
    /// USE/HIDE statement (TLAPS)
    UseStmt,
    /// Separator line (-----)
    Separator,
    /// RECURSIVE declaration: RECURSIVE Op(_)
    RecursiveDecl,

    // === Proof Nodes ===
    /// A proof block
    Proof,
    /// BY clause with hints
    ByClause,
    /// A proof step
    ProofStep,
    /// Step label like <1>a
    StepLabel,

    // === Expression Nodes ===
    /// Parenthesized expression
    ParenExpr,
    /// Binary operation
    BinaryExpr,
    /// Unary operation
    UnaryExpr,
    /// Operator application: Op(args)
    ApplyExpr,
    /// Operator reference (passing operator as value): \intersect, +, etc.
    OperatorRef,
    /// Lambda expression
    LambdaExpr,
    /// Quantified expression: \A x \in S : P
    QuantExpr,
    /// CHOOSE expression
    ChooseExpr,
    /// Set enumeration: {a, b, c}
    SetEnumExpr,
    /// Set builder: {expr : x \in S}
    SetBuilderExpr,
    /// Set filter: {x \in S : P}
    SetFilterExpr,
    /// Function definition: [x \in S |-> expr]
    FuncDefExpr,
    /// Function application: `f[x]`
    FuncApplyExpr,
    /// Function set: [S -> T]
    FuncSetExpr,
    /// EXCEPT expression
    ExceptExpr,
    /// Except spec: ![a][b] = v
    ExceptSpec,
    /// Record constructor: [a |-> 1, b |-> 2]
    RecordExpr,
    /// Record field access: r.field
    RecordAccessExpr,
    /// Labeled subexpression: P0:: expr
    LabelExpr,
    /// Module reference: Module!Op or Module!Op(args)
    ModuleRefExpr,
    /// Theorem assertion reference: TheoremName!:
    TheoremRefExpr,
    /// Action subscript: `[A]_v` or `<<A>>_v`
    SubscriptExpr,
    /// Record set: [a : S, b : T]
    RecordSetExpr,
    /// Record field binding: a |-> e or a : S
    RecordField,
    /// Tuple expression: <<a, b, c>>
    TupleExpr,
    /// IF-THEN-ELSE expression
    IfExpr,
    /// CASE expression
    CaseExpr,
    /// CASE arm: cond -> expr
    CaseArm,
    /// LET-IN expression
    LetExpr,
    /// Bound variable: x \in S
    BoundVar,
    /// Tuple pattern: <<x, y>> for destructuring in quantifiers
    TuplePattern,
    /// Argument list
    ArgList,
    /// Name list (for declarations)
    NameList,

    // Sentinel for rowan
    #[doc(hidden)]
    __Last,
}
