// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quint IR JSON deserialization types.
//!
//! These types mirror the Quint compiler's JSON IR output format.
//! Reference: <https://github.com/informalsystems/quint>
//!
//! The Quint IR uses a tagged-union style where expression nodes have a `kind`
//! field that determines the remaining fields. We model this with serde's
//! `tag = "kind"` attribute.
//!
//! Many fields (e.g., `id`, `qualifier`) are deserialized to accept full Quint
//! IR but not used during AST translation. Dead-code warnings are suppressed
//! at the module level.

use serde::Deserialize;

/// Deserialize an integer value that may be encoded as a JSON number or string.
/// Quint uses BigInt internally and may emit large integers as strings in JSON.
fn deserialize_int_value<'de, D>(deserializer: D) -> Result<i64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    use serde::de;

    struct IntVisitor;
    impl<'de> de::Visitor<'de> for IntVisitor {
        type Value = i64;

        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            formatter.write_str("an integer (number or string)")
        }

        fn visit_i64<E: de::Error>(self, v: i64) -> Result<i64, E> {
            Ok(v)
        }

        fn visit_u64<E: de::Error>(self, v: u64) -> Result<i64, E> {
            i64::try_from(v).map_err(|_| E::custom(format!("integer {v} out of i64 range")))
        }

        fn visit_str<E: de::Error>(self, v: &str) -> Result<i64, E> {
            v.parse::<i64>()
                .map_err(|_| E::custom(format!("cannot parse {v:?} as i64")))
        }
    }

    deserializer.deserialize_any(IntVisitor)
}

/// Top-level Quint IR container: a list of modules.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintIr {
    pub modules: Vec<QuintModule>,
}

/// A Quint module with its declarations.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintModule {
    pub name: String,
    pub declarations: Vec<QuintDeclaration>,
    /// Unique Quint node identifier.
    #[serde(default)]
    pub id: u64,
}

/// A top-level declaration in a Quint module.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind")]
pub(crate) enum QuintDeclaration {
    /// Operator/value definition: `val x = ...`, `def foo(a) = ...`,
    /// `action step = ...`, `temporal prop = ...`.
    #[serde(rename = "def")]
    Def(QuintDef),

    /// Variable declaration: `var x: Int`.
    #[serde(rename = "var")]
    Var(QuintVar),

    /// Constant declaration: `const N: Int`.
    #[serde(rename = "const")]
    Const(QuintConst),

    /// Type alias: `type Foo = Int`.
    #[serde(rename = "typedef")]
    TypeDef(QuintTypeDef),

    /// Assume: `assume N > 0`.
    #[serde(rename = "assume")]
    Assume(QuintAssume),

    /// Instance: `import M(N = 3) as I`.
    #[serde(rename = "instance")]
    Instance(QuintInstance),

    /// Import: `import M`.
    #[serde(rename = "import")]
    Import(QuintImport),

    /// Export: `export M`.
    #[serde(rename = "export")]
    Export(QuintExport),
}

/// A definition (operator, value, action, temporal).
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintDef {
    pub name: String,
    /// Qualifier: `val`, `def`, `action`, `temporal`, `pureval`, `puredef`,
    /// `nondet`, or `run`.
    #[serde(default)]
    pub qualifier: String,
    pub expr: Box<QuintExpr>,
    /// Parameters for operator definitions (`def foo(a, b) = ...`).
    #[serde(default)]
    pub params: Vec<QuintParam>,
    #[serde(default)]
    pub id: u64,
}

/// A variable declaration.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintVar {
    pub name: String,
    #[serde(default)]
    pub id: u64,
}

/// A constant declaration.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintConst {
    pub name: String,
    #[serde(default)]
    pub id: u64,
}

/// A type alias (we mostly ignore these during AST translation).
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintTypeDef {
    pub name: String,
    #[serde(default)]
    pub id: u64,
}

/// An assumption.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintAssume {
    pub name: String,
    pub assumption: QuintExpr,
    #[serde(default)]
    pub id: u64,
}

/// An instance declaration.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintInstance {
    #[serde(default)]
    pub name: String,
    #[serde(rename = "protoName", default)]
    pub proto_name: String,
    #[serde(default)]
    pub overrides: Vec<(String, QuintExpr)>,
    #[serde(default)]
    pub id: u64,
}

/// An import declaration.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintImport {
    #[serde(rename = "protoName", default)]
    pub proto_name: String,
    #[serde(default)]
    pub id: u64,
}

/// An export declaration.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintExport {
    #[serde(rename = "protoName", default)]
    pub proto_name: String,
    #[serde(default)]
    pub id: u64,
}

/// A parameter in a definition.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintParam {
    pub name: String,
    #[serde(default)]
    pub id: u64,
}

/// A Quint expression node. Tagged union on `kind`.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind")]
pub(crate) enum QuintExpr {
    /// Boolean literal: `true`, `false`.
    #[serde(rename = "bool")]
    Bool(QuintBoolExpr),

    /// Integer literal: `42`.
    #[serde(rename = "int")]
    Int(QuintIntExpr),

    /// String literal: `"hello"`.
    #[serde(rename = "str")]
    Str(QuintStrExpr),

    /// Name reference: `x`, `Init`, `Next`.
    #[serde(rename = "name")]
    Name(QuintNameExpr),

    /// Application of a built-in or user-defined operator.
    #[serde(rename = "app")]
    App(QuintAppExpr),

    /// Lambda expression: `(x, y) => body`.
    #[serde(rename = "lambda")]
    Lambda(QuintLambdaExpr),

    /// Let-in expression: `val x = e1 { e2 }`.
    #[serde(rename = "let")]
    Let(QuintLetExpr),
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintBoolExpr {
    pub value: bool,
    #[serde(default)]
    pub id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintIntExpr {
    #[serde(deserialize_with = "deserialize_int_value")]
    pub value: i64,
    #[serde(default)]
    pub id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintStrExpr {
    pub value: String,
    #[serde(default)]
    pub id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintNameExpr {
    pub name: String,
    #[serde(default)]
    pub id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintAppExpr {
    pub opcode: String,
    pub args: Vec<QuintExpr>,
    #[serde(default)]
    pub id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintLambdaExpr {
    pub params: Vec<QuintParam>,
    pub expr: Box<QuintExpr>,
    #[serde(default)]
    pub qualifier: String,
    #[serde(default)]
    pub id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct QuintLetExpr {
    pub opdef: Box<QuintDef>,
    pub expr: Box<QuintExpr>,
    #[serde(default)]
    pub id: u64,
}
