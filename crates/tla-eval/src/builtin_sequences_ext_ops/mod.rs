// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SequencesExt module operators — constructors, search, and combinatorial operations.
//!
//! Split into child modules by operation family (#3442):
//! - `search`: SelectInSeq, SelectLastInSeq + shared index-selection helper
//! - `constructors`: Prefixes, Suffixes, BoundedSeq/SeqOf, TupleOf, Indices
//! - `mutation`: InsertAt, RemoveAt, ReplaceAt, Remove, ReplaceAll
//! - `combinatorial`: Interleave, SubSeqs, SetToSeqs, AllSubSeqs

mod combinatorial;
mod constructors;
mod mutation;
mod search;

use super::{
    check_arity, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};

pub(super) fn eval_builtin_sequences_ext_ops(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    if let Some(v) = search::eval_search_ops(ctx, name, args, span)? {
        return Ok(Some(v));
    }
    if let Some(v) = constructors::eval_constructor_ops(ctx, name, args, span)? {
        return Ok(Some(v));
    }
    if let Some(v) = mutation::eval_mutation_ops(ctx, name, args, span)? {
        return Ok(Some(v));
    }
    if let Some(v) = combinatorial::eval_combinatorial_ops(ctx, name, args, span)? {
        return Ok(Some(v));
    }
    Ok(None)
}
