// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence operations.

use std::hash::Hash;

use z4_dpll::api::{Sort, Term};

use super::expect_result;
use crate::TranslationHost;

/// Sequence predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeqPredicate {
    Contains,
    PrefixOf,
    SuffixOf,
}

/// Empty sequence constant for the given element sort.
pub fn empty<V>(ctx: &mut impl TranslationHost<V>, element_sort: Sort) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().seq_empty(element_sort)
}

/// Unit sequence containing a single element.
pub fn unit<V>(ctx: &mut impl TranslationHost<V>, elem: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_seq_unit(elem), "seq.unit")
}

/// Sequence concatenation.
pub fn concat<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_seq_concat(a, b), "seq.concat")
}

/// Sequence length, returning Int.
pub fn len<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_seq_len(s), "seq.len")
}

/// Element at index, returning the element sort.
pub fn nth<V>(ctx: &mut impl TranslationHost<V>, s: Term, idx: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_seq_nth(s, idx), "seq.nth")
}

/// Subsequence extraction.
pub fn extract<V>(ctx: &mut impl TranslationHost<V>, s: Term, offset: Term, len: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_seq_extract(s, offset, len), "seq.extract")
}

/// Sequence predicate (contains, prefixof, suffixof).
pub fn predicate<V>(ctx: &mut impl TranslationHost<V>, pred: SeqPredicate, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    match pred {
        SeqPredicate::Contains => expect_result(
            ctx.solver().try_seq_contains(a, b),
            "seq.predicate.contains",
        ),
        SeqPredicate::PrefixOf => expect_result(
            ctx.solver().try_seq_prefixof(a, b),
            "seq.predicate.prefixof",
        ),
        SeqPredicate::SuffixOf => expect_result(
            ctx.solver().try_seq_suffixof(a, b),
            "seq.predicate.suffixof",
        ),
    }
}

/// Sequence index-of, returning Int (-1 if not found).
pub fn indexof<V>(ctx: &mut impl TranslationHost<V>, s: Term, t: Term, start: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_seq_indexof(s, t, start), "seq.indexof")
}

/// Sequence replacement (first occurrence).
pub fn replace<V>(ctx: &mut impl TranslationHost<V>, s: Term, from: Term, to: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_seq_replace(s, from, to), "seq.replace")
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "seq_tests.rs"]
mod tests;
