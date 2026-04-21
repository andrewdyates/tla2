// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String and regex operations.

use std::hash::Hash;

use z4_dpll::api::Term;

use super::expect_result;
use crate::TranslationHost;

/// String binary predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrPredicate {
    Contains,
    PrefixOf,
    SuffixOf,
}

/// String concatenation.
pub fn concat<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_concat(a, b), "string.concat")
}

/// String length, returning Int.
pub fn len<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_len(s), "string.len")
}

/// Character at index, returning a length-1 String.
pub fn at<V>(ctx: &mut impl TranslationHost<V>, s: Term, idx: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_at(s, idx), "string.at")
}

/// Substring extraction.
pub fn substr<V>(ctx: &mut impl TranslationHost<V>, s: Term, offset: Term, len: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_substr(s, offset, len), "string.substr")
}

/// String predicate (contains, prefixof, suffixof).
pub fn predicate<V>(ctx: &mut impl TranslationHost<V>, pred: StrPredicate, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    match pred {
        StrPredicate::Contains => expect_result(
            ctx.solver().try_str_contains(a, b),
            "string.predicate.contains",
        ),
        StrPredicate::PrefixOf => expect_result(
            ctx.solver().try_str_prefixof(a, b),
            "string.predicate.prefixof",
        ),
        StrPredicate::SuffixOf => expect_result(
            ctx.solver().try_str_suffixof(a, b),
            "string.predicate.suffixof",
        ),
    }
}

/// String index-of, returning Int (-1 if not found).
pub fn indexof<V>(ctx: &mut impl TranslationHost<V>, s: Term, t: Term, start: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_indexof(s, t, start), "string.indexof")
}

/// String replacement (first occurrence).
pub fn replace<V>(ctx: &mut impl TranslationHost<V>, s: Term, from: Term, to: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_replace(s, from, to), "string.replace")
}

/// String replace-all.
pub fn replace_all<V>(ctx: &mut impl TranslationHost<V>, s: Term, from: Term, to: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_str_replace_all(s, from, to),
        "string.replace_all",
    )
}

/// String to integer conversion.
pub fn to_int<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_to_int(s), "string.to_int")
}

/// Integer to string conversion.
pub fn from_int<V>(ctx: &mut impl TranslationHost<V>, n: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_from_int(n), "string.from_int")
}

/// String to regex conversion.
pub fn to_re<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_to_re(s), "string.to_re")
}

/// Regex membership test.
pub fn in_re<V>(ctx: &mut impl TranslationHost<V>, s: Term, re: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_str_in_re(s, re), "string.in_re")
}

/// Kleene star of a regex.
pub fn re_star<V>(ctx: &mut impl TranslationHost<V>, re: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_re_star(re), "string.re_star")
}

/// Kleene plus of a regex.
pub fn re_plus<V>(ctx: &mut impl TranslationHost<V>, re: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_re_plus(re), "string.re_plus")
}

/// Union of two regexes.
pub fn re_union<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_re_union(a, b), "string.re_union")
}

/// Concatenation of two regexes.
pub fn re_concat<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_re_concat(a, b), "string.re_concat")
}

/// String constant.
pub fn string_const<V>(ctx: &mut impl TranslationHost<V>, value: &str) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().string_const(value)
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "string_tests.rs"]
mod tests;
