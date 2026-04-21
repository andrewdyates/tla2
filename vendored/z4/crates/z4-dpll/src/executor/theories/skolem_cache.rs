// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared skolem cache for executor-level string decompositions.
//!
//! The string pipeline has multiple decomposition paths (pre-registration and
//! runtime lemmas). This cache ensures each logical decomposition key reuses a
//! canonical skolem `TermId` instead of creating incompatible fresh variables.

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermStore;
use z4_core::{Sort, TermId};

const DUMMY: TermId = TermId(u32::MAX);

/// Decomposition kinds used in executor-level string preprocessing and lemmas.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::executor::theories) enum SkolemKind {
    ConstSplit,
    VarSplit,
    ContainsPre,
    ContainsPost,
    PrefixRemainder,
    SuffixRemainder,
    SubstrPre,
    SubstrResult,
    SubstrSuffix,
    ReplaceResult,
    ReplacePre,
    ReplaceSuffix,
}

type CacheKey = (TermId, TermId, SkolemKind, usize);

/// Canonical skolem registry for string decomposition paths.
#[derive(Debug, Default)]
pub(in crate::executor) struct ExecutorSkolemCache {
    cache: HashMap<CacheKey, TermId>,
}

impl ExecutorSkolemCache {
    pub(in crate::executor::theories) fn new() -> Self {
        Self {
            cache: HashMap::new(),
        }
    }

    fn get_or_create(
        &mut self,
        terms: &mut TermStore,
        key: CacheKey,
        prefix: &'static str,
    ) -> TermId {
        if let Some(existing) = self.cache.get(&key).copied() {
            return existing;
        }
        let fresh = terms.mk_fresh_var(prefix, Sort::String);
        self.cache.insert(key, fresh);
        fresh
    }

    fn normalized_pair(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
        if lhs <= rhs {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        }
    }

    pub(in crate::executor::theories) fn const_split(
        &mut self,
        terms: &mut TermStore,
        x: TermId,
        constant: TermId,
        char_offset: usize,
    ) -> TermId {
        self.get_or_create(
            terms,
            (x, constant, SkolemKind::ConstSplit, char_offset),
            "sk_cspt",
        )
    }

    pub(in crate::executor::theories) fn var_split(
        &mut self,
        terms: &mut TermStore,
        x: TermId,
        y: TermId,
    ) -> TermId {
        let (lhs, rhs) = Self::normalized_pair(x, y);
        self.get_or_create(terms, (lhs, rhs, SkolemKind::VarSplit, 0), "sk_vspt")
    }

    pub(in crate::executor::theories) fn contains_pre(
        &mut self,
        terms: &mut TermStore,
        haystack: TermId,
        needle: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (haystack, needle, SkolemKind::ContainsPre, 0),
            "sk_ctn_pre",
        )
    }

    pub(in crate::executor::theories) fn contains_post(
        &mut self,
        terms: &mut TermStore,
        haystack: TermId,
        needle: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (haystack, needle, SkolemKind::ContainsPost, 0),
            "sk_ctn_post",
        )
    }

    pub(in crate::executor::theories) fn prefix_remainder(
        &mut self,
        terms: &mut TermStore,
        haystack: TermId,
        pattern: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (haystack, pattern, SkolemKind::PrefixRemainder, 0),
            "sk_pfx_suf",
        )
    }

    pub(in crate::executor::theories) fn suffix_remainder(
        &mut self,
        terms: &mut TermStore,
        haystack: TermId,
        pattern: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (haystack, pattern, SkolemKind::SuffixRemainder, 0),
            "sk_sfx_pre",
        )
    }

    pub(in crate::executor::theories) fn substr_pre(
        &mut self,
        terms: &mut TermStore,
        substr_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (substr_term, DUMMY, SkolemKind::SubstrPre, 0),
            "sk_sub_pre",
        )
    }

    pub(in crate::executor::theories) fn substr_result(
        &mut self,
        terms: &mut TermStore,
        substr_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (substr_term, DUMMY, SkolemKind::SubstrResult, 0),
            "sk_sub_res",
        )
    }

    pub(in crate::executor::theories) fn substr_suffix(
        &mut self,
        terms: &mut TermStore,
        substr_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (substr_term, DUMMY, SkolemKind::SubstrSuffix, 0),
            "sk_sub_suf",
        )
    }

    pub(in crate::executor::theories) fn replace_result(
        &mut self,
        terms: &mut TermStore,
        replace_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (replace_term, DUMMY, SkolemKind::ReplaceResult, 0),
            "sk_rep_res",
        )
    }

    pub(in crate::executor::theories) fn replace_pre(
        &mut self,
        terms: &mut TermStore,
        replace_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (replace_term, DUMMY, SkolemKind::ReplacePre, 0),
            "sk_rep_pre",
        )
    }

    pub(in crate::executor::theories) fn replace_suffix(
        &mut self,
        terms: &mut TermStore,
        replace_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (replace_term, DUMMY, SkolemKind::ReplaceSuffix, 0),
            "sk_rep_suf",
        )
    }
}

#[cfg(test)]
#[path = "skolem_cache_tests.rs"]
mod tests;
