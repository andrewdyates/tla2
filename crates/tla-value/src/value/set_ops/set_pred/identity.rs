// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SetPred identity contract: canonical identity types, ordering, hashing,
//! fingerprinting, and trait implementations.
//!
//! This module owns the structural identity rules that must stay in lockstep
//! across `Ord`, `Hash`, and `fingerprint_extend`. The runtime object and
//! its accessors live in `value.rs`.

use super::super::super::value_fingerprint::{fp_usize_to_i32, FingerprintResult};
use super::super::super::*;
use super::value::SetPredValue;
use crate::fingerprint::fp64_extend_i64;

#[inline]
fn cmp_optional_value_slices(lhs: Option<&[Value]>, rhs: Option<&[Value]>) -> Ordering {
    match (lhs, rhs) {
        (Some(a), Some(b)) => a.iter().cmp(b.iter()),
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    }
}

#[inline]
fn hash_optional_value_slice<H: Hasher>(values: Option<&[Value]>, state: &mut H) {
    match values {
        Some(values) => {
            true.hash(state);
            values.len().hash(state);
            for value in values {
                value.hash(state);
            }
        }
        None => false.hash(state),
    }
}

/// Canonical SetPred identity fields shared across ordering and hashing paths.
///
/// The iteration order in this struct is the single source of truth for SetPred
/// structural identity. All SetPred comparison/hash/fingerprint paths must
/// consume this representation to avoid drift.
pub struct SetPredIdentity<'a> {
    pub(crate) source: &'a Value,
    /// Part of #2955: Replaced String with u64 hash for ~12% speedup.
    pub(crate) bound_sig: u64,
    /// Part of #2955: Replaced String with u64 hash for ~12% speedup.
    pub(crate) pred_sig: u64,
    pub(crate) env_entries: Vec<(&'a Arc<str>, &'a Value)>,
    pub(crate) captured_state: Option<&'a [Value]>,
    pub(crate) captured_next_state: Option<&'a [Value]>,
}

/// Visitor contract for consuming SetPred identity fields in canonical order.
pub trait SetPredIdentityVisitor {
    fn visit_source(&mut self, source: &Value);
    fn visit_bound_sig(&mut self, bound_sig: u64);
    fn visit_pred_sig(&mut self, pred_sig: u64);
    fn visit_env_len(&mut self, len: usize);
    fn visit_env_entry(&mut self, name: &str, value: &Value);
    fn visit_captured_state(&mut self, captured_state: Option<&[Value]>);
    fn visit_captured_next_state(&mut self, captured_next_state: Option<&[Value]>);
}

impl SetPredValue {
    /// Build canonical SetPred identity fields for ordering/hashing/fingerprinting.
    pub(crate) fn identity_fields(&self) -> SetPredIdentity<'_> {
        let env = self.env();
        let mut env_entries: Vec<_> = env.iter().collect();
        env_entries.sort_by(|(lhs_name, _), (rhs_name, _)| lhs_name.cmp(rhs_name));

        SetPredIdentity {
            source: &self.source,
            bound_sig: self.cached_bound_sig,
            pred_sig: self.cached_pred_sig,
            env_entries,
            captured_state: self.captured_state.as_deref(),
            captured_next_state: self.captured_next_state.as_deref(),
        }
    }

    /// Visit SetPred identity fields in canonical order.
    pub fn visit_identity_fields<V: SetPredIdentityVisitor>(&self, visitor: &mut V) {
        let SetPredIdentity {
            source,
            bound_sig,
            pred_sig,
            env_entries,
            captured_state,
            captured_next_state,
        } = self.identity_fields();

        visitor.visit_source(source);
        visitor.visit_bound_sig(bound_sig);
        visitor.visit_pred_sig(pred_sig);
        visitor.visit_env_len(env_entries.len());
        for (name, value) in env_entries {
            visitor.visit_env_entry(name, value);
        }
        visitor.visit_captured_state(captured_state);
        visitor.visit_captured_next_state(captured_next_state);
    }

    /// Extend an FP64 fingerprint with deterministic SetPred structure.
    /// Consumes `identity_fields()` directly — same field order as the visitor path.
    pub(crate) fn structural_fingerprint_extend(&self, fp: u64) -> FingerprintResult<u64> {
        use crate::fingerprint::{fp64_extend_i32, fp64_extend_str};
        let id = self.identity_fields();
        let mut fp = id.source.fingerprint_extend(fp)?;
        fp = fp64_extend_i64(fp, id.bound_sig as i64);
        fp = fp64_extend_i64(fp, id.pred_sig as i64);
        fp = fp64_extend_i32(
            fp,
            fp_usize_to_i32(id.env_entries.len(), "SetPred env size")?,
        );
        for (name, value) in &id.env_entries {
            fp = fp64_extend_i32(fp, fp_usize_to_i32(name.len(), "SetPred env key length")?);
            fp = fp64_extend_str(fp, name);
            fp = value.fingerprint_extend(fp)?;
        }
        for (values, ctx) in [
            (id.captured_state, "SetPred captured_state length"),
            (id.captured_next_state, "SetPred captured_next_state length"),
        ] {
            match values {
                Some(vs) => {
                    fp = fp64_extend_i32(fp, 1);
                    fp = fp64_extend_i32(fp, fp_usize_to_i32(vs.len(), ctx)?);
                    for v in vs {
                        fp = v.fingerprint_extend(fp)?;
                    }
                }
                None => fp = fp64_extend_i32(fp, 0),
            }
        }
        Ok(fp)
    }
}

impl fmt::Debug for SetPredValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SetPred({:?}, {:?})", self.source, self.bound.name)
    }
}

impl Ord for SetPredValue {
    fn cmp(&self, other: &Self) -> Ordering {
        let a = self.identity_fields();
        let b = other.identity_fields();
        a.source
            .cmp(b.source)
            .then_with(|| a.bound_sig.cmp(&b.bound_sig))
            .then_with(|| a.pred_sig.cmp(&b.pred_sig))
            .then_with(|| a.env_entries.len().cmp(&b.env_entries.len()))
            .then_with(|| {
                for ((an, av), (bn, bv)) in a.env_entries.iter().zip(b.env_entries.iter()) {
                    match an.cmp(bn).then_with(|| av.cmp(bv)) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                Ordering::Equal
            })
            .then_with(|| cmp_optional_value_slices(a.captured_state, b.captured_state))
            .then_with(|| cmp_optional_value_slices(a.captured_next_state, b.captured_next_state))
    }
}

impl PartialOrd for SetPredValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for SetPredValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for SetPredValue {}

impl Hash for SetPredValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        struct StdHashVisitor<'a, H: Hasher> {
            state: &'a mut H,
        }
        impl<H: Hasher> SetPredIdentityVisitor for StdHashVisitor<'_, H> {
            fn visit_source(&mut self, source: &Value) {
                source.hash(self.state);
            }
            fn visit_bound_sig(&mut self, bound_sig: u64) {
                bound_sig.hash(self.state);
            }
            fn visit_pred_sig(&mut self, pred_sig: u64) {
                pred_sig.hash(self.state);
            }
            fn visit_env_len(&mut self, len: usize) {
                len.hash(self.state);
            }
            fn visit_env_entry(&mut self, name: &str, value: &Value) {
                name.hash(self.state);
                value.hash(self.state);
            }
            fn visit_captured_state(&mut self, cs: Option<&[Value]>) {
                hash_optional_value_slice(cs, self.state);
            }
            fn visit_captured_next_state(&mut self, cns: Option<&[Value]>) {
                hash_optional_value_slice(cns, self.state);
            }
        }

        "SetPred".hash(state);
        let mut visitor = StdHashVisitor { state };
        self.visit_identity_fields(&mut visitor);
    }
}
