// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF Bool-atom assignment and merge helpers.

use tracing::debug;
use z4_core::term::{TermData, TermId};
use z4_core::{Sort, TheoryLit};

use crate::solver::EufSolver;
use crate::types::{EqualityReason, MergeReason};

impl EufSolver<'_> {
    pub(crate) fn record_assignment(&mut self, term: TermId, value: bool) {
        let debug = self.debug_euf;
        match self.assigns.get(&term).copied() {
            Some(prev) if prev == value => {
                if debug {
                    safe_eprintln!(
                        "[EUF] record_assignment: term {} = {} (unchanged)",
                        term.0,
                        value
                    );
                }
            }
            Some(prev) => {
                if debug {
                    safe_eprintln!(
                        "[EUF] record_assignment: CONFLICT term {} was {} now {}",
                        term.0,
                        prev,
                        value
                    );
                }
                self.pending_conflict = Some(term);
            }
            None => {
                self.trail.push((term, None));
                self.assigns.insert(term, value);
                self.dirty = true;

                if value {
                    self.try_track_func_app_value(term);
                }

                if value {
                    if let Some((lhs, rhs)) = self.decode_eq(term) {
                        if self.terms.sort(lhs) == self.terms.sort(rhs) {
                            if !self.enodes_init {
                                self.init_enodes();
                            }
                            self.ensure_enodes_size(lhs.0);
                            self.ensure_enodes_size(rhs.0);

                            let lhs_root = self.enode_find_const(lhs.0);
                            let rhs_root = self.enode_find_const(rhs.0);
                            if lhs_root != rhs_root {
                                self.to_merge.push_back(MergeReason {
                                    a: lhs.0,
                                    b: rhs.0,
                                    reason: EqualityReason::Direct(term),
                                });

                                if debug {
                                    safe_eprintln!(
                                        "[EUF] record_assignment: eq term {} (terms {} == {}) queued for merge",
                                        term.0, lhs.0, rhs.0
                                    );
                                }
                            }

                            if lhs != rhs && !self.propagated_eqs.contains(&term) {
                                self.propagated_eqs.insert(term);
                                let reason = vec![TheoryLit::new(term, true)];
                                self.queue_pending_propagation(
                                    lhs,
                                    rhs,
                                    reason,
                                    "asserted equality",
                                );
                            }
                        }
                    }
                }

                if debug && self.decode_eq(term).is_some() {
                    safe_eprintln!(
                        "[EUF] record_assignment: eq term {} = {} (NEW, dirty=true, total_assigns={})",
                        term.0,
                        value,
                        self.assigns.len()
                    );
                }
            }
        }
    }

    /// Incremental-mode variant of merge_bool_valued_atoms.
    /// Queues BoolValue merges into to_merge for incremental_propagate(). (#4610)
    pub(crate) fn incremental_merge_bool_valued_atoms(&mut self) -> usize {
        let mut true_rep: Option<u32> = None;
        let mut false_rep: Option<u32> = None;
        let mut queued = 0usize;

        let mut bool_assigns: Vec<(u32, bool)> = self
            .assigns
            .iter()
            .filter_map(|(&term, &val)| {
                if self.terms.sort(term) != &Sort::Bool {
                    return None;
                }
                match self.terms.get(term) {
                    TermData::Var(_, _) => Some((term.0, val)),
                    TermData::App(sym, _) if !Self::is_builtin_symbol(sym) => Some((term.0, val)),
                    _ => None,
                }
            })
            .collect();
        bool_assigns.sort_unstable();

        for (term_id, val) in bool_assigns {
            let rep = if val { &mut true_rep } else { &mut false_rep };
            if let Some(existing_rep) = *rep {
                if self.enode_find_const(term_id) != self.enode_find_const(existing_rep) {
                    self.to_merge.push_back(MergeReason {
                        a: term_id,
                        b: existing_rep,
                        reason: EqualityReason::BoolValue {
                            term: TermId(term_id),
                            value: val,
                        },
                    });
                    queued += 1;
                }
            } else {
                *rep = Some(term_id);
            }
        }

        if queued > 0 {
            debug!(
                target: "z4::euf",
                queued,
                "EUF Bool-value merges queued for incremental closure"
            );
        }

        queued
    }
}
