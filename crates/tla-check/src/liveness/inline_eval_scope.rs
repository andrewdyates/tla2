// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

/// Single-source boundary for inline liveness evaluation.
///
/// Inline leaf recording shares the model checker's evaluator caches with BFS.
/// `#3118` showed that this path needs the stronger evaluation-scope cleanup,
/// not the lighter state-only clear. Centralize that decision here so future
/// inline-liveness work does not reintroduce a raw cache-clear call at the
/// recording site.
///
/// Part of #3792: Uses `clear_for_inline_liveness_boundary()` instead of
/// `clear_for_eval_scope_boundary()`. The inline liveness boundary preserves
/// the persistent partitions of ZERO_ARG_OP_CACHE and NARY_OP_CACHE — entries
/// with empty deps that are truly state-independent. This prevents catastrophic
/// re-evaluation of constant operators like SpanTreeRandom's `Edges` (which
/// calls RandomElement(SUBSET ...) taking O(2^n) per evaluation). Previously,
/// the full eval-scope clear wiped persistent entries after every liveness
/// batch, forcing re-evaluation for each of the 87K BFS states.
#[must_use]
pub(crate) struct InlineEvalScope {
    finished: bool,
}

impl InlineEvalScope {
    pub(crate) fn new() -> Self {
        Self { finished: false }
    }

    pub(crate) fn finish(mut self) {
        clear_inline_eval_boundary();
        self.finished = true;
    }
}

impl Drop for InlineEvalScope {
    fn drop(&mut self) {
        if !self.finished {
            clear_inline_eval_boundary();
        }
    }
}

fn clear_inline_eval_boundary() {
    // Part of #3792: Preserve persistent cache partitions across inline liveness
    // boundaries. Persistent entries (empty deps, no instance_lazy_read) are truly
    // constant — they don't depend on which BFS state triggered the evaluation.
    // The previous `clear_for_eval_scope_boundary()` wiped them, causing O(states)
    // re-evaluation of constant operators like SpanTreeRandom's `Edges`.
    crate::eval::clear_for_inline_liveness_boundary();
}
