// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String lemma clause creation: translates symbolic `StringLemma` requests into
//! concrete CNF clauses for the SAT solver.

use num_bigint::BigInt;
use z4_core::term::{Constant, Symbol, TermData};
use z4_core::{Sort, StringLemma, StringLemmaKind, TermId};

use super::super::super::Executor;
use super::super::skolem_cache::ExecutorSkolemCache;
use super::guards::{build_reason_guard, emit_guard_empty_splits};

impl Executor {
    /// Extra terms that should be marked as dynamically reduced after a string lemma.
    pub(in crate::executor) fn string_lemma_reduced_terms(
        &mut self,
        lemma: &StringLemma,
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Vec<TermId> {
        match lemma.kind {
            StringLemmaKind::SubstrReduction => {
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(lemma.x) else {
                    return Vec::new();
                };
                if name != "str.substr" || args.len() != 3 {
                    return Vec::new();
                }
                let sk_pre = skolem_cache.substr_pre(&mut self.ctx.terms, lemma.x);
                let skt = skolem_cache.substr_result(&mut self.ctx.terms, lemma.x);
                let sk_suf = skolem_cache.substr_suffix(&mut self.ctx.terms, lemma.x);
                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![sk_pre, skt, sk_suf],
                    Sort::String,
                );
                vec![lemma.x, concat]
            }
            _ => Vec::new(),
        }
    }

    /// Create clauses from a `StringLemma` request.
    ///
    /// Translates the symbolic lemma description into concrete `TermId` atoms.
    /// Returns one or more clauses; the SAT solver must satisfy at least one
    /// literal in each clause.
    ///
    /// - **LengthSplit**: `[len(x) = len(y), ¬(len(x) = len(y))]`
    /// - **EmptySplit**: `[x = "", ¬(x = "")]`
    /// - **ConstSplit** (SSPLIT_CST): `[x = "", x = str.++(c[0], k)]`
    ///   where `c[0]` is the first character of constant `y`, `k` is a fresh
    ///   skolem. The `x = ""` guard prevents over-constraining the empty branch.
    ///   Plus auxiliary: `len(k) >= 0`.
    ///   Reference: CVC5 `core_solver.cpp:1618-1639`, `getConclusion` CONCAT_CSPLIT.
    /// - **VarSplit** (SSPLIT_VAR): `[len(x)=len(y), x = str.++(y, k), y = str.++(x, k)]`
    ///   where `k` is a fresh skolem. The `len(x)=len(y)` guard prevents
    ///   over-constraining the equal-length branch (#3375).
    ///   Plus auxiliary: `len(k) >= 0`.
    ///   Reference: CVC5 `core_solver.cpp:1642-1747`, `getConclusion` CONCAT_SPLIT.
    pub(in crate::executor) fn create_string_lemma_clauses(
        &mut self,
        lemma: &StringLemma,
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Vec<Vec<TermId>> {
        match lemma.kind {
            StringLemmaKind::LengthSplit => {
                // Case 6: introduce len(x) = len(y) as a decision atom.
                let len_x =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![lemma.x], Sort::Int);
                let len_y =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![lemma.y], Sort::Int);
                let eq = self.ctx.terms.mk_eq(len_x, len_y);
                let neq = self.ctx.terms.mk_not(eq);
                vec![vec![eq, neq]]
            }
            StringLemmaKind::EmptySplit => {
                // Case 8 prerequisite: introduce x = "" as a decision atom.
                let empty = self.ctx.terms.mk_string(String::new());
                let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                let neq = self.ctx.terms.mk_not(eq);
                vec![vec![eq, neq]]
            }
            StringLemmaKind::ConstSplit => {
                // SSPLIT_CST: x = "" OR x = char_at(y, char_offset) ++ k.
                //
                // Guard: ConstSplit is only valid when x != "". We add `x = ""`
                // as an escape literal so that when SAT backtracks to x = "",
                // the clause is trivially satisfied and the skolem k is
                // unconstrained (#3375).
                //
                // Extract the character at `char_offset` of constant y.
                // When char_offset > 0, the constant has already been partially
                // consumed by process_simple_neq's offset tracking.
                let first_char = match self.ctx.terms.get(lemma.y) {
                    TermData::Const(Constant::String(s)) => {
                        debug_assert!(
                            lemma.char_offset < s.chars().count(),
                            "BUG: ConstSplit char_offset {} >= constant y length {} — NF offset tracking error",
                            lemma.char_offset, s.chars().count()
                        );
                        match s.chars().nth(lemma.char_offset) {
                            Some(ch) => self.ctx.terms.mk_string(ch.to_string()),
                            None => {
                                // Invalid offset into constant y: degrade to EmptySplit.
                                let empty = self.ctx.terms.mk_string(String::new());
                                let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                                let neq = self.ctx.terms.mk_not(eq);
                                return vec![vec![eq, neq]];
                            }
                        }
                    }
                    _ => {
                        // Fallback: y is not a string constant or is empty.
                        // Degrade to EmptySplit.
                        let empty = self.ctx.terms.mk_string(String::new());
                        let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                        let neq = self.ctx.terms.mk_not(eq);
                        return vec![vec![eq, neq]];
                    }
                };

                // Build guard: x = "" (escape literal for empty-x branch)
                let empty = self.ctx.terms.mk_string(String::new());
                let x_eq_empty = self.ctx.terms.mk_eq(lemma.x, empty);

                // Get or create skolem for the remainder after first char.
                let k = skolem_cache.const_split(
                    &mut self.ctx.terms,
                    lemma.x,
                    lemma.y,
                    lemma.char_offset,
                );

                // Build: str.++(firstChar, k)
                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![first_char, k],
                    Sort::String,
                );
                // Primary clause: x = "" OR x = str.++(firstChar, k)
                let eq = self.ctx.terms.mk_eq(lemma.x, concat);

                // Bridge axioms for skolem k (CVC5 lengthPositive pattern):
                // len(k) >= 0, len(k)=0 => k="", k="" => len(k)=0
                let mut aux = self.emit_skolem_len_bridge(k);

                // Concat length decomposition: len(str.++(c, k)) = 1 + len(k)
                let len_concat =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![concat], Sort::Int);
                let one = self.ctx.terms.mk_int(BigInt::from(1));
                let len_k_for_sum =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![k], Sort::Int);
                let sum = self.ctx.terms.mk_add(vec![one, len_k_for_sum]);
                let concat_len_eq = self.ctx.terms.mk_eq(len_concat, sum);
                aux.push(vec![concat_len_eq]);

                // Build the primary clause with NF reason guards (#4094).
                //
                // ConstSplit is context-dependent: it asserts that x starts
                // with a specific character derived from the NF comparison.
                // Without guards, stale ConstSplit clauses from backtracked
                // branches persist and force variables to wrong characters.
                //
                // Clause: ¬(reason_1) ∨ ... ∨ ¬(reason_n) ∨ x="" ∨ x=char++k
                //
                // When the DPLL backtracks and undoes a reason literal, the
                // guard becomes true and the clause is trivially satisfied.
                let mut primary = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
                primary.push(x_eq_empty);
                primary.push(eq);

                let mut clauses = vec![primary];
                clauses.extend(aux);
                // Emit companion EmptySplit clauses for guard variables (#6273).
                clauses.extend(emit_guard_empty_splits(&mut self.ctx.terms, &lemma.reason));
                clauses
            }
            StringLemmaKind::ContainsPositive => {
                // Positive str.contains(x, y) reduction:
                //   x = sk_pre ++ y ++ sk_post
                // where sk_pre and sk_post are fresh skolem variables.
                //
                // This is a unit clause (always asserted): the CEGAR loop emits
                // this after the theory reported str.contains(x,y) = true with
                // non-ground arguments.
                //
                // Reference: CVC5 extf_solver.cpp:181-202

                // Get or create skolems for prefix and suffix.
                let sk_pre = skolem_cache.contains_pre(&mut self.ctx.terms, lemma.x, lemma.y);
                let sk_post = skolem_cache.contains_post(&mut self.ctx.terms, lemma.x, lemma.y);

                // Build: str.++(sk_pre, y, sk_post)
                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![sk_pre, lemma.y, sk_post],
                    Sort::String,
                );

                // Primary clause: x = str.++(sk_pre, y, sk_post)
                let eq = self.ctx.terms.mk_eq(lemma.x, concat);

                // Bridge axioms for both skolems (CVC5 lengthPositive pattern)
                let mut clauses = vec![vec![eq]];
                clauses.extend(self.emit_skolem_len_bridge(sk_pre));
                clauses.extend(self.emit_skolem_len_bridge(sk_post));
                clauses
            }
            StringLemmaKind::SubstrReduction => {
                // On-demand substr reduction: lower the same axiom emitted by
                // preregistration, but only for the specific blocking term.
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(lemma.x) else {
                    return Vec::new();
                };
                if name != "str.substr" || args.len() != 3 {
                    return Vec::new();
                }
                let s = args[0];
                let n = args[1];
                let m = args[2];

                let sk_pre = skolem_cache.substr_pre(&mut self.ctx.terms, lemma.x);
                let skt = skolem_cache.substr_result(&mut self.ctx.terms, lemma.x);
                let sk_suf = skolem_cache.substr_suffix(&mut self.ctx.terms, lemma.x);

                let zero = self.ctx.terms.mk_int(BigInt::from(0));
                let len_s = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
                let c1 = self.ctx.terms.mk_ge(n, zero);
                let c2 = self.ctx.terms.mk_gt(len_s, n);
                let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
                let c3 = self.ctx.terms.mk_gt(m, zero2);
                let cond = self.ctx.terms.mk_and(vec![c1, c2, c3]);

                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![sk_pre, skt, sk_suf],
                    Sort::String,
                );
                let b11 = self.ctx.terms.mk_eq(s, concat);

                let len_sk_pre =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![sk_pre], Sort::Int);
                let b12 = self.ctx.terms.mk_eq(len_sk_pre, n);

                let len_sk_suf =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![sk_suf], Sort::Int);
                let n_plus_m = self.ctx.terms.mk_add(vec![n, m]);
                let len_s2 = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
                let remainder = self.ctx.terms.mk_sub(vec![len_s2, n_plus_m]);
                let suf_eq_remainder = self.ctx.terms.mk_eq(len_sk_suf, remainder);
                let zero3 = self.ctx.terms.mk_int(BigInt::from(0));
                let suf_eq_zero = self.ctx.terms.mk_eq(len_sk_suf, zero3);
                let b13 = self.ctx.terms.mk_or(vec![suf_eq_remainder, suf_eq_zero]);

                let len_skt = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![skt], Sort::Int);
                let b14 = self.ctx.terms.mk_le(len_skt, m);

                let then_branch = self.ctx.terms.mk_and(vec![b11, b12, b13, b14]);
                let empty = self.ctx.terms.mk_string(String::new());
                let else_branch = self.ctx.terms.mk_eq(skt, empty);
                let ite = self.ctx.terms.mk_ite(cond, then_branch, else_branch);
                let bridge = self.ctx.terms.mk_eq(lemma.x, skt);

                let mut clauses = Vec::new();
                clauses.extend(self.lower_dynamic_axiom_to_clauses(ite));
                clauses.extend(self.lower_dynamic_axiom_to_clauses(bridge));
                clauses.extend(self.emit_skolem_len_bridge(sk_pre));
                clauses.extend(self.emit_skolem_len_bridge(skt));
                clauses.extend(self.emit_skolem_len_bridge(sk_suf));
                clauses
            }
            StringLemmaKind::ConstUnify => {
                // Length-aware constant unification (#4055): x = prefix(y, n).
                //
                // When a variable x has known length n and is compared against
                // a constant y with len(y) >= n, directly assert x = y[0..n].
                // The char_offset field carries n (the prefix length).
                //
                // This resolves in one CEGAR step what ConstSplit would need
                // n character-by-character iterations to accomplish.
                let prefix_str = match self.ctx.terms.get(lemma.y) {
                    TermData::Const(Constant::String(s)) => {
                        let chars: Vec<char> = s.chars().collect();
                        debug_assert!(
                            lemma.char_offset <= chars.len(),
                            "BUG: ConstUnify char_offset {} > constant y length {} — prefix silently truncated",
                            lemma.char_offset, chars.len()
                        );
                        let n = lemma.char_offset.min(chars.len());
                        chars[..n].iter().collect::<String>()
                    }
                    _ => {
                        // y is not a string constant — degrade to EmptySplit.
                        let empty = self.ctx.terms.mk_string(String::new());
                        let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                        let neq = self.ctx.terms.mk_not(eq);
                        return vec![vec![eq, neq]];
                    }
                };
                let prefix_term = self.ctx.terms.mk_string(prefix_str);
                let eq = self.ctx.terms.mk_eq(lemma.x, prefix_term);

                // Guard the equality clause with NF context reasons (#6273).
                // ConstUnify is context-dependent like ConstSplit: it asserts
                // x = prefix(y, n) based on the NF alignment. Without guards,
                // stale ConstUnify clauses persist after DPLL backtracking and
                // force wrong equalities, causing false-UNSAT.
                //
                // Clause: ¬(reason_1) ∨ ... ∨ ¬(reason_n) ∨ x=prefix(y,n)
                let mut primary = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 1);
                primary.push(eq);

                // Length axiom for the prefix constant (tautology, no guards needed).
                let len_prefix =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![prefix_term], Sort::Int);
                let n_val = self.ctx.terms.mk_int(BigInt::from(lemma.char_offset));
                let len_eq = self.ctx.terms.mk_eq(len_prefix, n_val);

                let mut clauses = vec![primary, vec![len_eq]];
                // Emit companion EmptySplit clauses for guard variables (#6273).
                clauses.extend(emit_guard_empty_splits(&mut self.ctx.terms, &lemma.reason));
                clauses
            }
            StringLemmaKind::VarSplit => {
                // SSPLIT_VAR: len(x)=len(y) OR (x = y ++ k) OR (y = x ++ k).
                //
                // Guard: VarSplit is only valid under len(x) != len(y). To
                // prevent over-constraining the equal-length branch, we add
                // `len(x) = len(y)` as an escape literal in the primary clause.
                // When SAT backtracks to len(x) = len(y), the clause is trivially
                // satisfied via the guard, and the split skolem k is unconstrained.
                //
                // CVC5 reference: core_solver.cpp:1642 asserts areDisequal(lenx, leny).
                // CVC5 uses explanation-guarded lemmas; Z4 achieves the same effect
                // by including the negated precondition in the clause itself (#3375).

                // Get or create skolem for the split remainder.
                let k = skolem_cache.var_split(&mut self.ctx.terms, lemma.x, lemma.y);

                // Build guard: len(x) = len(y) (escape literal for equal-length branch)
                let len_x =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![lemma.x], Sort::Int);
                let len_y =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![lemma.y], Sort::Int);
                let len_eq = self.ctx.terms.mk_eq(len_x, len_y);

                // Build: str.++(y, k) and str.++(x, k)
                let concat_yk =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.++"), vec![lemma.y, k], Sort::String);
                let concat_xk =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.++"), vec![lemma.x, k], Sort::String);

                // Primary clause: len(x)=len(y) OR x=str.++(y,k) OR y=str.++(x,k)
                let eq_xy = self.ctx.terms.mk_eq(lemma.x, concat_yk);
                let eq_yx = self.ctx.terms.mk_eq(lemma.y, concat_xk);

                // Build the primary clause with NF reason guards (#4094).
                //
                // VarSplit is context-dependent: it asserts that one of x,y
                // is a prefix of the other, which depends on the NF comparison
                // context. Without guards, stale VarSplit clauses persist after
                // DPLL backtracking and over-constrain variables.
                //
                // Non-emptiness guards (#6273): CVC5 adds explainNonEmpty(nc) to
                // VarSplit premises (core_solver.cpp:1702-1716). Without these,
                // the VarSplit clause is active even when a component is empty,
                // creating contradictions with ConstSplit clauses from the empty
                // branch. We add (x="") and (y="") as positive escape literals:
                // when a component IS empty, the escape literal is true and the
                // clause is trivially satisfied; when non-empty, the escape
                // literal is false and the VarSplit disjuncts remain active.
                //
                // Clause: ¬(reason_1) ∨ ... ∨ x="" ∨ y="" ∨ len(x)=len(y) ∨ x=y++k ∨ y=x++k
                let empty = self.ctx.terms.mk_string(String::new());
                let x_empty = self.ctx.terms.mk_eq(lemma.x, empty);
                let y_empty = self.ctx.terms.mk_eq(lemma.y, empty);
                let mut primary = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 5);
                primary.push(x_empty);
                primary.push(y_empty);
                primary.push(len_eq);
                primary.push(eq_xy);
                primary.push(eq_yx);

                // Bridge axioms for skolem k (CVC5 lengthPositive pattern)
                let mut clauses = vec![primary];
                clauses.extend(self.emit_skolem_len_bridge(k));
                // Emit companion EmptySplit clauses for guard variables (#6273).
                clauses.extend(emit_guard_empty_splits(&mut self.ctx.terms, &lemma.reason));
                clauses
            }
            StringLemmaKind::EqualitySplit => {
                // DEQ_STRINGS_EQ: x = y OR x != y.
                //
                // Emitted by process_simple_deq when two NF components have
                // equal lengths but unknown equality status. Forces the SAT
                // solver to decide: if x = y, the disequality may still hold
                // via other NF components; if x != y, the disequality is
                // directly satisfied at this position.
                //
                // CVC5 reference: core_solver.cpp:2280-2300 (sendSplit on
                // mismatched components after processSimpleDeq returns false).
                let eq = self.ctx.terms.mk_eq(lemma.x, lemma.y);
                let neq = self.ctx.terms.mk_not(eq);
                let mut clause = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
                clause.push(eq);
                clause.push(neq);
                vec![clause]
            }
            StringLemmaKind::DeqEmptySplit => {
                // DEQ_DISL_EMP_SPLIT: x = "" OR x != "".
                //
                // One NF component is constant, the other (x) is non-constant
                // and may be empty. Forces the SAT solver to decide emptiness
                // before the caller can apply decomposition cases.
                //
                // CVC5 reference: core_solver.cpp:2157-2167.
                let empty = self.ctx.terms.mk_string(String::new());
                let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                let neq = self.ctx.terms.mk_not(eq);
                let mut clause = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
                clause.push(eq);
                clause.push(neq);
                vec![clause]
            }
            StringLemmaKind::DeqFirstCharEqSplit => {
                // DEQ_DISL_FIRST_CHAR_EQ_SPLIT: x = c OR x != c.
                //
                // Non-constant x has length 1; lemma.y is the constant
                // component. Extract the first character and split on
                // equality with it.
                //
                // CVC5 reference: core_solver.cpp:2192-2198.
                let first_char_term =
                    if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(lemma.y) {
                        let ch: String = s.chars().take(1).collect();
                        self.ctx.terms.mk_string(ch)
                    } else {
                        // Fallback: use the full constant term.
                        lemma.y
                    };
                let eq = self.ctx.terms.mk_eq(lemma.x, first_char_term);
                let neq = self.ctx.terms.mk_not(eq);
                let mut clause = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
                clause.push(eq);
                clause.push(neq);
                vec![clause]
            }
            _ => {
                // Future StringLemmaKind variants — return empty for now.
                vec![]
            }
        }
    }

    /// Emit bridge axioms for a split skolem variable `k`.
    ///
    /// Returns clauses encoding the CVC5 `lengthPositive` pattern:
    /// 1. `len(k) >= 0` — non-negativity
    /// 2. `len(k) = 0 => k = ""` — zero-length implies empty
    /// 3. `k = "" => len(k) = 0` — empty implies zero-length
    ///
    /// These axioms close the gap between the SAT-level split lemma and
    /// the LIA length reasoning, allowing the CEGAR loop to converge on
    /// QF_SLIA problems involving split-generated skolems.
    ///
    /// Reference: CVC5 `term_registry.cpp:173-185` (`lengthPositive`).
    pub(in crate::executor) fn emit_skolem_len_bridge(&mut self, k: TermId) -> Vec<Vec<TermId>> {
        let len_k = self
            .ctx
            .terms
            .mk_app(Symbol::named("str.len"), vec![k], Sort::Int);
        let zero = self.ctx.terms.mk_int(BigInt::from(0));
        let empty = self.ctx.terms.mk_string(String::new());

        // Axiom 1: len(k) >= 0
        let len_ge_zero = self.ctx.terms.mk_ge(len_k, zero);

        // Axiom 2: len(k) = 0 => k = ""
        // Encoded as clause: [NOT(len(k)=0), k=""]
        // This ensures both atoms are separate theory atoms that the string
        // solver can process. The previous encoding as mk_implies created an
        // opaque atom invisible to the theory (#3429).
        let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
        let len_eq_zero = self.ctx.terms.mk_eq(len_k, zero2);
        let k_eq_empty = self.ctx.terms.mk_eq(k, empty);
        let not_len_eq_zero = self.ctx.terms.mk_not(len_eq_zero);

        // Axiom 3: k = "" => len(k) = 0
        // Encoded as clause: [NOT(k=""), len(k)=0]
        let not_k_eq_empty = self.ctx.terms.mk_not(k_eq_empty);
        let zero3 = self.ctx.terms.mk_int(BigInt::from(0));
        let len_eq_zero2 = self.ctx.terms.mk_eq(len_k, zero3);

        let clauses = vec![
            vec![len_ge_zero],
            vec![not_len_eq_zero, k_eq_empty],
            vec![not_k_eq_empty, len_eq_zero2],
        ];
        debug_assert!(
            clauses.iter().all(|c| !c.is_empty()),
            "BUG: emit_skolem_len_bridge produced empty clause — would cause false UNSAT"
        );
        clauses
    }

    /// Dynamic axioms are injected as raw SAT clauses via `apply_string_lemma`.
    ///
    /// Unlike the initial preprocessed assertion set, this path does not run
    /// Tseitin transformation. Lower implication terms to CNF at insertion time
    /// so `(=> a b)` contributes as `(~a \/ b)` instead of an opaque atom.
    pub(in crate::executor) fn lower_dynamic_axiom_to_clauses(
        &mut self,
        axiom: TermId,
    ) -> Vec<Vec<TermId>> {
        match self.ctx.terms.get(axiom) {
            // Disjunction (or a b ...): treat as a single clause with each disjunct as a literal.
            // mk_implies(a, b) desugars to or(not(a), b), so this handles implications.
            TermData::App(Symbol::Named(name), args) if name == "or" && args.len() >= 2 => {
                vec![args.clone()]
            }
            // Conjunction (and a b ...): each conjunct becomes a separate unit clause.
            TermData::App(Symbol::Named(name), args) if name == "and" && args.len() >= 2 => {
                args.iter().map(|&a| vec![a]).collect()
            }
            // Atom or anything else: single unit clause.
            _ => vec![vec![axiom]],
        }
    }
}
