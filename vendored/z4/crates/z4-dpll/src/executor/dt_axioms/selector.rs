// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DT selector projection, tester evaluation, exhaustiveness, constructor,
//! and equality-to-tester axioms (A-E).
//!
//! Extracted from `dt_axioms.rs` as part of the code-health module split.

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::Symbol;
use z4_core::{Sort, TermData, TermId};

use super::SelectorList;
use crate::executor::Executor;

// Type aliases for datatype axiom generation (fixes clippy::type_complexity)
/// Constructor application info: (constructor_term, args, selectors)
type CtorAppInfo = (TermId, Vec<TermId>, SelectorList);
/// Constructor binding: (constructor_name, args, selectors)
type CtorBinding = (String, Vec<TermId>, SelectorList);
/// Constructor args and selectors (for nested resolution)
type CtorArgsAndSelectors = (Vec<TermId>, SelectorList);

impl Executor {
    fn selector_signature(&self, ctor_name: &str) -> Option<SelectorList> {
        self.ctx
            .constructor_selector_info(ctor_name)
            .map(<[_]>::to_vec)
    }

    /// Generate DT selector, tester, exhaustiveness, constructor, and equality axioms.
    ///
    /// This is the central DT axiom generator for combined DT+theory solver paths
    /// (DT_AUFLIA, DT_AUFLRA, DT_AUFLIRA, DT_UFBV, DT_AUFBV, DT_AX). It produces
    /// five classes of axioms:
    ///
    /// (A) Selector projection: `sel_i(C(a_0, ..., a_n)) = a_i`
    /// (B) Tester evaluation: `is-C(C(...)) = true`, `is-C'(C(...)) = false`
    /// (B') Tester evaluation for axiom-C terms (second pass, #2766)
    /// (C) Constructor: `is-C(x) => x = C(sel_1(x), ..., sel_n(x))`
    /// (D) Exhaustiveness: `(or (is-C1 x) ... (is-Ck x))` for DT variables
    /// (E) Equality-to-tester: `x = C(...) => is-C(x)` (#1737)
    ///
    /// Also handles:
    /// - Transitive equality propagation via union-find (#1741)
    /// - Variable indirection: `p = C(args)` => selector axioms for `p` (#1740)
    /// - Nested selector resolution (#1765)
    /// - Reachability filtering to avoid combinatorial explosion (#5082)
    pub(in crate::executor) fn dt_selector_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        // Capture the current term-store size so we don't scan terms created during
        // axiom generation itself.
        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }

        // First pass: collect constructor applications + selector metadata without
        // mutating the term store (avoids borrow conflicts and unstable references).
        let mut ctor_apps: Vec<CtorAppInfo> = Vec::new();

        // Collect ALL constructor terms (including nullary) for tester evaluation axioms (B).
        // Each entry: (term, ctor_name, dt_name) where dt_name is the datatype.
        // Note: Nullary constructors are stored as Var terms, not App terms (#1745).
        let mut ctor_terms_for_testers: Vec<(TermId, String, String)> = Vec::new();

        // Union-find for computing equivalence classes of asserted equalities.
        // This handles transitive equality propagation (#1741): if `p = q` and `q = C(args)`,
        // we need to generate selector axioms for `p` as well.
        let mut uf_parent: HashMap<TermId, TermId> = HashMap::new();
        let uf_find = |parent: &mut HashMap<TermId, TermId>, mut x: TermId| -> TermId {
            let mut path = Vec::new();
            while let Some(&p) = parent.get(&x) {
                if p == x {
                    break;
                }
                path.push(x);
                x = p;
            }
            // Path compression
            for node in path {
                parent.insert(node, x);
            }
            x
        };
        let uf_union = |parent: &mut HashMap<TermId, TermId>, a: TermId, b: TermId| {
            let ra = uf_find(parent, a);
            let rb = uf_find(parent, b);
            if ra != rb {
                parent.insert(ra, rb);
            }
        };

        // Collect asserted equalities for union-find
        let mut asserted_equalities: Vec<(TermId, TermId)> = Vec::new();

        // Maps: term p -> (ctor_name, args, selectors) for direct `p = C(args)` equalities
        let mut var_to_ctor: HashMap<TermId, CtorBinding> = HashMap::new();

        // Collect selector applications in the term store: sel_name -> [(sel_app, arg)]
        // where sel_app = sel(arg).
        let mut selector_apps: HashMap<String, Vec<(TermId, TermId)>> = HashMap::new();

        for idx in 0..base_term_len {
            debug_assert!(u32::try_from(idx).is_ok(), "term id overflow");
            let term = TermId::new(idx as u32);

            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    // Check if this is a constructor application
                    if let Some(selectors) = self.ctx.constructor_selectors(name) {
                        // Track ALL constructor terms for tester axioms (B) (#1745)
                        if let Some((dt_name, ctor_name)) = self.ctx.is_constructor(name) {
                            ctor_terms_for_testers.push((term, ctor_name, dt_name));
                        }

                        // Only collect selector metadata for non-nullary constructors
                        if !selectors.is_empty() {
                            if let Some(selector_syms) = self.selector_signature(name) {
                                if selector_syms.len() == args.len() {
                                    ctor_apps.push((term, args.clone(), selector_syms));
                                }
                            }
                        }
                    }

                    // Check if this is a selector application (single argument function
                    // where the function name is a registered selector).
                    if args.len() == 1 {
                        // Check if name is a selector by looking for it in any constructor's
                        // selector list.
                        for (_ctor_name, sel_list) in self.ctx.ctor_selectors_iter() {
                            if sel_list.contains(&name.clone()) {
                                selector_apps
                                    .entry(name.clone())
                                    .or_default()
                                    .push((term, args[0]));
                                break;
                            }
                        }
                    }

                    // Check if this is an equality `= p C(args)` or `= C(args) p`
                    // CRITICAL: Only process equalities that are directly asserted,
                    // not equalities nested inside larger formulas (e.g., disjunctions).
                    // Generating axioms for non-asserted equalities is unsound (#1740 audit).
                    if name == "=" && args.len() == 2 && base_assertions.contains(&term) {
                        let (lhs, rhs) = (args[0], args[1]);

                        // Check if either side is a constructor
                        let lhs_is_ctor = matches!(
                            self.ctx.terms.get(lhs),
                            TermData::App(Symbol::Named(n), _)
                            if self.ctx.constructor_selectors(n).is_some()
                        );
                        let rhs_is_ctor = matches!(
                            self.ctx.terms.get(rhs),
                            TermData::App(Symbol::Named(n), _)
                            if self.ctx.constructor_selectors(n).is_some()
                        );

                        // Collect variable-to-variable equalities for union-find (#1741)
                        if !lhs_is_ctor && !rhs_is_ctor {
                            asserted_equalities.push((lhs, rhs));
                        }

                        // Try to find which side is a constructor
                        for (p, ctor_term) in [(lhs, rhs), (rhs, lhs)] {
                            if let TermData::App(Symbol::Named(ctor_name), ctor_args) =
                                self.ctx.terms.get(ctor_term)
                            {
                                if let Some(selectors) = self.ctx.constructor_selectors(ctor_name) {
                                    if !selectors.is_empty() {
                                        if let Some(selector_syms) =
                                            self.selector_signature(ctor_name)
                                        {
                                            if selector_syms.len() == ctor_args.len() {
                                                // Only record if p is NOT itself a constructor
                                                // app (direct ctor apps are handled above)
                                                let p_is_ctor = if p == lhs {
                                                    lhs_is_ctor
                                                } else {
                                                    rhs_is_ctor
                                                };
                                                if !p_is_ctor {
                                                    var_to_ctor.insert(
                                                        p,
                                                        (
                                                            ctor_name.clone(),
                                                            ctor_args.clone(),
                                                            selector_syms,
                                                        ),
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                // Handle nullary constructors stored as Var terms (#1745)
                // In z4, nullary constructors like `None` are stored as Var("None", id)
                // not App("None", []), so we need to check Var terms as well.
                TermData::Var(name, _) => {
                    if let Some((dt_name, ctor_name)) = self.ctx.is_constructor(name) {
                        ctor_terms_for_testers.push((term, ctor_name, dt_name));
                    }
                }
                _ => continue,
            }
        }

        // Build union-find from asserted equalities (#1741)
        for (a, b) in &asserted_equalities {
            uf_union(&mut uf_parent, *a, *b);
        }

        // Propagate var_to_ctor through equivalence classes (#1741)
        // If q = C(args) and p = q (transitively), then p should also map to C(args)
        // Sort for deterministic propagation order (#3060)
        let mut direct_mappings: Vec<_> =
            var_to_ctor.iter().map(|(k, v)| (*k, v.clone())).collect();
        direct_mappings.sort_by_key(|(term, _)| term.0);
        for (term, ctor_info) in direct_mappings {
            let root = uf_find(&mut uf_parent, term);
            // Find all terms in same equivalence class
            for (a, b) in &asserted_equalities {
                for t in [*a, *b] {
                    if t != term && uf_find(&mut uf_parent, t) == root {
                        var_to_ctor.entry(t).or_insert_with(|| ctor_info.clone());
                    }
                }
            }
        }

        // Second pass: generate equality axioms.
        //
        // For each constructor application `C(a_0, ..., a_{n-1})` and its ordered selector list
        // `[sel_0, ..., sel_{n-1}]`, generate the theory axiom:
        // `sel_i(C(a_0, ..., a_{n-1})) = a_i`.
        //
        // We also track which selector applications equal constructors, so we can generate
        // transitive axioms for nested selectors (#1765).
        let mut extra: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::new();

        // Track selector apps that equal constructor terms: sel_app -> (ctor_args, selectors)
        // This is used for nested selector resolution (#1765).
        let mut sel_app_to_ctor: HashMap<TermId, CtorArgsAndSelectors> = HashMap::new();

        for (ctor_term, args, selectors) in &ctor_apps {
            debug_assert_eq!(selectors.len(), args.len());
            for (idx, (sel_name, sel_sort)) in selectors.iter().enumerate() {
                let sel_app = self.ctx.terms.mk_app(
                    Symbol::named(sel_name.clone()),
                    vec![*ctor_term],
                    sel_sort.clone(),
                );
                let eq = self.ctx.terms.mk_eq(sel_app, args[idx]);

                if base_assertions.contains(&eq) {
                    continue;
                }
                if seen.insert(eq) {
                    extra.push(eq);
                }

                // Track that sel_app equals args[idx], which may be a constructor (#1765).
                // This enables nested selector resolution: if args[idx] is a constructor C2(...),
                // then any selector applied to sel_app should get axioms based on C2.
                let arg = args[idx];
                if let TermData::App(Symbol::Named(inner_ctor_name), inner_args) =
                    self.ctx.terms.get(arg)
                {
                    if let Some(inner_selectors) = self.ctx.constructor_selectors(inner_ctor_name) {
                        if !inner_selectors.is_empty() {
                            if let Some(inner_selector_syms) =
                                self.selector_signature(inner_ctor_name)
                            {
                                if inner_selector_syms.len() == inner_args.len() {
                                    sel_app_to_ctor
                                        .insert(sel_app, (inner_args.clone(), inner_selector_syms));
                                }
                            }
                        }
                    }
                }
            }
        }

        // Third pass: generate selector axioms for variable indirection (#1740).
        //
        // For each equality `p = C(a_0, ..., a_{n-1})` in the assertions and each
        // selector application `sel_i(p)` in the term store, generate:
        // `sel_i(p) = a_i`.
        //
        // This handles cases like:
        //   (assert (= p (mk-pair x y)))
        //   (assert (not (= (fst p) x)))
        // Where we need `fst(p) = x` to derive a contradiction.
        for (p, (_ctor_name, args, selectors)) in &var_to_ctor {
            for (idx, (sel_name, sel_sort)) in selectors.iter().enumerate() {
                // Check if sel_i(p) appears in the term store
                if let Some(apps) = selector_apps.get(sel_name) {
                    for &(sel_app, sel_arg) in apps {
                        if sel_arg == *p {
                            // Found sel_i(p), generate axiom sel_i(p) = a_i
                            let eq = self.ctx.terms.mk_eq(sel_app, args[idx]);

                            if base_assertions.contains(&eq) {
                                continue;
                            }
                            if seen.insert(eq) {
                                extra.push(eq);
                            }
                        }
                    }
                }

                // Also generate the canonical axiom sel_i(p) = a_i even if sel_i(p)
                // doesn't appear explicitly, because the SAT solver may need it.
                let sel_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(sel_name), vec![*p], sel_sort.clone());
                let eq = self.ctx.terms.mk_eq(sel_app, args[idx]);

                if base_assertions.contains(&eq) {
                    continue;
                }
                if seen.insert(eq) {
                    extra.push(eq);
                }
            }
        }

        // (E) Nested selector axioms for recursive datatypes (#1765).
        //
        // When sel(ctor(...)) = inner_ctor(...), any selector applied to sel(ctor(...))
        // should get axioms based on inner_ctor.
        //
        // Example: For Wrapper = base | c(f: Wrapper)
        //   f(c(c(base))) = c(base)     (generated in second pass)
        //   f(f(c(c(base)))) should equal f(c(base)) = base
        //
        // We iterate to fixpoint: keep generating axioms until no new ones are added.
        // This handles arbitrarily deep nesting.
        //
        // Safety bound: 100 iterations handles extremely deep nesting while protecting
        // against infinite loops from potential bugs. Each iteration processes one nesting
        // level, so this supports up to 100 levels of selector application.
        const MAX_NESTED_ITERATIONS: usize = 100;
        for _iteration in 0..MAX_NESTED_ITERATIONS {
            let mut new_axioms = Vec::new();
            let mut new_mappings: Vec<CtorAppInfo> = Vec::new();

            // For each selector application sel(arg) in the term store, check if arg
            // is known to equal a constructor (via sel_app_to_ctor).
            for (sel_name, apps) in &selector_apps {
                for &(sel_app_term, sel_arg) in apps {
                    // If sel_arg is a selector application that equals a constructor...
                    if let Some((ctor_args, ctor_selectors)) = sel_app_to_ctor.get(&sel_arg) {
                        // Find which selector index sel_name corresponds to
                        for (idx, (ctor_sel_name, _ctor_sel_sort)) in
                            ctor_selectors.iter().enumerate()
                        {
                            if ctor_sel_name == sel_name {
                                // Generate axiom: sel(sel_arg) = ctor_args[idx]
                                // But we already have sel_app_term = sel(sel_arg), so:
                                let eq = self.ctx.terms.mk_eq(sel_app_term, ctor_args[idx]);
                                if !base_assertions.contains(&eq) && seen.insert(eq) {
                                    new_axioms.push(eq);

                                    // Track if the result is also a constructor
                                    let result = ctor_args[idx];
                                    if let TermData::App(Symbol::Named(inner_name), inner_args) =
                                        self.ctx.terms.get(result)
                                    {
                                        if let Some(inner_sels) =
                                            self.ctx.constructor_selectors(inner_name)
                                        {
                                            if !inner_sels.is_empty() {
                                                if let Some(inner_sel_syms) =
                                                    self.selector_signature(inner_name)
                                                {
                                                    if inner_sel_syms.len() == inner_args.len() {
                                                        new_mappings.push((
                                                            sel_app_term,
                                                            inner_args.clone(),
                                                            inner_sel_syms,
                                                        ));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                break;
                            }
                        }
                    }
                }
            }

            // If no new axioms were generated, we've reached fixpoint.
            if new_axioms.is_empty() {
                break;
            }

            extra.extend(new_axioms);
            for (sel_app, args, sels) in new_mappings {
                sel_app_to_ctor.entry(sel_app).or_insert((args, sels));
            }
        }

        // (D) Exhaustiveness axioms for datatype variables (#1738).
        //
        // For each datatype-sorted variable `x : D` with constructors `C_1..C_k`, assert:
        // `(or (is-C1 x) ... (is-Ck x))`
        //
        // This ensures at least one constructor applies to any datatype value.
        //
        // Note: Datatype sorts are stored as Sort::Uninterpreted("<name>") in z4, not
        // Sort::Datatype. We identify datatype-sorted symbols by checking if their sort
        // name matches a declared datatype.
        //
        // Implementation: Build a map from datatype name -> constructors once, then use it
        // for both identifying DT-sorted variables and generating axioms.
        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();

        // Collect all term IDs reachable from assertions to avoid generating
        // axioms for unconstrained DT variables (#5082). Benchmarks like
        // typed_v5l20092 declare 15 DT variables but only use 1 in assertions;
        // generating exhaustiveness + constructor axioms for all 15 creates a
        // combinatorial explosion that prevents solving.
        let reachable_terms: HashSet<TermId> = {
            let mut visited = HashSet::new();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Const(_) | TermData::Var(_, _) => {}
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, val) in bindings {
                            stack.push(*val);
                        }
                    }
                    TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                        stack.push(*body);
                    }
                    // All current TermData variants are handled above.
                    // This arm is required by #[non_exhaustive] and catches future variants.
                    other => unreachable!(
                        "unhandled TermData variant in dt_axioms reachability: {other:?}"
                    ),
                }
            }
            visited
        };

        let dt_vars: Vec<(TermId, String)> = {
            let mut result: Vec<(TermId, String)> = self
                .ctx
                .symbol_iter()
                .filter_map(|(sym_name, info)| {
                    // Skip constructor symbols themselves - they get tester evaluation axioms (B),
                    // not exhaustiveness axioms (D). Exhaustiveness is for user-declared variables.
                    if self.ctx.is_constructor(sym_name).is_some() {
                        return None;
                    }
                    if let Sort::Uninterpreted(sort_name) = &info.sort {
                        if datatype_ctors.contains_key(sort_name) {
                            // Only generate axioms for variables reachable from assertions (#5082)
                            return info
                                .term
                                .filter(|t| reachable_terms.contains(t))
                                .map(|t| (t, sort_name.clone()));
                        }
                    }
                    // Also check Sort::Datatype for completeness
                    if let Sort::Datatype(dt) = &info.sort {
                        return info
                            .term
                            .filter(|t| reachable_terms.contains(t))
                            .map(|t| (t, dt.name.clone()));
                    }
                    None
                })
                .collect();

            // (#6190) Also collect DT-sorted selector applications from assertions.
            //
            // Selector applications like `(cdr x4)` produce values of datatype
            // sort but are not declared symbols. Without exhaustiveness axioms
            // for these sub-terms, the solver cannot derive that e.g.
            // `(cdr x4)` must be one of the constructors, causing false SAT.
            //
            // (#6201) Only add exhaustiveness for selector applications, not ALL
            // DT-sorted sub-terms. The original #6190 fix was too broad — adding
            // exhaustiveness for every DT-sorted reachable term caused a 13.8%
            // performance regression on QF_DT benchmarks (174→150 solves).
            // Selector applications are the specific case that caused the soundness
            // bug; other DT-sorted terms (ITE, UF) inherit exhaustiveness from
            // their constituent variables.
            let existing: HashSet<TermId> = result.iter().map(|(t, _)| *t).collect();
            let selector_term_ids: HashSet<TermId> = selector_apps
                .values()
                .flat_map(|apps| apps.iter().map(|(sel_app, _arg)| *sel_app))
                .collect();
            for &t in &selector_term_ids {
                if existing.contains(&t) || !reachable_terms.contains(&t) {
                    continue;
                }
                let sort = self.ctx.terms.sort(t);
                let dt_name = match sort {
                    Sort::Uninterpreted(name) if datatype_ctors.contains_key(name) => name.clone(),
                    Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => dt.name.clone(),
                    _ => continue,
                };
                result.push((t, dt_name));
            }
            result
        };

        for (var_term, dt_name) in &dt_vars {
            let Some(dt_ctors) = datatype_ctors.get(dt_name) else {
                continue;
            };

            if dt_ctors.is_empty() {
                continue;
            }

            // Build disjunction of all testers: (or (is-C1 x) ... (is-Ck x))
            let mut tester_apps = Vec::new();
            for ctor_name in dt_ctors {
                let tester_name = format!("is-{ctor_name}");
                let tester_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![*var_term], Sort::Bool);
                tester_apps.push(tester_app);
            }

            let axiom = self.ctx.terms.mk_or(tester_apps);
            if !base_assertions.contains(&axiom) && seen.insert(axiom) {
                extra.push(axiom);
            }
        }

        // (B) Tester evaluation axioms (#1745).
        //
        // For each constructor term `C(...)` in the term store, generate:
        // - `is-C(C(...)) = true` (positive case)
        // - `is-C'(C(...)) = false` for all other constructors C' of the same datatype (negative case)
        //
        // This ensures that recognizers evaluate correctly for concrete constructor values,
        // including nullary constructors like `None` where `is-None(None) = true`.
        for (ctor_term, ctor_name, dt_name) in ctor_terms_for_testers {
            // Get all constructors of this datatype
            let Some(dt_ctors) = datatype_ctors.get(&dt_name) else {
                continue;
            };

            let true_term = self.ctx.terms.true_term();
            let false_term = self.ctx.terms.false_term();

            for other_ctor in dt_ctors {
                let tester_name = format!("is-{other_ctor}");
                let tester_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![ctor_term], Sort::Bool);

                // is-C(C(...)) = true, is-C'(C(...)) = false for C' != C
                let expected = if other_ctor == &ctor_name {
                    true_term
                } else {
                    false_term
                };

                let eq = self.ctx.terms.mk_eq(tester_app, expected);
                if !base_assertions.contains(&eq) && seen.insert(eq) {
                    extra.push(eq);
                }
            }
        }

        // (C) Constructor axiom (#1737): tester → constructor.
        //
        // For each datatype variable `x : D` and each constructor `C` with selectors
        // `sel_1..sel_n`, assert:
        // `(=> (is-C x) (= x (C (sel_1 x) ... (sel_n x))))`
        //
        // This turns a tester decision into a concrete constructor term for equality reasoning.
        // When combined with constructor clash detection in DtSolver, this also enforces
        // tester disjointness: if both is-C1(x) and is-C2(x) hold, we derive x = C1(...) and
        // x = C2(...), which clashes.
        //
        // Nullary constructor case: (=> (is-C x) (= x C)) - selector list is empty.
        //
        // We collect the new constructor terms created here so axiom (B') can generate
        // tester evaluation axioms for them (#2766).
        let mut axiom_c_ctor_terms: Vec<(TermId, String, String)> = Vec::new();
        for (var_term, dt_name) in &dt_vars {
            let Some(dt_ctors) = datatype_ctors.get(dt_name) else {
                continue;
            };

            for ctor_name in dt_ctors {
                let tester_name = format!("is-{ctor_name}");
                let tester_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![*var_term], Sort::Bool);

                // Build C(sel_1(x), ..., sel_n(x)) or just C for nullary
                // Clone selectors to avoid borrow conflict with self.ctx.terms
                let selectors: Vec<String> = match self.ctx.constructor_selectors(ctor_name) {
                    Some(sels) => sels.to_vec(),
                    None => continue,
                };
                let ctor_term = if selectors.is_empty() {
                    // Nullary constructor - use constant term
                    let dt_sort = Sort::Uninterpreted(dt_name.clone());
                    self.ctx.terms.mk_var(ctor_name.clone(), dt_sort)
                } else {
                    let Some(selector_info) = self
                        .ctx
                        .constructor_selector_info(ctor_name)
                        .map(<[_]>::to_vec)
                    else {
                        continue;
                    };
                    if selector_info.len() != selectors.len() {
                        continue;
                    }

                    // Build selector applications: sel_1(x), ..., sel_n(x)
                    let mut sel_apps = Vec::with_capacity(selectors.len());
                    for (sel_name, (_, sel_sort)) in selectors.iter().zip(selector_info.iter()) {
                        let sel_app = self.ctx.terms.mk_app(
                            Symbol::named(sel_name),
                            vec![*var_term],
                            sel_sort.clone(),
                        );
                        sel_apps.push(sel_app);
                    }

                    // Build C(sel_1(x), ..., sel_n(x))
                    let dt_sort = Sort::Uninterpreted(dt_name.clone());
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(ctor_name), sel_apps, dt_sort)
                };

                // Track non-nullary constructor terms for axiom (B') below (#2766).
                if !selectors.is_empty() {
                    axiom_c_ctor_terms.push((ctor_term, ctor_name.clone(), dt_name.clone()));
                }

                // Build: (=> (is-C x) (= x C(...)))
                let eq = self.ctx.terms.mk_eq(*var_term, ctor_term);
                let implication = self.ctx.terms.mk_implies(tester_app, eq);

                if !base_assertions.contains(&implication) && seen.insert(implication) {
                    extra.push(implication);
                }
            }
        }

        // (B') Tester evaluation for axiom-C constructor terms (#2766).
        //
        // Axiom (C) creates constructor terms like `Err(sel-err(x))` that were not in the
        // original formula. Axiom (B) ran before (C) and only saw pre-existing constructor
        // terms. Without this second pass, the combined DT+arithmetic solver (AUFLIA path)
        // cannot derive `is-Ok(Err(sel-err(x))) = false`, breaking cross-tester reasoning.
        //
        // In the pure DT path (solve_dt), the interactive DtSolver + DPLL(T) loop handles
        // this: tester decisions propagate equalities that lead to constructor clash
        // detection, so explicit tester-evaluation axioms are unnecessary. The axiom-based
        // AUFLIA/AUFLRA paths lack this dynamic interaction and need explicit axioms.
        for (ctor_term, ctor_name, dt_name) in axiom_c_ctor_terms {
            let Some(dt_ctors) = datatype_ctors.get(&dt_name) else {
                continue;
            };

            let true_term = self.ctx.terms.true_term();
            let false_term = self.ctx.terms.false_term();

            for other_ctor in dt_ctors {
                let tester_name = format!("is-{other_ctor}");
                let tester_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![ctor_term], Sort::Bool);

                let expected = if other_ctor == &ctor_name {
                    true_term
                } else {
                    false_term
                };

                let eq = self.ctx.terms.mk_eq(tester_app, expected);
                if !base_assertions.contains(&eq) && seen.insert(eq) {
                    extra.push(eq);
                }
            }
        }

        // (E) Equality-to-tester axiom (#1737): x = C(...) → is-C(x).
        //
        // For each asserted equality `eq := (= x t)` where `t := C(a_1, ..., a_n)` is
        // a constructor application, assert `(is-C x)`.
        //
        // This is a "micro congruence" lemma that avoids needing full EUF congruence
        // for testers. Together with axiom (C), it enables:
        // 1. x = C(args) implies is-C(x) (this axiom)
        // 2. is-C(x) implies x = C(sel_1(x), ..., sel_n(x)) (axiom C)
        // 3. DtSolver injectivity detects a_i = sel_i(x) must hold
        //
        // Note: We assert is-C(x) directly since the equality is already asserted.
        // This is equivalent to modus ponens on (=> (= x C(args)) (is-C x)).
        for (p, (ctor_name, _args, _selectors)) in &var_to_ctor {
            let tester_name = format!("is-{ctor_name}");
            let tester_app =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&tester_name), vec![*p], Sort::Bool);

            if !base_assertions.contains(&tester_app) && seen.insert(tester_app) {
                extra.push(tester_app);
            }
        }

        extra
    }
}
