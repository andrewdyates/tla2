// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stdlib application translation helpers for the Rust emitter.

use super::*;

impl<'a> RustEmitter<'a> {
    fn translate_recursive_helper_apply(
        &self,
        name: &str,
        args: &[Spanned<Expr>],
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> Option<String> {
        if !self.recursive_helpers.contains(name) {
            return None;
        }

        let mut call_args = Vec::new();
        if self.recursive_helpers_needing_state.contains(name) {
            call_args.push(state_ref.to_string());
        }
        for arg in args {
            let arg_str =
                self.expr_to_rust_with_scope(&arg.node, prefix_state, state_ref, prime_state_ref);
            call_args.push(format!("&{arg_str}"));
        }
        let depth_arg = if self.in_recursive_helper.get() {
            "__depth + 1".to_string()
        } else {
            "0".to_string()
        };
        call_args.push(depth_arg);

        Some(format!(
            "self.{}({})",
            to_snake_case(name),
            call_args.join(", ")
        ))
    }

    /// Translate a stdlib operator application to Rust
    pub(super) fn translate_stdlib_apply(
        &self,
        name: &str,
        args: &[Spanned<Expr>],
        prefix_state: bool,
        state_ref: &str,
        prime_state_ref: Option<&str>,
    ) -> String {
        let arg = |i: usize| -> String {
            args.get(i)
                .map(|a| {
                    self.expr_to_rust_with_scope(&a.node, prefix_state, state_ref, prime_state_ref)
                })
                .unwrap_or_else(|| "/* missing arg */".to_string())
        };

        match name {
            // ===== Sequences (Sequences module) =====
            // Len(s) - length of sequence
            "Len" => format!("({}.len() as i64)", arg(0)),
            // Head(s) - first element
            "Head" => format!(
                "{}.first().cloned().expect(\"Head requires non-empty sequence\")",
                arg(0)
            ),
            // Tail(s) - all but first element
            "Tail" => format!("{}.into_iter().skip(1).collect::<Vec<_>>()", arg(0)),
            // Append(s, e) - append element to sequence
            "Append" => {
                format!("{{ let mut v = {}.clone(); v.push({}); v }}", arg(0), arg(1))
            }
            // SubSeq(s, m, n) - subsequence from index m to n (TLA+ is 1-indexed)
            "SubSeq" => {
                format!(
                    "{}[({} - 1) as usize..{} as usize].to_vec()",
                    arg(0),
                    arg(1),
                    arg(2)
                )
            }
            // Seq(S) - set of all sequences over S (placeholder - can't enumerate infinite set)
            "Seq" => format!("/* Seq({}) - infinite set */", arg(0)),
            // SelectSeq(s, Test) - filter sequence by predicate
            "SelectSeq" => {
                format!(
                    "{}.into_iter().filter(|x| {}(x.clone())).collect::<Vec<_>>()",
                    arg(0),
                    arg(1)
                )
            }

            // ===== FiniteSets module =====
            // Cardinality(S) - number of elements in set
            "Cardinality" => format!("({}.len() as i64)", arg(0)),
            // IsFiniteSet(S) - always true for our finite sets
            "IsFiniteSet" => "true".to_string(),

            // ===== TLC module =====
            // Print(out, val) - print and return val
            "Print" => format!("{{ println!(\"{{}}\", {}); {} }}", arg(0), arg(1)),
            // PrintT(out) - print and return TRUE
            "PrintT" => format!("{{ println!(\"{{}}\", {}); true }}", arg(0)),
            // Assert(val, out) - assert val is true
            "Assert" => format!("{{ assert!({}, \"{{}}\", {}); true }}", arg(0), arg(1)),
            // ToString(v) - convert value to string
            "ToString" => format!("format!(\"{{:?}}\", {})", arg(0)),
            // JavaTime - current time in milliseconds
            "JavaTime" => {
                "std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).expect(\"system clock should be at or after UNIX_EPOCH\").as_millis() as i64".to_string()
            }

            // ===== SequencesExt module (community) =====
            // Reverse(s) - reverse sequence
            "Reverse" => {
                format!("{{ let mut v = {}.clone(); v.reverse(); v }}", arg(0))
            }
            // Front(s) - all but last element
            "Front" => format!("{}[..{}.len() - 1].to_vec()", arg(0), arg(0)),
            // Last(s) - last element
            "Last" => format!(
                "{}.last().cloned().expect(\"Last requires non-empty sequence\")",
                arg(0)
            ),
            // Cons(e, s) - prepend element
            "Cons" => {
                format!(
                    "{{ let mut v = vec![{}]; v.extend({}.clone()); v }}",
                    arg(0),
                    arg(1)
                )
            }
            // Contains(s, e) - check if sequence contains element
            "Contains" => format!("{}.contains(&{})", arg(0), arg(1)),
            // ToSet(s) or Range(s) - convert sequence to set
            "ToSet" | "Range" if args.len() == 1 => {
                format!("{}.iter().cloned().collect::<TlaSet<_>>()", arg(0))
            }
            // Indices(s) - 1..Len(s)
            "Indices" => format!("range_set(1, {}.len() as i64)", arg(0)),

            // ===== FiniteSetsExt module (community) =====
            // Max(S) - maximum element of set
            "Max" => format!(
                "{}.iter().max().cloned().expect(\"Max requires non-empty set\")",
                arg(0)
            ),
            // Min(S) - minimum element of set
            "Min" => format!(
                "{}.iter().min().cloned().expect(\"Min requires non-empty set\")",
                arg(0)
            ),
            // Sum(S) - sum of set elements
            "Sum" => format!("{}.iter().sum::<i64>()", arg(0)),
            // Product(S) - product of set elements
            "Product" => format!("{}.iter().product::<i64>()", arg(0)),
            // SymDiff(S, T) - symmetric difference
            "SymDiff" => {
                format!(
                    "{}.difference(&{}).union(&{}.difference(&{}))",
                    arg(0),
                    arg(1),
                    arg(1),
                    arg(0)
                )
            }
            // Flatten(SS) - union of sets of sets
            "Flatten" => {
                format!(
                    "{}.iter().fold(TlaSet::new(), |acc, s| acc.union(s))",
                    arg(0)
                )
            }
            // Choose(S) - arbitrary element from set (returns first in sorted order)
            "Choose" if args.len() == 1 => {
                format!(
                    "{}.iter().next().cloned().expect(\"Choose requires non-empty set\")",
                    arg(0)
                )
            }

            // ===== Functions module (community) =====
            // Restrict(f, S) - restrict function domain to S
            "Restrict" => {
                format!(
                    "{}.iter().filter(|(k, _)| {}.contains(k)).cloned().collect::<TlaFunc<_, _>>()",
                    arg(0),
                    arg(1)
                )
            }
            // IsInjective(f) - check if function is injective
            "IsInjective" => {
                format!(
                    "{{ let vals: Vec<_> = {}.iter().map(|(_, v)| v).collect(); vals.len() == vals.iter().collect::<std::collections::HashSet<_>>().len() }}",
                    arg(0)
                )
            }

            // ===== Bags module =====
            // EmptyBag - empty multiset
            "EmptyBag" => "TlaFunc::new()".to_string(),

            // ===== Unknown operator - generate fallback =====
            _ => {
                if let Some(recursive_call) = self.translate_recursive_helper_apply(
                    name,
                    args,
                    prefix_state,
                    state_ref,
                    prime_state_ref,
                ) {
                    return recursive_call;
                }
                let args_str: Vec<_> = args
                    .iter()
                    .map(|a| {
                        self.expr_to_rust_with_scope(
                            &a.node,
                            prefix_state,
                            state_ref,
                            prime_state_ref,
                        )
                    })
                    .collect();
                format!("/* {}({}) */", name, args_str.join(", "))
            }
        }
    }
}
