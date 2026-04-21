// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::util::{to_pascal_case, to_snake_case};
use super::{CgResult, RustEmitter, WRITE_TO_STRING_ERR};
use std::fmt::Write;
use tla_core::ast::OperatorDef;

impl RustEmitter<'_> {
    pub(in crate::emit) fn emit_proptest(
        &mut self,
        name: &str,
        invariants: &[&OperatorDef],
    ) -> CgResult {
        let struct_name = to_pascal_case(name);

        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "#[cfg(test)]").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "mod tests {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    use super::*;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    use std::collections::HashSet;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        // Test init produces at least one state
        writeln!(self.out, "    #[test]").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    fn test_init_not_empty() {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let init_states = machine.init();").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        assert!(!init_states.is_empty(), \"Init should produce at least one state\");"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        // Test invariants hold in initial states
        if !invariants.is_empty() {
            writeln!(self.out, "    #[test]").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    fn test_init_satisfies_invariants() {{")
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        let machine = {};", struct_name)
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        let init_states = machine.init();")
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        for state in &init_states {{").expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "            if let Some(ok) = machine.check_invariant(state) {{"
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "                assert!(ok, \"Invariant violated in initial state: {{:?}}\", state);").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        }

        // Test bounded BFS exploration
        writeln!(self.out, "    #[test]").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    fn test_bounded_exploration() {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        let mut seen: HashSet<{}State> = HashSet::new();",
            struct_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let mut frontier = machine.init();")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        // Explore up to 1000 states").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let max_states = 1000;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let mut total_states = 0;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        while !frontier.is_empty() && total_states < max_states {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            let state = frontier.pop().expect(\"frontier is non-empty after guard\");"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            if seen.contains(&state) {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                continue;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            seen.insert(state.clone());").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            total_states += 1;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        if !invariants.is_empty() {
            writeln!(self.out, "            // Check invariant").expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "            if let Some(ok) = machine.check_invariant(&state) {{"
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "                assert!(ok, \"Invariant violated in state: {{:?}}\", state);"
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        }

        writeln!(self.out, "            // Generate successors").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            let next_states = machine.next(&state);"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            frontier.extend(next_states);").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        println!(\"Explored {{}} states\", total_states);"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);

        // Test one-step invariant preservation (for each initial state)
        if !invariants.is_empty() {
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    #[test]").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    fn test_next_preserves_invariants() {{")
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        let machine = {};", struct_name)
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        let init_states = machine.init();")
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        for state in &init_states {{").expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "            let next_states = machine.next(state);"
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "            for next_state in &next_states {{")
                .expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "                if let Some(ok) = machine.check_invariant(next_state) {{"
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "                    assert!(ok, \"Invariant violated after transition: {{:?}} -> {{:?}}\", state, next_state);").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "                }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        }

        writeln!(self.out, "}}").expect(WRITE_TO_STRING_ERR);
        Ok(())
    }

    pub(in crate::emit) fn emit_kani_harness(
        &mut self,
        name: &str,
        invariants: &[&OperatorDef],
    ) -> CgResult {
        let struct_name = to_pascal_case(name);

        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "#[cfg(kani)]").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "mod kani_proofs {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    use super::*;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        // Proof that all initial states satisfy invariants
        writeln!(self.out, "    #[kani::proof]").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    fn init_satisfies_invariants() {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let init_states = machine.init();").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        for state in &init_states {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            if let Some(ok) = machine.check_invariant(state) {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                kani::assert(ok, \"Invariant violated in initial state\");"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        // Proof that invariants are preserved by Next
        writeln!(self.out, "    #[kani::proof]").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    #[kani::unwind(5)]").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    fn next_preserves_invariants() {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let init_states = machine.init();").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        if init_states.is_empty() {{ return; }}")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        // Check that if invariant holds in state, it holds in next states"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let idx: usize = kani::any();").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        kani::assume(idx < init_states.len());")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let state = &init_states[idx];").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        // Assume invariant holds in current state"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        if let Some(ok) = machine.check_invariant(state) {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            kani::assume(ok);").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        // Check invariant holds in all next states"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let next_states = machine.next(state);")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        for next_state in &next_states {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            if let Some(ok) = machine.check_invariant(next_state) {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                kani::assert(ok, \"Invariant violated after transition\");"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);

        // Generate individual invariant proofs
        for inv in invariants {
            let inv_name = to_snake_case(&inv.name.node);
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    #[kani::proof]").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    fn {}_holds_initially() {{", inv_name)
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        let machine = {};", struct_name)
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        let init_states = machine.init();")
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        for state in &init_states {{").expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "            kani::assert(machine.check_{}(state), \"{} violated\");",
                inv_name, inv.name.node
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        }

        writeln!(self.out, "}}").expect(WRITE_TO_STRING_ERR);
        Ok(())
    }
}
