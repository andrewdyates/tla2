// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checker module emission: generates `pub mod checker` adapter layer
//! and `impl checker::To<Spec>State` blocks for production-type adapters.

use super::{
    to_pascal_case, to_snake_case, validate_single_line_rust_expr_trimmed,
    validate_single_line_rust_fragment_trimmed, CheckerMapConfig, CodegenError, HashMap,
    RustEmitter, WRITE_TO_STRING_ERR,
};
use std::fmt::Write;

impl<'a> RustEmitter<'a> {
    pub(super) fn emit_checker_module(
        &mut self,
        name: &str,
        invariants: &[&tla_core::ast::OperatorDef],
    ) -> Result<(), CodegenError> {
        let struct_name = to_pascal_case(name);
        let state_name = format!("{}State", struct_name);
        let trait_name = format!("To{}State", struct_name);
        let to_state_fn = format!("to_{}_state", to_snake_case(name));

        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "/// Production-type adapter helpers for {}.",
            name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "pub mod checker {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "    use super::{{{}, {}}};",
            struct_name, state_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    use tla_runtime::StateMachine;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        writeln!(self.out, "    pub trait {} {{", trait_name).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        fn {}(&self) -> {};",
            to_state_fn, state_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        writeln!(
            self.out,
            "    pub fn check_invariants<T: {}>(value: &T) -> bool {{",
            trait_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let state = value.{}();", to_state_fn)
            .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        machine.check_invariant(&state).expect(\"invariant evaluation error\")"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);

        for inv in invariants {
            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "    pub fn check_{}<T: {}>(value: &T) -> bool {{",
                to_snake_case(&inv.name.node),
                trait_name
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        let machine = {};", struct_name)
                .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        let state = value.{}();", to_state_fn)
                .expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "        machine.check_{}(&state)",
                to_snake_case(&inv.name.node)
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        }

        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "    fn violated_invariants_state(machine: &{}, state: &{}) -> Vec<&'static str> {{",
            struct_name, state_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        machine.invariant_names().into_iter().filter(|name| !matches!(machine.check_named_invariant(name, state), Some(true))).collect()"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        writeln!(
            self.out,
            "    pub fn check_init<T: {}>(value: &T) -> Result<(), String> {{",
            trait_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let state = value.{}();", to_state_fn)
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let mut init_count: usize = 0;").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        let mut sample_init_states: Vec<{}> = Vec::new();",
            state_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        if matches!(machine.for_each_init(|s| {{")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            init_count += 1;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            if sample_init_states.len() < 5 {{")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                sample_init_states.push(s.clone());"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            if s == state {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                std::ops::ControlFlow::Break(())")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }} else {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                std::ops::ControlFlow::Continue(())"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        }}), std::ops::ControlFlow::Break(())) {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            Ok(())").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }} else {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            let violated_invariants = violated_invariants_state(&machine, &state);"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            Err(format!(\"invalid init state (state not in Init)\\nstate={{:?}}\\nviolated_invariants={{:?}}\\ninit_count={{}}\\nsample_init_states={{:?}}\", state, violated_invariants, init_count, sample_init_states))"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        writeln!(
            self.out,
            "    fn check_transition_state(machine: &{}, old_state: {}, new_state: {}) -> Result<(), String> {{",
            struct_name, state_name, state_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        if let Some(ok) = machine.is_next(&old_state, &new_state) {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            if ok {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                Ok(())").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }} else {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                let violated_invariants = violated_invariants_state(&machine, &new_state);"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                Err(format!(\"invalid transition (is_next=false)\\nold_state={{:?}}\\nnew_state={{:?}}\\nviolated_invariants={{:?}}\", old_state, new_state, violated_invariants))"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }} else {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            let mut successor_count: usize = 0;")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            let mut sample_successors: Vec<{}> = Vec::new();",
            state_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            if matches!(machine.for_each_next(&old_state, |s| {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                successor_count += 1;").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                if sample_successors.len() < 5 {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                    sample_successors.push(s.clone());"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                if s == new_state {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                    std::ops::ControlFlow::Break(())"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                }} else {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                    std::ops::ControlFlow::Continue(())"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                }}").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            }}), std::ops::ControlFlow::Break(())) {{"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "                Ok(())").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }} else {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                let violated_invariants = violated_invariants_state(&machine, &new_state);"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "                Err(format!(\"invalid transition (new_state not in successors)\\nold_state={{:?}}\\nnew_state={{:?}}\\nviolated_invariants={{:?}}\\nsuccessor_count={{}}\\nsample_successors={{:?}}\", old_state, new_state, violated_invariants, successor_count, sample_successors))"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);

        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "    pub fn check_transition<T: {}>(old: &T, new: &T) -> Result<(), String> {{",
            trait_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let old_state = old.{}();", to_state_fn)
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let new_state = new.{}();", to_state_fn)
            .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        check_transition_state(&machine, old_state, new_state)"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        writeln!(
            self.out,
            "    pub fn check_transition_or_stutter<T: {}>(old: &T, new: &T) -> Result<(), String> {{",
            trait_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let old_state = old.{}();", to_state_fn)
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let new_state = new.{}();", to_state_fn)
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        if old_state == new_state {{").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "            Ok(())").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }} else {{").expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "            check_transition_state(&machine, old_state, new_state)"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        writeln!(
            self.out,
            "    pub fn violated_invariants<T: {}>(value: &T) -> Vec<&'static str> {{",
            trait_name
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let machine = {};", struct_name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "        let state = value.{}();", to_state_fn)
            .expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "        violated_invariants_state(&machine, &state)"
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);

        writeln!(self.out, "}}").expect(WRITE_TO_STRING_ERR);

        Ok(())
    }

    pub(super) fn emit_checker_impls(
        &mut self,
        name: &str,
        variables: &[String],
        checker_map: &CheckerMapConfig,
    ) -> Result<(), CodegenError> {
        if let Some(spec_module) = &checker_map.spec_module {
            if spec_module != name {
                return Err(CodegenError::CheckerMapModuleMismatch {
                    config_module: spec_module.clone(),
                    actual_module: name.to_string(),
                });
            }
        }

        if checker_map.impls.is_empty() {
            return Err(CodegenError::CheckerMapNoImpls);
        }

        let struct_name = to_pascal_case(name);
        let state_name = format!("{}State", struct_name);
        let trait_name = format!("To{}State", struct_name);
        let to_state_fn = format!("to_{}_state", to_snake_case(name));

        let required_fields: Vec<(String, String)> = variables
            .iter()
            .map(|var| (to_snake_case(var), var.clone()))
            .collect();
        let mut key_to_field: HashMap<String, String> = HashMap::new();
        for (field, tla_var) in &required_fields {
            key_to_field.insert(field.clone(), field.clone());
            key_to_field.insert(tla_var.clone(), field.clone());
        }
        let expected_keys_preview = || {
            const LIMIT: usize = 12;
            let total = required_fields.len();
            let mut preview = required_fields
                .iter()
                .take(LIMIT)
                .map(|(field, tla_var)| format!("{field} ({tla_var})"))
                .collect::<Vec<_>>()
                .join(", ");
            if total > LIMIT {
                preview.push_str(&format!(", ... (+{})", total - LIMIT));
            }
            preview
        };

        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(
            self.out,
            "/// Checker adapter impls generated from `tla2 codegen --checker-map`."
        )
        .expect(WRITE_TO_STRING_ERR);

        for (idx, cfg_impl) in checker_map.impls.iter().enumerate() {
            let rust_type =
                validate_single_line_rust_fragment_trimmed("impl rust_type", &cfg_impl.rust_type)?;

            let mut unknown: Vec<String> = Vec::new();
            let mut mapped_fields: HashMap<String, String> = HashMap::new();

            for (k, v) in &cfg_impl.fields {
                let key = k.trim();
                let value = validate_single_line_rust_expr_trimmed(v)?;

                let Some(field) = key_to_field.get(key) else {
                    unknown.push(key.to_string());
                    continue;
                };

                if let Some(prev) = mapped_fields.insert(field.clone(), value.to_string()) {
                    return Err(CodegenError::CheckerMapDuplicateField {
                        index: idx,
                        field: field.clone(),
                        prev,
                        current: value.to_string(),
                    });
                }
            }

            unknown.sort();
            unknown.dedup();
            if !unknown.is_empty() {
                return Err(CodegenError::CheckerMapUnknownFields {
                    index: idx,
                    unknown: unknown.join(", "),
                    expected: expected_keys_preview(),
                });
            }

            for (field, _tla_var) in &required_fields {
                if !mapped_fields.contains_key(field) {
                    return Err(CodegenError::CheckerMapMissingField {
                        index: idx,
                        field: field.clone(),
                    });
                }
            }

            writeln!(self.out).expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "impl checker::{} for {} {{",
                trait_name, rust_type
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(
                self.out,
                "    fn {}(&self) -> {} {{",
                to_state_fn, state_name
            )
            .expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "        {} {{", state_name).expect(WRITE_TO_STRING_ERR);
            for (field, tla_var) in &required_fields {
                let expr = mapped_fields
                    .get(field)
                    .map(|s| s.as_str())
                    .expect("checked missing field mapping above");
                writeln!(
                    self.out,
                    "            {}: {}, // TLA+ VARIABLE: {}",
                    field, expr, tla_var
                )
                .expect(WRITE_TO_STRING_ERR);
            }
            writeln!(self.out, "        }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "    }}").expect(WRITE_TO_STRING_ERR);
            writeln!(self.out, "}}").expect(WRITE_TO_STRING_ERR);
        }

        Ok(())
    }
}
