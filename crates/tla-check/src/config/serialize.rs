// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Configuration serialization: Config::to_cfg_string().

#[cfg(test)]
use super::types::{Config, ConstantValue};
#[cfg(test)]
use std::fmt::Write;

#[cfg(test)]
impl Config {
    /// Write the configuration to TLC .cfg format
    pub fn to_cfg_string(&self) -> String {
        let mut out = String::new();

        if let Some(ref spec) = self.specification {
            let _ = writeln!(out, "SPECIFICATION {}", spec);
        }

        if let Some(ref init) = self.init {
            let _ = writeln!(out, "INIT {}", init);
        }

        if let Some(ref next) = self.next {
            let _ = writeln!(out, "NEXT {}", next);
        }

        for inv in &self.invariants {
            let _ = writeln!(out, "INVARIANT {}", inv);
        }

        for prop in &self.properties {
            let _ = writeln!(out, "PROPERTY {}", prop);
        }

        for (name, value) in &self.constants {
            match value {
                ConstantValue::Value(v) => {
                    let _ = writeln!(out, "CONSTANT {} = {}", name, v);
                }
                ConstantValue::ModelValue => {
                    let _ = writeln!(out, "CONSTANT {} <- [ model value ]", name);
                }
                ConstantValue::ModelValueSet(vs) => {
                    let _ = writeln!(out, "CONSTANT {} <- {{{}}}", name, vs.join(", "));
                }
                ConstantValue::Replacement(r) => {
                    let _ = writeln!(out, "CONSTANT {} <- {}", name, r);
                }
            }
        }

        // Module-scoped config entries.
        //
        // TLC does not require any ordering constraints here, but we iterate deterministically
        // for stable output.
        let mut module_names: Vec<&String> = self
            .module_overrides
            .keys()
            .chain(self.module_assignments.keys())
            .collect();
        module_names.sort();
        module_names.dedup();

        for mod_name in module_names {
            if let Some(map) = self.module_overrides.get(mod_name) {
                let mut keys: Vec<&String> = map.keys().collect();
                keys.sort();
                for k in keys {
                    let rhs = &map[k];
                    let _ = writeln!(out, "CONSTANT {} <- [{}] {}", k, mod_name, rhs);
                }
            }
            if let Some(map) = self.module_assignments.get(mod_name) {
                let mut keys: Vec<&String> = map.keys().collect();
                keys.sort();
                for k in keys {
                    let rhs = &map[k];
                    let _ = writeln!(out, "CONSTANT {} = [{}] {}", k, mod_name, rhs);
                }
            }
        }

        if let Some(ref sym) = self.symmetry {
            let _ = writeln!(out, "SYMMETRY {}", sym);
        }

        for c in &self.constraints {
            let _ = writeln!(out, "CONSTRAINT {}", c);
        }

        for ac in &self.action_constraints {
            let _ = writeln!(out, "ACTION_CONSTRAINT {}", ac);
        }

        if let Some(ref view) = self.view {
            let _ = writeln!(out, "VIEW {}", view);
        }

        if let Some(ref alias) = self.alias {
            let _ = writeln!(out, "ALIAS {}", alias);
        }

        out
    }
}
