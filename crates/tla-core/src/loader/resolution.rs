// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Module ordering for semantic resolution and model checking.

use std::collections::{HashSet, VecDeque};

use super::error::LoadedModule;
use super::ModuleLoader;
use crate::ast::{Module, Unit};

impl ModuleLoader {
    /// Get a loaded module from the cache
    pub fn get(&self, name: &str) -> Option<&LoadedModule> {
        self.cache.get(name)
    }

    /// Get all loaded modules
    pub(crate) fn loaded_modules(&self) -> impl Iterator<Item = (&str, &LoadedModule)> {
        self.cache.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Compute module lists suitable for TLC-style semantic name resolution.
    ///
    /// This distinguishes:
    /// - `EXTENDS M`: imports M's constants/variables/operators into the unqualified scope.
    /// - a standalone `INSTANCE M`: imports only M's *operators* into the unqualified scope.
    ///
    /// Named instances (`I == INSTANCE M ...`) are *not* part of the unqualified import scope and
    /// must not be treated like `EXTENDS`, or they can spuriously introduce duplicate-definition
    /// errors (e.g., when both an EXTENDS'd module and a named-instance dependency define the same
    /// constant).
    ///
    /// This function assumes relevant modules have already been loaded into the cache (e.g. via
    /// `load_extends` / `load_instances`).
    pub fn modules_for_semantic_resolution<'a>(
        &'a self,
        module: &Module,
    ) -> (Vec<&'a Module>, Vec<&'a Module>) {
        // Compute the transitive EXTENDS closure (non-stdlib modules are those present in cache),
        // in a deterministic order that matches TLC's "first definition wins" conflict handling.
        //
        // TLC processes a module's EXTENDS list in source order; each extendee has already merged
        // its own EXTENDS list into its context before the current module merges it. This means
        // transitive extendees' symbols are effectively imported before their direct extenders'.
        let mut extends_seen: HashSet<String> = HashSet::new();
        let mut extends_order: Vec<String> = Vec::new();

        fn visit_extends(
            loader: &ModuleLoader,
            name: &str,
            seen: &mut HashSet<String>,
            out: &mut Vec<String>,
        ) {
            if !seen.insert(name.to_string()) {
                return;
            }
            let Some(loaded) = loader.get(name) else {
                return;
            };
            for ext in &loaded.module.extends {
                visit_extends(loader, &ext.node, seen, out);
            }
            out.push(name.to_string());
        }

        for ext in &module.extends {
            visit_extends(self, &ext.node, &mut extends_seen, &mut extends_order);
        }

        fn collect_standalone_instances(m: &Module, out: &mut VecDeque<String>) {
            for unit in &m.units {
                if let Unit::Instance(inst) = &unit.node {
                    out.push_back(inst.module.node.clone());
                }
            }
        }

        // Compute transitive closure of standalone INSTANCE imports from the main module and its
        // EXTENDS closure, in deterministic discovery order.
        let mut instance_seen: HashSet<String> = HashSet::new();
        let mut instance_order: Vec<String> = Vec::new();
        let mut queue: VecDeque<String> = VecDeque::new();

        collect_standalone_instances(module, &mut queue);
        for name in &extends_order {
            if let Some(loaded) = self.get(name) {
                collect_standalone_instances(&loaded.module, &mut queue);
            }
        }

        while let Some(name) = queue.pop_front() {
            if !instance_seen.insert(name.clone()) {
                continue;
            }
            instance_order.push(name.clone());
            if let Some(loaded) = self.get(&name) {
                collect_standalone_instances(&loaded.module, &mut queue);
            }
        }

        // If a module is reached via EXTENDS, treat it as extended (constants/vars/operators)
        // even if it also appears in the INSTANCE-import closure.
        let extends_set: HashSet<&str> = extends_order
            .iter()
            .map(std::string::String::as_str)
            .collect();
        instance_order.retain(|name| !extends_set.contains(name.as_str()));

        let extended_modules: Vec<&Module> = extends_order
            .iter()
            .filter_map(|name| self.get(name.as_str()).map(|l| &l.module))
            .collect();

        let instanced_modules: Vec<&Module> = instance_order
            .iter()
            .filter_map(|name| self.get(name.as_str()).map(|l| &l.module))
            .collect();

        (extended_modules, instanced_modules)
    }

    /// Compute a deterministic module slice suitable for model checking.
    ///
    /// The returned list is intended to be passed to `ModelChecker::new_with_extends` (and the
    /// adaptive/parallel equivalents). Its prefix ordering matches TLC's unqualified import scope:
    /// `EXTENDS` modules first (in TLC-shaped deterministic order), followed by standalone
    /// `INSTANCE` imports. Any remaining loaded modules are appended in deterministic module-name
    /// order for reproducible diagnostics.
    ///
    /// This function assumes relevant dependencies have already been loaded into the cache (e.g.
    /// via `load_extends` and `load_instances`).
    pub fn modules_for_model_checking<'a>(&'a self, module: &Module) -> Vec<&'a Module> {
        let (extends, instances) = self.modules_for_semantic_resolution(module);

        let mut out = Vec::new();
        let mut seen: HashSet<&'a str> = HashSet::new();

        for m in extends.into_iter().chain(instances) {
            let name = m.name.node.as_str();
            if seen.insert(name) {
                out.push(m);
            }
        }

        let main_name = module.name.node.as_str();
        let mut rest: Vec<(&'a str, &'a Module)> = self
            .loaded_modules()
            .filter_map(|(name, loaded)| {
                if name == main_name || seen.contains(name) {
                    return None;
                }
                Some((name, &loaded.module))
            })
            .collect();
        rest.sort_by(|(a, _), (b, _)| a.cmp(b));
        out.extend(rest.into_iter().map(|(_, m)| m));

        out
    }
}
