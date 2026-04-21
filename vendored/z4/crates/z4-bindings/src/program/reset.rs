// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Z4Program state accessors and command-reset logic.

use super::Z4Program;
use crate::constraint::Constraint;

impl Z4Program {
    /// Get all commands (used by execute_direct feature).
    #[must_use]
    pub fn commands(&self) -> &[Constraint] {
        &self.commands
    }

    /// Get the current context level.
    #[must_use]
    pub fn context_level(&self) -> u32 {
        self.context_level
    }

    /// Clear all commands but keep declarations.
    ///
    /// Removes all assertions, check-sat, push/pop, and other non-declaration
    /// commands. Re-adds all tracked declarations: datatypes, constants,
    /// functions, CHC relations, and CHC variables.
    pub fn clear_commands(&mut self) {
        self.commands.clear();
        self.context_level = 0;
        // Re-add datatype declarations first (other declarations may reference these sorts)
        for dt in self.declared_datatypes.values() {
            self.commands.push(Constraint::declare_datatype(dt.clone()));
        }
        // Re-add constant declarations
        for (name, sort) in &self.declared_vars {
            self.commands
                .push(Constraint::declare_const(name.clone(), sort.clone()));
        }
        // Re-add function declarations
        for (name, arg_sorts, return_sort) in &self.declared_funs {
            self.commands.push(Constraint::declare_fun(
                name.clone(),
                arg_sorts.clone(),
                return_sort.clone(),
            ));
        }
        // Re-add CHC relation declarations
        for (name, arg_sorts) in &self.declared_rels {
            self.commands
                .push(Constraint::declare_rel(name.clone(), arg_sorts.clone()));
        }
        // Re-add CHC variable declarations
        for (name, sort) in &self.declared_chc_vars {
            self.commands
                .push(Constraint::declare_var(name.clone(), sort.clone()));
        }
    }
}
