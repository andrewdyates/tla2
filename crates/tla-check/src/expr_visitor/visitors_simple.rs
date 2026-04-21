// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.
//
// Simple ExprVisitor implementations — re-exported from tla-core root.
//
// The canonical implementation lives in tla-core (expr_visitors module).
// This module re-exports via tla_core root so existing imports continue to work.
// Items imported directly in other tla-check files (collect_conjuncts_v,
// apply_substitutions_v, expr_contains_temporal_v, expr_mentions_name_v) are
// not duplicated here.

pub use tla_core::{
    expr_contains_any_prime_v, expr_contains_enabled_v, expr_contains_operator_application_v,
    expr_contains_prime_not_assignment_v, expr_contains_prime_v, expr_references_state_vars_v,
    get_primed_var_refs_v, is_guard_expression_v, is_simple_prime_var,
};

#[cfg(test)]
pub use tla_core::{
    collect_bound_names_v, expr_contains_exists_v, expr_contains_ident_v,
    expr_contains_primed_param_v, expr_has_any_prime_legacy_v, expr_has_free_var_in_set_v,
};
