// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Tests use the deprecated panicking convenience API; migration tracked in z4#6183.
#![allow(deprecated)]

mod test_api_health;
mod test_bool_eq;
mod test_bv;
mod test_bv_api_simplification;
mod test_core;
mod test_counterexample_minimization;
mod test_fp;
mod test_model_access;
mod test_model_parse_fp_dt;
mod test_proof_access;
mod test_proof_artifact;
mod test_solver_scope;
mod test_solving_assumptions;
mod test_solving_controls;
mod test_strings;
mod test_try_check_sat;
mod test_type_logic;
mod test_type_model_value;
mod test_unsat_core;
