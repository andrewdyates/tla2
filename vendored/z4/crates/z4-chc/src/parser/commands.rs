// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Command surface and declaration parsing for the CHC parser.
//!
//! Handles `set-logic`, `declare-rel`/`declare-fun`, `declare-var`,
//! `declare-datatype`/`declare-datatypes`, `rule`, `query`, and `assert`
//! commands. Delegates expression/sort parsing through `self.parse_expr()`
//! and `self.parse_sort()`.

use super::ChcParser;
use crate::expr::{ChcDtConstructor, ChcDtSelector};
use crate::{ChcError, ChcExpr, ChcResult, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use std::sync::Arc;

impl ChcParser {
    /// Parse a single command
    pub(super) fn parse_command(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        if self.pos >= self.input.len() {
            return Ok(());
        }

        self.expect_char('(')?;
        self.skip_whitespace_and_comments();

        let cmd = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        match cmd.as_str() {
            "set-logic" => {
                let logic = self.parse_symbol()?;
                // Accept HORN or other logics that might contain CHC
                if !["HORN", "LIA", "LRA", "ALIA", "AUFLIA", "QF_LIA", "QF_LRA"]
                    .contains(&logic.as_str())
                {
                    tracing::warn!(
                        "Unexpected logic '{logic}', expecting HORN or arithmetic logic"
                    );
                }
            }
            "declare-rel" | "declare-fun" => {
                self.parse_declare_predicate(&cmd)?;
            }
            "declare-var" | "declare-const" => {
                self.parse_declare_var()?;
            }
            "declare-datatype" => {
                self.parse_declare_datatype()?;
            }
            "declare-datatypes" => {
                self.parse_declare_datatypes()?;
            }
            "rule" => {
                self.problem.set_fixedpoint_format();
                self.parse_rule()?;
            }
            "query" => {
                self.problem.set_fixedpoint_format();
                self.parse_query()?;
            }
            "check-sat" | "exit" | "set-info" | "set-option" => {
                // Skip until closing paren
                let mut depth = 1;
                while depth > 0 && self.pos < self.input.len() {
                    match self.current_char() {
                        Some('(') => depth += 1,
                        Some(')') => depth -= 1,
                        _ => {}
                    }
                    self.pos += 1;
                }
                return Ok(());
            }
            "assert" => {
                // Parse an assertion (may be a Horn clause)
                self.skip_whitespace_and_comments();
                let expr = self.parse_expr()?;
                self.add_assertion_as_clause(expr)?;
            }
            _ => {
                // Skip unknown command
                tracing::warn!("Unknown command: {cmd}");
                let mut depth = 1;
                while depth > 0 && self.pos < self.input.len() {
                    match self.current_char() {
                        Some('(') => depth += 1,
                        Some(')') => depth -= 1,
                        _ => {}
                    }
                    self.pos += 1;
                }
                return Ok(());
            }
        }

        self.skip_whitespace_and_comments();
        self.expect_char(')')?;
        Ok(())
    }

    /// Parse a declare-rel or declare-fun command
    fn parse_declare_predicate(&mut self, cmd: &str) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        let name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        // Parse argument sorts
        self.expect_char('(')?;
        let mut sorts = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            sorts.push(self.parse_sort()?);
        }
        self.expect_char(')')?;

        // For declare-fun, also parse return sort
        if cmd == "declare-fun" {
            self.skip_whitespace_and_comments();
            let ret_sort = self.parse_sort()?;
            if ret_sort != ChcSort::Bool {
                // Non-Bool functions are not supported - fail with error (fixes #352)
                return Err(ChcError::Parse(format!(
                    "Non-predicate function declaration: '{name}' with return sort {ret_sort:?}. \
                     Only Bool-returning functions (predicates) are supported in z4-chc."
                )));
            }
        }

        // Register predicate
        let pred_id = self.problem.declare_predicate(&name, sorts.clone());
        self.predicates.insert(name, (pred_id, sorts));

        Ok(())
    }

    /// Parse a declare-var command
    fn parse_declare_var(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        let name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();
        let sort = self.parse_sort()?;

        self.variables.insert(name, sort);
        Ok(())
    }

    /// Parse a declare-datatype command
    /// Syntax: (declare-datatype <name> ((<ctor> (<selector> <sort>)*)*))
    /// Example: (declare-datatype Tuple_bv32_bool ((mk (fld_0 (_ BitVec 32)) (fld_1 Bool))))
    fn parse_declare_datatype(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();

        // Parse datatype name
        let datatype_name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        // Register the name first so recursive sort references resolve during parsing.
        self.declared_sorts.insert(datatype_name.clone());

        // Pass 1: Parse constructor/selector structure, collecting metadata.
        // We need the parsed sorts before we can build ChcSort::Datatype, so we
        // collect (ctor_name, selectors) tuples and register functions after.
        let mut parsed_ctors: Vec<(String, Vec<(String, ChcSort)>)> = Vec::new();

        self.expect_char('(')?;

        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }

            // Parse single constructor: (<ctor> (<selector> <sort>)*)
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();
            let ctor_name = self.parse_symbol()?;
            self.skip_whitespace_and_comments();

            // Parse selectors
            let mut selectors: Vec<(String, ChcSort)> = Vec::new();
            while self.peek_char() == Some('(') {
                self.expect_char('(')?;
                self.skip_whitespace_and_comments();
                let selector_name = self.parse_symbol()?;
                self.skip_whitespace_and_comments();
                let selector_sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                self.expect_char(')')?;
                self.skip_whitespace_and_comments();

                selectors.push((selector_name, selector_sort));
            }

            self.skip_whitespace_and_comments();
            self.expect_char(')')?;

            parsed_ctors.push((ctor_name, selectors));
        }

        self.expect_char(')')?;

        // Pass 2: Build ChcSort::Datatype with full metadata.
        let chc_constructors: Vec<ChcDtConstructor> = parsed_ctors
            .iter()
            .map(|(ctor_name, sels)| ChcDtConstructor {
                name: ctor_name.clone(),
                selectors: sels
                    .iter()
                    .map(|(sel_name, sel_sort)| ChcDtSelector {
                        name: sel_name.clone(),
                        sort: sel_sort.clone(),
                    })
                    .collect(),
            })
            .collect();

        let datatype_sort = ChcSort::Datatype {
            name: datatype_name.clone(),
            constructors: Arc::new(chc_constructors),
        };

        // Propagate DT definition to the problem so SmtContext can emit
        // declare-datatype commands for the executor adapter (#7016).
        self.problem
            .add_datatype_def(datatype_name.clone(), parsed_ctors.clone());

        // Store the full sort for parse_sort lookups.
        self.declared_datatype_sorts
            .insert(datatype_name, datatype_sort.clone());

        // Pass 3: Register constructors, selectors, and testers in self.functions.
        for (ctor_name, selectors) in &parsed_ctors {
            // Register each selector: datatype -> field_sort
            let mut selector_sorts: Vec<ChcSort> = Vec::new();
            for (sel_name, sel_sort) in selectors {
                self.register_function(
                    sel_name.clone(),
                    sel_sort.clone(),
                    vec![datatype_sort.clone()],
                );
                selector_sorts.push(sel_sort.clone());
            }

            // Register constructor: (field_sorts) -> datatype
            self.register_function(ctor_name.clone(), datatype_sort.clone(), selector_sorts);

            // Register tester: datatype -> Bool
            let tester_name = format!("is-{ctor_name}");
            self.register_function(tester_name, ChcSort::Bool, vec![datatype_sort.clone()]);
        }
        Ok(())
    }

    /// Parse a declare-datatypes command (plural form for mutually recursive DTs).
    /// Syntax: (declare-datatypes ((T1 0) (T2 0) ...) ((ctors1) (ctors2) ...))
    /// Example: (declare-datatypes ((Tree 0) (Forest 0))
    ///            (((leaf (val Int)) (node (children Forest)))
    ///             ((nil) (cons (head Tree) (tail Forest)))))
    fn parse_declare_datatypes(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();

        // Step 1: Parse sort declarations: ((T1 arity1) (T2 arity2) ...)
        self.expect_char('(')?;
        let mut sort_names: Vec<String> = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();
            let name = self.parse_symbol()?;
            self.skip_whitespace_and_comments();
            // Parse arity (ignored for now — z4-chc doesn't support parametric DTs)
            let _arity = self.parse_numeral()?;
            self.skip_whitespace_and_comments();
            self.expect_char(')')?;
            sort_names.push(name);
        }
        self.expect_char(')')?;
        self.skip_whitespace_and_comments();

        // Step 2: Register ALL names before parsing constructors (mutual recursion).
        for name in &sort_names {
            self.declared_sorts.insert(name.clone());
        }

        // Step 3: Parse constructor lists: ((ctors_for_T1) (ctors_for_T2) ...)
        self.expect_char('(')?;
        let mut all_parsed_ctors: Vec<Vec<(String, Vec<(String, ChcSort)>)>> = Vec::new();
        for _ in &sort_names {
            self.skip_whitespace_and_comments();
            // Parse one datatype's constructors: ((ctor1 ...) (ctor2 ...))
            self.expect_char('(')?;
            let mut parsed_ctors: Vec<(String, Vec<(String, ChcSort)>)> = Vec::new();
            loop {
                self.skip_whitespace_and_comments();
                if self.peek_char() == Some(')') {
                    break;
                }
                self.expect_char('(')?;
                self.skip_whitespace_and_comments();
                let ctor_name = self.parse_symbol()?;
                self.skip_whitespace_and_comments();

                let mut selectors: Vec<(String, ChcSort)> = Vec::new();
                while self.peek_char() == Some('(') {
                    self.expect_char('(')?;
                    self.skip_whitespace_and_comments();
                    let selector_name = self.parse_symbol()?;
                    self.skip_whitespace_and_comments();
                    let selector_sort = self.parse_sort()?;
                    self.skip_whitespace_and_comments();
                    self.expect_char(')')?;
                    self.skip_whitespace_and_comments();
                    selectors.push((selector_name, selector_sort));
                }

                self.skip_whitespace_and_comments();
                self.expect_char(')')?;
                parsed_ctors.push((ctor_name, selectors));
            }
            self.expect_char(')')?;
            all_parsed_ctors.push(parsed_ctors);
        }
        self.expect_char(')')?;

        if sort_names.len() != all_parsed_ctors.len() {
            return Err(ChcError::Parse(
                "declare-datatypes: sort count does not match constructor list count".into(),
            ));
        }

        // Step 4: Build ChcSort::Datatype and register constructors/selectors/testers
        // for each datatype.
        for (datatype_name, parsed_ctors) in sort_names.into_iter().zip(all_parsed_ctors) {
            let chc_constructors: Vec<ChcDtConstructor> = parsed_ctors
                .iter()
                .map(|(ctor_name, sels)| ChcDtConstructor {
                    name: ctor_name.clone(),
                    selectors: sels
                        .iter()
                        .map(|(sel_name, sel_sort)| ChcDtSelector {
                            name: sel_name.clone(),
                            sort: sel_sort.clone(),
                        })
                        .collect(),
                })
                .collect();

            let datatype_sort = ChcSort::Datatype {
                name: datatype_name.clone(),
                constructors: Arc::new(chc_constructors),
            };

            self.problem
                .add_datatype_def(datatype_name.clone(), parsed_ctors.clone());

            self.declared_datatype_sorts
                .insert(datatype_name, datatype_sort.clone());

            // Register constructors, selectors, and testers.
            for (ctor_name, selectors) in &parsed_ctors {
                let mut selector_sorts: Vec<ChcSort> = Vec::new();
                for (sel_name, sel_sort) in selectors {
                    self.register_function(
                        sel_name.clone(),
                        sel_sort.clone(),
                        vec![datatype_sort.clone()],
                    );
                    selector_sorts.push(sel_sort.clone());
                }
                self.register_function(ctor_name.clone(), datatype_sort.clone(), selector_sorts);
                let tester_name = format!("is-{ctor_name}");
                self.register_function(tester_name, ChcSort::Bool, vec![datatype_sort.clone()]);
            }
        }
        Ok(())
    }

    /// Parse a rule command
    fn parse_rule(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        let expr = self.parse_expr()?;

        // Convert expression to Horn clause
        self.add_expr_as_clause(expr)?;
        Ok(())
    }

    /// Parse a query command
    fn parse_query(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();

        // Query can be a predicate name or an expression
        if self.peek_char() == Some('(') {
            // Expression form
            let expr = self.parse_expr()?;
            // Extract predicates/constraints so the solver can reason about the query predicate.
            // Add as a clause: (preds /\ constraint) => false
            let (preds, constraint) = self.extract_body_parts(&expr);
            let body = if preds.is_empty() && constraint.is_none() {
                ClauseBody::constraint(ChcExpr::Bool(true))
            } else {
                ClauseBody::new(preds, constraint)
            };
            let clause = HornClause::new(body, ClauseHead::False);
            self.problem.add_clause(clause);
        } else {
            // Predicate name form
            let pred_name = self.parse_symbol()?;
            if let Some((pred_id, sorts)) = self.predicates.get(&pred_name).cloned() {
                // Create a query: Pred(x1, ..., xn) => false
                let args: Vec<ChcExpr> = sorts
                    .iter()
                    .enumerate()
                    .map(|(i, sort)| ChcExpr::var(ChcVar::new(format!("_qv{i}"), sort.clone())))
                    .collect();
                let clause = HornClause::new(
                    ClauseBody::new(vec![(pred_id, args)], None),
                    ClauseHead::False,
                );
                self.problem.add_clause(clause);
            } else {
                return Err(ChcError::Parse(format!(
                    "Unknown predicate in query: {pred_name}"
                )));
            }
        }

        Ok(())
    }
}
