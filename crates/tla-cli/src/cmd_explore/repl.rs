// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Terminal REPL for interactive TLA+ state-space exploration.
//!
//! Provides commands: `init`, `step`, `pick`, `eval`, `inv`, `back`, `forward`,
//! `state`, `trace`, `actions`, `help`, `quit`.

use rustc_hash::FxHashMap;
use std::collections::HashMap;
use std::io::{self, BufRead, Write as IoWrite};
use std::sync::Arc;

use anyhow::Result;

use tla_check::{InteractiveServer, StateSnapshot};

// ---------------------------------------------------------------------------
// State history for back/forward navigation
// ---------------------------------------------------------------------------

/// Keeps a linear history of explored states with a cursor for back/forward.
struct StateHistory {
    /// All visited states in order. Each entry is (state_id, snapshot).
    entries: Vec<StateSnapshot>,
    /// Current position in `entries` (0-indexed). `None` if history is empty.
    cursor: Option<usize>,
}

impl StateHistory {
    fn new() -> Self {
        Self {
            entries: Vec::new(),
            cursor: None,
        }
    }

    /// Push a new state, discarding any forward history beyond the cursor.
    fn push(&mut self, snap: StateSnapshot) {
        if let Some(pos) = self.cursor {
            self.entries.truncate(pos + 1);
        }
        self.entries.push(snap);
        self.cursor = Some(self.entries.len() - 1);
    }

    /// Move back one step. Returns the state at the new position or `None`.
    fn back(&mut self) -> Option<&StateSnapshot> {
        let pos = self.cursor?;
        if pos == 0 {
            return None;
        }
        self.cursor = Some(pos - 1);
        self.entries.get(pos - 1)
    }

    /// Move forward one step. Returns the state at the new position or `None`.
    fn forward(&mut self) -> Option<&StateSnapshot> {
        let pos = self.cursor?;
        if pos + 1 >= self.entries.len() {
            return None;
        }
        self.cursor = Some(pos + 1);
        self.entries.get(pos + 1)
    }

    /// Current state snapshot, if any.
    fn current(&self) -> Option<&StateSnapshot> {
        self.cursor.and_then(|pos| self.entries.get(pos))
    }

    /// Current cursor position and total length, for display.
    fn position_info(&self) -> (usize, usize) {
        (self.cursor.map_or(0, |c| c + 1), self.entries.len())
    }
}

// ---------------------------------------------------------------------------
// Pretty-printing
// ---------------------------------------------------------------------------

/// Print a state snapshot with one variable per line, sorted alphabetically.
fn pretty_print_state(snap: &StateSnapshot) {
    println!("State #{}", snap.state_id);
    let mut vars: Vec<(&String, &serde_json::Value)> = snap.variables.iter().collect();
    vars.sort_by_key(|(k, _)| k.as_str());
    let max_name_len = vars.iter().map(|(k, _)| k.len()).max().unwrap_or(0);
    for (name, value) in &vars {
        let formatted = format_json_value(value);
        println!("  {:<width$} = {}", name, formatted, width = max_name_len);
    }
}

/// Format a serde_json::Value in TLA+ style rather than raw JSON.
fn format_json_value(v: &serde_json::Value) -> String {
    match v {
        serde_json::Value::Null => "UNDEFINED".to_string(),
        serde_json::Value::Bool(b) => {
            if *b {
                "TRUE".to_string()
            } else {
                "FALSE".to_string()
            }
        }
        serde_json::Value::Number(n) => n.to_string(),
        serde_json::Value::String(s) => format!("\"{s}\""),
        serde_json::Value::Array(elems) => {
            // Check if this looks like a function (array of 2-element arrays).
            let is_function = !elems.is_empty()
                && elems
                    .iter()
                    .all(|e| matches!(e, serde_json::Value::Array(pair) if pair.len() == 2));
            if is_function {
                let pairs: Vec<String> = elems
                    .iter()
                    .map(|pair| {
                        if let serde_json::Value::Array(kv) = pair {
                            format!(
                                "{} :> {}",
                                format_json_value(&kv[0]),
                                format_json_value(&kv[1])
                            )
                        } else {
                            format_json_value(pair)
                        }
                    })
                    .collect();
                format!("({})", pairs.join(" @@ "))
            } else {
                let inner: Vec<String> = elems.iter().map(format_json_value).collect();
                format!("{{{}}}", inner.join(", "))
            }
        }
        serde_json::Value::Object(map) => {
            // Check for interval representation.
            if let (Some(lo), Some(hi)) = (map.get("lo"), map.get("hi")) {
                return format!("{}..{}", format_json_value(lo), format_json_value(hi));
            }
            let fields: Vec<String> = map
                .iter()
                .map(|(k, val)| format!("{k} |-> {}", format_json_value(val)))
                .collect();
            format!("[{}]", fields.join(", "))
        }
    }
}

/// Print a numbered list of state snapshots (for init/step results).
fn print_state_list(label: &str, snapshots: &[StateSnapshot]) {
    if snapshots.is_empty() {
        println!("{label}: (none)");
        return;
    }
    println!("{label}: {} state(s)", snapshots.len());
    for (i, snap) in snapshots.iter().enumerate() {
        println!();
        println!("[{i}] State #{}", snap.state_id);
        let mut vars: Vec<(&String, &serde_json::Value)> = snap.variables.iter().collect();
        vars.sort_by_key(|(k, _)| k.as_str());
        let max_name_len = vars.iter().map(|(k, _)| k.len()).max().unwrap_or(0);
        for (name, value) in &vars {
            let formatted = format_json_value(value);
            println!("    {:<width$} = {}", name, formatted, width = max_name_len);
        }
    }
}

// ---------------------------------------------------------------------------
// Help text
// ---------------------------------------------------------------------------

fn print_help() {
    println!(
        "\
TLA2 Explore REPL -- Interactive State-Space Explorer

Commands:
  init                     Compute initial states and pick the first one.
  state                    Show the current state.
  step                     Compute successors of the current state.
  step <n>                 Compute successors, then pick successor #n.
  pick <n>                 Pick state #n from the last step/init result.
  actions                  Show enabled actions with their successors.
  eval <expr>              Evaluate a TLA+ expression in the current state.
  inv                      Check all configured invariants on the current state.
  inv <name>               Check a specific invariant by operator name.
  back                     Navigate to the previous state in history.
  forward                  Navigate to the next state in history.
  trace                    Show the full exploration trace (history).
  reset                    Clear history and start over (re-runs init).
  help, ?                  Show this help message.
  quit, exit, q            Exit the REPL.

Symbolic exploration (requires z4 feature):
  symbolic                 Switch to symbolic (SMT-based) exploration mode.
  concrete                 Switch back to concrete exploration mode.
  rollback                 Undo the last symbolic transition (solver pop).
  assume <var>=<value>     Assert a concrete variable value in symbolic mode.
  next_model               Get an alternate satisfying assignment.
  compact                  Compact solver state (extract + reset at depth 0).

Tips:
  - After `init` or `step`, use `pick <n>` to select a specific state.
  - `step 0` is a shortcut for `step` followed by `pick 0`.
  - `back` and `forward` let you navigate the exploration history.
  - `eval` can evaluate any TLA+ expression using current state variables.
  - Invariants from the .cfg file are checked automatically unless --no-invariants.
  - Use `symbolic` to switch to SMT-based exploration for constraint solving."
    );
}

// ---------------------------------------------------------------------------
// REPL loop
// ---------------------------------------------------------------------------

pub(crate) fn run_repl(
    module: Arc<tla_core::ast::Module>,
    config: tla_check::Config,
    engine: tla_check::ServerExploreMode,
    max_symbolic_depth: usize,
    no_invariants: bool,
) -> Result<()> {
    let invariant_names: Vec<String> = config.invariants.clone();
    let mut server = InteractiveServer::with_mode(module, config, engine, max_symbolic_depth);
    let mut history = StateHistory::new();
    // Cache the last set of states returned by init/step for `pick`.
    let mut last_results: Vec<StateSnapshot> = Vec::new();

    println!("TLA2 Explore REPL (type 'help' for commands, 'quit' to exit)");
    println!();

    // Auto-initialize.
    match do_init(&mut server) {
        Ok(states) => {
            print_state_list("Initial states", &states);
            if let Some(first) = states.first() {
                history.push(first.clone());
                println!();
                println!(
                    "Picked state #{}. Use 'pick <n>' to choose another.",
                    first.state_id
                );
                if !no_invariants {
                    check_invariants_quiet(&mut server, first.state_id, &invariant_names);
                }
            }
            last_results = states;
        }
        Err(e) => {
            eprintln!("Error computing initial states: {e}");
            eprintln!("Use 'init' to retry after fixing the spec.");
        }
    }

    let stdin = io::stdin();
    let mut reader = stdin.lock();
    let mut line_buf = String::new();

    loop {
        // Prompt with position info.
        let (pos, total) = history.position_info();
        if total > 0 {
            print!("[{pos}/{total}] explore> ");
        } else {
            print!("explore> ");
        }
        io::stdout().flush().ok();

        line_buf.clear();
        match reader.read_line(&mut line_buf) {
            Ok(0) => {
                // EOF (Ctrl-D).
                println!();
                break;
            }
            Ok(_) => {}
            Err(e) => {
                eprintln!("Read error: {e}");
                break;
            }
        }

        let trimmed = line_buf.trim();
        if trimmed.is_empty() {
            continue;
        }

        // Parse command and argument.
        let (cmd, arg) = match trimmed.split_once(char::is_whitespace) {
            Some((c, a)) => (c, a.trim()),
            None => (trimmed, ""),
        };

        match cmd {
            "help" | "?" => print_help(),
            "quit" | "exit" | "q" => break,

            "init" => match do_init(&mut server) {
                Ok(states) => {
                    print_state_list("Initial states", &states);
                    if let Some(first) = states.first() {
                        history.push(first.clone());
                        println!();
                        println!(
                            "Picked state #{}. Use 'pick <n>' to choose another.",
                            first.state_id
                        );
                        if !no_invariants {
                            check_invariants_quiet(&mut server, first.state_id, &invariant_names);
                        }
                    }
                    last_results = states;
                }
                Err(e) => eprintln!("Error: {e}"),
            },

            "state" => {
                if let Some(snap) = history.current() {
                    pretty_print_state(snap);
                } else {
                    eprintln!("No current state. Run 'init' first.");
                }
            }

            "step" => {
                let auto_pick: Option<usize> = if arg.is_empty() {
                    None
                } else {
                    match arg.parse::<usize>() {
                        Ok(n) => Some(n),
                        Err(_) => {
                            eprintln!("Invalid index: {arg}. Usage: step [<n>]");
                            continue;
                        }
                    }
                };

                if let Some(snap) = history.current() {
                    let state_id = snap.state_id;
                    match do_step(&mut server, state_id) {
                        Ok(successors) => {
                            print_state_list("Successors", &successors);
                            if successors.is_empty() {
                                println!("Deadlock: no successor states.");
                            } else if let Some(idx) = auto_pick {
                                if idx < successors.len() {
                                    let picked = &successors[idx];
                                    history.push(picked.clone());
                                    println!();
                                    println!("Picked state #{}.", picked.state_id);
                                    if !no_invariants {
                                        check_invariants_quiet(
                                            &mut server,
                                            picked.state_id,
                                            &invariant_names,
                                        );
                                    }
                                } else {
                                    eprintln!(
                                        "Index {idx} out of range (0..{}). Use 'pick <n>'.",
                                        successors.len()
                                    );
                                }
                            }
                            last_results = successors;
                        }
                        Err(e) => eprintln!("Error computing successors: {e}"),
                    }
                } else {
                    eprintln!("No current state. Run 'init' first.");
                }
            }

            "pick" => {
                if arg.is_empty() {
                    eprintln!("Usage: pick <n>");
                    continue;
                }
                match arg.parse::<usize>() {
                    Ok(idx) => {
                        if idx < last_results.len() {
                            let picked = &last_results[idx];
                            history.push(picked.clone());
                            pretty_print_state(picked);
                            if !no_invariants {
                                check_invariants_quiet(
                                    &mut server,
                                    picked.state_id,
                                    &invariant_names,
                                );
                            }
                        } else if last_results.is_empty() {
                            eprintln!("No states to pick from. Run 'init' or 'step' first.");
                        } else {
                            eprintln!("Index {idx} out of range (0..{})", last_results.len());
                        }
                    }
                    Err(_) => eprintln!("Invalid index: {arg}. Usage: pick <n>"),
                }
            }

            "actions" => {
                if let Some(snap) = history.current() {
                    let state_id = snap.state_id;
                    match do_step(&mut server, state_id) {
                        Ok(successors) => {
                            if successors.is_empty() {
                                println!("No enabled actions (deadlock).");
                            } else {
                                println!("Enabled actions: {} successor(s)", successors.len());
                                for (i, succ) in successors.iter().enumerate() {
                                    // Show which variables changed.
                                    let changes = diff_states(&snap.variables, &succ.variables);
                                    println!();
                                    if changes.is_empty() {
                                        println!(
                                            "[{i}] State #{} (stuttering step)",
                                            succ.state_id
                                        );
                                    } else {
                                        println!("[{i}] State #{}", succ.state_id);
                                        for (var, old_val, new_val) in &changes {
                                            println!(
                                                "    {var}: {} -> {}",
                                                format_json_value(old_val),
                                                format_json_value(new_val)
                                            );
                                        }
                                    }
                                }
                            }
                            last_results = successors;
                        }
                        Err(e) => eprintln!("Error computing successors: {e}"),
                    }
                } else {
                    eprintln!("No current state. Run 'init' first.");
                }
            }

            "eval" => {
                if arg.is_empty() {
                    eprintln!("Usage: eval <expression>");
                    continue;
                }
                if let Some(snap) = history.current() {
                    let state_id = snap.state_id;
                    match do_eval(&mut server, state_id, arg) {
                        Ok(result) => println!("{}", format_json_value(&result)),
                        Err(e) => eprintln!("Eval error: {e}"),
                    }
                } else {
                    eprintln!("No current state. Run 'init' first.");
                }
            }

            "inv" => {
                if let Some(snap) = history.current() {
                    let state_id = snap.state_id;
                    if arg.is_empty() {
                        // Check all configured invariants.
                        if invariant_names.is_empty() {
                            println!("No invariants configured in the .cfg file.");
                            println!("Use 'inv <name>' to check a specific operator.");
                        } else {
                            check_invariants_verbose(&mut server, state_id, &invariant_names);
                        }
                    } else {
                        // Check a specific invariant.
                        check_invariant_single(&mut server, state_id, arg);
                    }
                } else {
                    eprintln!("No current state. Run 'init' first.");
                }
            }

            "back" => {
                if let Some(snap) = history.back() {
                    let snap = snap.clone();
                    pretty_print_state(&snap);
                } else {
                    eprintln!("Already at the beginning of history.");
                }
            }

            "forward" => {
                if let Some(snap) = history.forward() {
                    let snap = snap.clone();
                    pretty_print_state(&snap);
                } else {
                    eprintln!("Already at the end of history.");
                }
            }

            "trace" => {
                if history.entries.is_empty() {
                    eprintln!("No exploration history. Run 'init' first.");
                } else {
                    let (cur_pos, total) = history.position_info();
                    println!("Exploration trace ({total} state(s), cursor at {cur_pos}):");
                    for (i, snap) in history.entries.iter().enumerate() {
                        let marker = if Some(i) == history.cursor {
                            " <-- current"
                        } else {
                            ""
                        };
                        println!();
                        println!("[{i}] State #{}{marker}", snap.state_id);
                        let mut vars: Vec<(&String, &serde_json::Value)> =
                            snap.variables.iter().collect();
                        vars.sort_by_key(|(k, _)| k.as_str());
                        let max_name_len = vars.iter().map(|(k, _)| k.len()).max().unwrap_or(0);
                        for (name, value) in &vars {
                            let formatted = format_json_value(value);
                            println!("    {:<width$} = {}", name, formatted, width = max_name_len);
                        }
                    }
                }
            }

            "symbolic" => {
                match server.dispatch_http("set_mode", serde_json::json!({"mode": "symbolic"})) {
                    Ok(result) => println!("Mode switched: {result}"),
                    Err(e) => eprintln!("Error: {e}"),
                }
            }

            "concrete" => {
                match server.dispatch_http("set_mode", serde_json::json!({"mode": "concrete"})) {
                    Ok(result) => println!("Mode switched: {result}"),
                    Err(e) => eprintln!("Error: {e}"),
                }
            }

            "rollback" | "undo" => match server.dispatch_http("rollback", serde_json::json!({})) {
                Ok(result) => println!("Rollback: {result}"),
                Err(e) => eprintln!("Error: {e}"),
            },

            "assume" => {
                if arg.is_empty() {
                    eprintln!("Usage: assume <var>=<value>");
                    continue;
                }
                match arg.split_once('=') {
                    Some((var, val_str)) => {
                        let var = var.trim();
                        let val_str = val_str.trim();
                        // Try to parse as integer, then boolean, then string.
                        let json_val = if let Ok(i) = val_str.parse::<i64>() {
                            serde_json::json!(i)
                        } else if val_str.eq_ignore_ascii_case("true") {
                            serde_json::json!(true)
                        } else if val_str.eq_ignore_ascii_case("false") {
                            serde_json::json!(false)
                        } else {
                            serde_json::json!(val_str)
                        };
                        let assignments = serde_json::json!({
                            "assignments": { var: json_val }
                        });
                        match server.dispatch_http("assume_state", assignments) {
                            Ok(result) => println!("Assumed: {result}"),
                            Err(e) => eprintln!("Error: {e}"),
                        }
                    }
                    None => eprintln!("Invalid format. Usage: assume <var>=<value>"),
                }
            }

            "next_model" => match server.dispatch_http("next_model", serde_json::json!({})) {
                Ok(result) => {
                    if result.is_null() {
                        println!("No more satisfying assignments.");
                    } else {
                        println!("Alternate model: {result}");
                    }
                }
                Err(e) => eprintln!("Error: {e}"),
            },

            "compact" => match server.dispatch_http("compact", serde_json::json!({})) {
                Ok(result) => println!("Compacted: {result}"),
                Err(e) => eprintln!("Error: {e}"),
            },

            "reset" => {
                history = StateHistory::new();
                last_results.clear();
                println!("History cleared. Running init...");
                match do_init(&mut server) {
                    Ok(states) => {
                        print_state_list("Initial states", &states);
                        if let Some(first) = states.first() {
                            history.push(first.clone());
                            println!();
                            println!("Picked state #{}.", first.state_id);
                            if !no_invariants {
                                check_invariants_quiet(
                                    &mut server,
                                    first.state_id,
                                    &invariant_names,
                                );
                            }
                        }
                        last_results = states;
                    }
                    Err(e) => eprintln!("Error: {e}"),
                }
            }

            other => {
                eprintln!("Unknown command: '{other}'. Type 'help' for available commands.");
            }
        }
    }

    println!("Goodbye.");
    Ok(())
}

// ---------------------------------------------------------------------------
// Server wrappers
// ---------------------------------------------------------------------------

fn do_init(server: &mut InteractiveServer) -> Result<Vec<StateSnapshot>, String> {
    let result = server.dispatch_http("init", serde_json::json!({}))?;
    serde_json::from_value(result).map_err(|e| format!("parse error: {e}"))
}

fn do_step(server: &mut InteractiveServer, state_id: u64) -> Result<Vec<StateSnapshot>, String> {
    let result = server.dispatch_http("step", serde_json::json!({"state_id": state_id}))?;
    serde_json::from_value(result).map_err(|e| format!("parse error: {e}"))
}

fn do_eval(
    server: &mut InteractiveServer,
    state_id: u64,
    expr: &str,
) -> Result<serde_json::Value, String> {
    server.dispatch_http(
        "eval",
        serde_json::json!({"state_id": state_id, "expr": expr}),
    )
}

fn do_check_invariant(
    server: &mut InteractiveServer,
    state_id: u64,
    inv_name: &str,
) -> Result<serde_json::Value, String> {
    server.dispatch_http(
        "check_invariant",
        serde_json::json!({"state_id": state_id, "inv": inv_name}),
    )
}

// ---------------------------------------------------------------------------
// Invariant checking helpers
// ---------------------------------------------------------------------------

/// Check all invariants, printing only violations (called after each pick).
fn check_invariants_quiet(
    server: &mut InteractiveServer,
    state_id: u64,
    invariant_names: &[String],
) {
    for inv in invariant_names {
        match do_check_invariant(server, state_id, inv) {
            Ok(result) => {
                if let Some(false) = result.get("holds").and_then(|v| v.as_bool()) {
                    println!("  INVARIANT VIOLATION: {inv} is FALSE in this state!");
                }
            }
            Err(e) => {
                eprintln!("  Warning: could not check invariant {inv}: {e}");
            }
        }
    }
}

/// Check all invariants, printing pass/fail for each.
fn check_invariants_verbose(
    server: &mut InteractiveServer,
    state_id: u64,
    invariant_names: &[String],
) {
    println!("Checking {} invariant(s):", invariant_names.len());
    for inv in invariant_names {
        match do_check_invariant(server, state_id, inv) {
            Ok(result) => {
                if let Some(holds) = result.get("holds").and_then(|v| v.as_bool()) {
                    if holds {
                        println!("  PASS: {inv}");
                    } else {
                        println!("  FAIL: {inv} -- invariant violated!");
                    }
                } else {
                    println!("  ???:  {inv} -- unexpected result: {result}");
                }
            }
            Err(e) => {
                println!("  ERR:  {inv} -- {e}");
            }
        }
    }
}

/// Check a single invariant by name with verbose output.
fn check_invariant_single(server: &mut InteractiveServer, state_id: u64, inv_name: &str) {
    match do_check_invariant(server, state_id, inv_name) {
        Ok(result) => {
            if let Some(holds) = result.get("holds").and_then(|v| v.as_bool()) {
                if holds {
                    println!("PASS: {inv_name} holds in state #{state_id}.");
                } else {
                    println!("FAIL: {inv_name} is violated in state #{state_id}!");
                }
            } else {
                println!("Unexpected result: {result}");
            }
        }
        Err(e) => eprintln!("Error checking invariant: {e}"),
    }
}

// ---------------------------------------------------------------------------
// State diff
// ---------------------------------------------------------------------------

/// Compare two state snapshots and return the variables that changed.
fn diff_states<'a>(
    old: &'a FxHashMap<String, serde_json::Value>,
    new: &'a FxHashMap<String, serde_json::Value>,
) -> Vec<(&'a str, &'a serde_json::Value, &'a serde_json::Value)> {
    let mut changes = Vec::new();
    let mut keys: Vec<&String> = old.keys().collect();
    keys.sort();
    for key in keys {
        if let Some(new_val) = new.get(key) {
            if let Some(old_val) = old.get(key) {
                if old_val != new_val {
                    changes.push((key.as_str(), old_val, new_val));
                }
            }
        }
    }
    // Also check for new variables (unlikely in TLA+ but defensive).
    for key in new.keys() {
        if !old.contains_key(key) {
            changes.push((key.as_str(), &serde_json::Value::Null, &new[key]));
        }
    }
    changes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_json_value_bool() {
        assert_eq!(format_json_value(&serde_json::json!(true)), "TRUE");
        assert_eq!(format_json_value(&serde_json::json!(false)), "FALSE");
    }

    #[test]
    fn test_format_json_value_number() {
        assert_eq!(format_json_value(&serde_json::json!(42)), "42");
    }

    #[test]
    fn test_format_json_value_string() {
        assert_eq!(format_json_value(&serde_json::json!("hello")), "\"hello\"");
    }

    #[test]
    fn test_format_json_value_set() {
        // Non-pair arrays render as sets.
        let v = serde_json::json!([1, 2, 3]);
        assert_eq!(format_json_value(&v), "{1, 2, 3}");
    }

    #[test]
    fn test_format_json_value_record() {
        let v = serde_json::json!({"a": 1, "b": true});
        let s = format_json_value(&v);
        // Keys might be in any order.
        assert!(s.contains("a |-> 1"));
        assert!(s.contains("b |-> TRUE"));
    }

    #[test]
    fn test_format_json_value_interval() {
        let v = serde_json::json!({"lo": 1, "hi": 10});
        assert_eq!(format_json_value(&v), "1..10");
    }

    #[test]
    fn test_format_json_value_null() {
        assert_eq!(format_json_value(&serde_json::Value::Null), "UNDEFINED");
    }

    #[test]
    fn test_state_history_push_and_navigate() {
        let mut h = StateHistory::new();
        assert!(h.current().is_none());

        let s0 = StateSnapshot {
            state_id: 0,
            variables: FxHashMap::default(),
        };
        let s1 = StateSnapshot {
            state_id: 1,
            variables: FxHashMap::default(),
        };
        let s2 = StateSnapshot {
            state_id: 2,
            variables: FxHashMap::default(),
        };

        h.push(s0);
        assert_eq!(h.current().map(|s| s.state_id), Some(0));

        h.push(s1);
        assert_eq!(h.current().map(|s| s.state_id), Some(1));

        h.push(s2);
        assert_eq!(h.current().map(|s| s.state_id), Some(2));

        // Back twice.
        assert_eq!(h.back().map(|s| s.state_id), Some(1));
        assert_eq!(h.back().map(|s| s.state_id), Some(0));
        assert!(h.back().is_none()); // Already at start.

        // Forward.
        assert_eq!(h.forward().map(|s| s.state_id), Some(1));
        assert_eq!(h.forward().map(|s| s.state_id), Some(2));
        assert!(h.forward().is_none()); // Already at end.
    }

    #[test]
    fn test_state_history_push_truncates_forward() {
        let mut h = StateHistory::new();
        h.push(StateSnapshot {
            state_id: 0,
            variables: FxHashMap::default(),
        });
        h.push(StateSnapshot {
            state_id: 1,
            variables: FxHashMap::default(),
        });
        h.push(StateSnapshot {
            state_id: 2,
            variables: FxHashMap::default(),
        });

        // Go back to state 0.
        h.back();
        h.back();
        assert_eq!(h.current().map(|s| s.state_id), Some(0));

        // Push a new state -- should discard states 1 and 2.
        h.push(StateSnapshot {
            state_id: 99,
            variables: FxHashMap::default(),
        });
        assert_eq!(h.entries.len(), 2);
        assert_eq!(h.current().map(|s| s.state_id), Some(99));
        assert!(h.forward().is_none());
    }

    #[test]
    fn test_diff_states_detects_changes() {
        let mut old = FxHashMap::default();
        old.insert("x".to_string(), serde_json::json!(1));
        old.insert("y".to_string(), serde_json::json!("a"));

        let mut new = FxHashMap::default();
        new.insert("x".to_string(), serde_json::json!(2));
        new.insert("y".to_string(), serde_json::json!("a"));

        let changes = diff_states(&old, &new);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].0, "x");
    }

    #[test]
    fn test_diff_states_no_changes() {
        let mut state = FxHashMap::default();
        state.insert("x".to_string(), serde_json::json!(1));

        let changes = diff_states(&state, &state);
        assert!(changes.is_empty());
    }

    #[test]
    fn test_position_info() {
        let mut h = StateHistory::new();
        assert_eq!(h.position_info(), (0, 0));

        h.push(StateSnapshot {
            state_id: 0,
            variables: FxHashMap::default(),
        });
        assert_eq!(h.position_info(), (1, 1));

        h.push(StateSnapshot {
            state_id: 1,
            variables: FxHashMap::default(),
        });
        assert_eq!(h.position_info(), (2, 2));

        h.back();
        assert_eq!(h.position_info(), (1, 2));
    }
}
