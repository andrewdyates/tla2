// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 init` subcommand: scaffold a new TLA+ specification project.
//!
//! Generates a `.tla` module file and a `.cfg` configuration file from one of
//! several built-in templates (basic, distributed, mutex, cache).

use std::path::Path;

use anyhow::{bail, Context, Result};

use crate::cli_schema::InitTemplate;

/// Run the `init` command.
pub(crate) fn cmd_init(
    name: &str,
    template: InitTemplate,
    dir: &Path,
    force: bool,
) -> Result<()> {
    validate_module_name(name)?;

    let tla_path = dir.join(format!("{name}.tla"));
    let cfg_path = dir.join(format!("{name}.cfg"));

    if !force {
        if tla_path.exists() {
            bail!(
                "{} already exists. Use --force to overwrite.",
                tla_path.display()
            );
        }
        if cfg_path.exists() {
            bail!(
                "{} already exists. Use --force to overwrite.",
                cfg_path.display()
            );
        }
    }

    // Ensure output directory exists.
    if !dir.exists() {
        std::fs::create_dir_all(dir)
            .with_context(|| format!("create directory {}", dir.display()))?;
    }

    let (tla_content, cfg_content) = render_template(name, template);

    std::fs::write(&tla_path, &tla_content)
        .with_context(|| format!("write {}", tla_path.display()))?;
    std::fs::write(&cfg_path, &cfg_content)
        .with_context(|| format!("write {}", cfg_path.display()))?;

    println!("Created {}", tla_path.display());
    println!("Created {}", cfg_path.display());
    println!();
    println!("Next steps:");
    println!("  1. Edit {name}.tla to define your specification");
    println!("  2. Run: tla2 check {name}.tla");

    Ok(())
}

/// Validate that `name` is a legal TLA+ module identifier.
fn validate_module_name(name: &str) -> Result<()> {
    if name.is_empty() {
        bail!("Spec name must not be empty");
    }
    if !name.chars().next().map_or(false, |c| c.is_ascii_alphabetic() || c == '_') {
        bail!(
            "Spec name must start with a letter or underscore, got '{}'",
            name
        );
    }
    if !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        bail!(
            "Spec name must contain only letters, digits, and underscores, got '{}'",
            name
        );
    }
    Ok(())
}

/// Return `(tla_content, cfg_content)` for the given template.
fn render_template(name: &str, template: InitTemplate) -> (String, String) {
    match template {
        InitTemplate::Basic => render_basic(name),
        InitTemplate::Distributed => render_distributed(name),
        InitTemplate::Mutex => render_mutex(name),
        InitTemplate::Cache => render_cache(name),
    }
}

// ---------------------------------------------------------------------------
// Template: basic
// ---------------------------------------------------------------------------

fn render_basic(name: &str) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES x

Init ==
    x = 0

Next ==
    x' = x + 1

TypeOK ==
    x \\in Nat

Spec == Init /\\ [][Next]_<<x>>
====
"
    );

    let cfg = "\
INIT Init
NEXT Next
INVARIANT TypeOK
CONSTANT N = 3
"
    .to_string();

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Template: distributed
// ---------------------------------------------------------------------------

fn render_distributed(name: &str) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs

VARIABLES pc, messages

vars == <<pc, messages>>

Init ==
    /\\ pc = [p \\in Procs |-> \"ready\"]
    /\\ messages = <<>>

Send(p) ==
    /\\ pc[p] = \"ready\"
    /\\ messages' = Append(messages, p)
    /\\ pc' = [pc EXCEPT ![p] = \"sent\"]

Recv(p) ==
    /\\ pc[p] = \"sent\"
    /\\ Len(messages) > 0
    /\\ pc' = [pc EXCEPT ![p] = \"done\"]
    /\\ messages' = Tail(messages)

Next ==
    \\E p \\in Procs : Send(p) \\/ Recv(p)

TypeOK ==
    /\\ pc \\in [Procs -> {{\"ready\", \"sent\", \"done\"}}]
    /\\ messages \\in Seq(Procs)

Spec == Init /\\ [][Next]_vars
====
"
    );

    let cfg = "\
INIT Init
NEXT Next
INVARIANT TypeOK
CONSTANT Procs = {p1, p2, p3}
"
    .to_string();

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Template: mutex
// ---------------------------------------------------------------------------

fn render_mutex(name: &str) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
EXTENDS Naturals, FiniteSets

CONSTANTS Procs

VARIABLES pc, turn

vars == <<pc, turn>>

Init ==
    /\\ pc = [p \\in Procs |-> \"idle\"]
    /\\ turn = CHOOSE p \\in Procs : TRUE

Request(p) ==
    /\\ pc[p] = \"idle\"
    /\\ pc' = [pc EXCEPT ![p] = \"waiting\"]
    /\\ UNCHANGED turn

Enter(p) ==
    /\\ pc[p] = \"waiting\"
    /\\ turn = p
    /\\ pc' = [pc EXCEPT ![p] = \"critical\"]
    /\\ UNCHANGED turn

Exit(p) ==
    /\\ pc[p] = \"critical\"
    /\\ pc' = [pc EXCEPT ![p] = \"idle\"]
    /\\ turn' = CHOOSE q \\in Procs : q /= p

Next ==
    \\E p \\in Procs : Request(p) \\/ Enter(p) \\/ Exit(p)

TypeOK ==
    /\\ pc \\in [Procs -> {{\"idle\", \"waiting\", \"critical\"}}]
    /\\ turn \\in Procs

MutualExclusion ==
    \\A p, q \\in Procs :
        (p /= q) => ~(pc[p] = \"critical\" /\\ pc[q] = \"critical\")

Spec == Init /\\ [][Next]_vars
====
"
    );

    let cfg = "\
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT MutualExclusion
CONSTANT Procs = {p1, p2}
"
    .to_string();

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Template: cache
// ---------------------------------------------------------------------------

fn render_cache(name: &str) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
EXTENDS Naturals, FiniteSets

CONSTANTS Procs, Addrs, Values

VARIABLES cache, memory

vars == <<cache, memory>>

Init ==
    /\\ cache = [p \\in Procs |-> [a \\in Addrs |-> None]]
    /\\ memory = [a \\in Addrs |-> CHOOSE v \\in Values : TRUE]

None == CHOOSE v : v \\notin Values

Read(p, a) ==
    /\\ cache[p][a] = None
    /\\ cache' = [cache EXCEPT ![p][a] = memory[a]]
    /\\ UNCHANGED memory

Write(p, a, v) ==
    /\\ v \\in Values
    /\\ memory' = [memory EXCEPT ![a] = v]
    /\\ cache' = [c \\in Procs |-> [cache[c] EXCEPT ![a] = None]]

Next ==
    \\E p \\in Procs, a \\in Addrs :
        \\/ Read(p, a)
        \\/ \\E v \\in Values : Write(p, a, v)

TypeOK ==
    /\\ cache \\in [Procs -> [Addrs -> Values \\cup {{None}}]]
    /\\ memory \\in [Addrs -> Values]

Coherence ==
    \\A p \\in Procs, a \\in Addrs :
        cache[p][a] /= None => cache[p][a] = memory[a]

Spec == Init /\\ [][Next]_vars
====
"
    );

    let cfg = "\
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT Coherence
CONSTANT Procs = {p1, p2}
CONSTANT Addrs = {a1}
CONSTANT Values = {v1, v2}
"
    .to_string();

    (tla, cfg)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_module_name_valid() {
        assert!(validate_module_name("MySpec").is_ok());
        assert!(validate_module_name("_Spec").is_ok());
        assert!(validate_module_name("Spec123").is_ok());
    }

    #[test]
    fn test_validate_module_name_empty() {
        assert!(validate_module_name("").is_err());
    }

    #[test]
    fn test_validate_module_name_starts_with_digit() {
        assert!(validate_module_name("123Spec").is_err());
    }

    #[test]
    fn test_validate_module_name_special_chars() {
        assert!(validate_module_name("My-Spec").is_err());
        assert!(validate_module_name("My Spec").is_err());
    }

    #[test]
    fn test_render_basic_contains_module_name() {
        let (tla, cfg) = render_basic("Foo");
        assert!(tla.contains("---- MODULE Foo ----"));
        assert!(tla.contains("EXTENDS Naturals"));
        assert!(tla.contains("Init =="));
        assert!(tla.contains("Next =="));
        assert!(tla.contains("TypeOK =="));
        assert!(cfg.contains("INIT Init"));
        assert!(cfg.contains("NEXT Next"));
        assert!(cfg.contains("INVARIANT TypeOK"));
    }

    #[test]
    fn test_render_distributed_contains_procs() {
        let (tla, cfg) = render_distributed("Dist");
        assert!(tla.contains("---- MODULE Dist ----"));
        assert!(tla.contains("EXTENDS Naturals, Sequences"));
        assert!(tla.contains("VARIABLES pc, messages"));
        assert!(cfg.contains("CONSTANT Procs"));
    }

    #[test]
    fn test_render_mutex_contains_mutual_exclusion() {
        let (tla, _cfg) = render_mutex("Lock");
        assert!(tla.contains("---- MODULE Lock ----"));
        assert!(tla.contains("MutualExclusion =="));
    }

    #[test]
    fn test_render_cache_contains_coherence() {
        let (tla, cfg) = render_cache("MyCache");
        assert!(tla.contains("---- MODULE MyCache ----"));
        assert!(tla.contains("Coherence =="));
        assert!(cfg.contains("INVARIANT Coherence"));
    }

    #[test]
    fn test_cmd_init_creates_files() {
        let dir = std::env::temp_dir().join("tla2_test_init_basic");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();

        cmd_init("TestSpec", InitTemplate::Basic, &dir, false).unwrap();

        assert!(dir.join("TestSpec.tla").exists());
        assert!(dir.join("TestSpec.cfg").exists());

        let tla = std::fs::read_to_string(dir.join("TestSpec.tla")).unwrap();
        assert!(tla.contains("---- MODULE TestSpec ----"));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cmd_init_rejects_existing_without_force() {
        let dir = std::env::temp_dir().join("tla2_test_init_no_force");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();

        // First call succeeds.
        cmd_init("Dup", InitTemplate::Basic, &dir, false).unwrap();

        // Second call without --force fails.
        let err = cmd_init("Dup", InitTemplate::Basic, &dir, false);
        assert!(err.is_err());

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cmd_init_force_overwrites() {
        let dir = std::env::temp_dir().join("tla2_test_init_force");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();

        cmd_init("Over", InitTemplate::Basic, &dir, false).unwrap();
        // Overwrite with force=true and a different template.
        cmd_init("Over", InitTemplate::Mutex, &dir, true).unwrap();

        let tla = std::fs::read_to_string(dir.join("Over.tla")).unwrap();
        assert!(tla.contains("MutualExclusion"));

        let _ = std::fs::remove_dir_all(&dir);
    }
}
