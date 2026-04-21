// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 template` subcommand: generate complete protocol template TLA+ specs.
//!
//! Unlike `tla2 init` (which scaffolds project structure), `tla2 template`
//! generates complete, runnable TLA+ specs for common distributed systems
//! protocol patterns: mutex, consensus, cache coherence, bounded queue,
//! leader election, and token ring.

use std::path::Path;

use anyhow::{bail, Context, Result};

/// Protocol template kind for the `template` command.
///
/// When this module is wired into the CLI, move this enum to
/// `crate::cli_schema::TemplateKind` and replace with a re-import.
#[derive(Debug, Clone, Copy, clap::ValueEnum, serde::Serialize)]
pub(crate) enum TemplateKind {
    /// Peterson's mutual exclusion (2+ processes, shared variables).
    Mutex,
    /// Simple consensus with proposals and votes (N processes).
    Consensus,
    /// MSI-like cache coherence protocol.
    Cache,
    /// Bounded FIFO queue with producer/consumer.
    Queue,
    /// Leader election in a unidirectional ring (LCR).
    Leader,
    /// Token passing ring protocol.
    TokenRing,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the `template` command.
///
/// Generates a complete `.tla` specification and matching `.cfg` configuration
/// file for the given protocol template kind. When `stdout_only` is true, both
/// files are printed to stdout instead of written to disk.
pub(crate) fn cmd_template(
    kind: TemplateKind,
    name: &str,
    processes: u32,
    output_dir: &Path,
    stdout_only: bool,
) -> Result<()> {
    validate_module_name(name)?;
    validate_processes(processes)?;

    let (tla_content, cfg_content) = render_template(kind, name, processes);

    if stdout_only {
        print!("{tla_content}");
        println!("---- CONFIG ----");
        print!("{cfg_content}");
        return Ok(());
    }

    let tla_path = output_dir.join(format!("{name}.tla"));
    let cfg_path = output_dir.join(format!("{name}.cfg"));

    // Ensure output directory exists.
    if !output_dir.exists() {
        std::fs::create_dir_all(output_dir)
            .with_context(|| format!("create directory {}", output_dir.display()))?;
    }

    std::fs::write(&tla_path, &tla_content)
        .with_context(|| format!("write {}", tla_path.display()))?;
    std::fs::write(&cfg_path, &cfg_content)
        .with_context(|| format!("write {}", cfg_path.display()))?;

    println!("Created {}", tla_path.display());
    println!("Created {}", cfg_path.display());
    println!();
    println!("Template: {kind:?} ({processes} processes)");
    println!("Next steps:");
    println!("  1. Review {name}.tla and customize as needed");
    println!("  2. Run: tla2 check {name}.tla");

    Ok(())
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

/// Validate that `name` is a legal TLA+ module identifier.
fn validate_module_name(name: &str) -> Result<()> {
    if name.is_empty() {
        bail!("Module name must not be empty");
    }
    if !name
        .chars()
        .next()
        .map_or(false, |c| c.is_ascii_alphabetic() || c == '_')
    {
        bail!(
            "Module name must start with a letter or underscore, got '{}'",
            name
        );
    }
    if !name
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        bail!(
            "Module name must contain only letters, digits, and underscores, got '{}'",
            name
        );
    }
    Ok(())
}

/// Validate the process count.
fn validate_processes(n: u32) -> Result<()> {
    if n == 0 {
        bail!("Process count must be at least 1");
    }
    if n > 100 {
        bail!("Process count must be at most 100 (got {n}), state space explodes beyond that");
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Template dispatch
// ---------------------------------------------------------------------------

/// Return `(tla_content, cfg_content)` for the given template kind.
fn render_template(kind: TemplateKind, name: &str, processes: u32) -> (String, String) {
    match kind {
        TemplateKind::Mutex => render_mutex(name, processes),
        TemplateKind::Consensus => render_consensus(name, processes),
        TemplateKind::Cache => render_cache(name, processes),
        TemplateKind::Queue => render_queue(name, processes),
        TemplateKind::Leader => render_leader(name, processes),
        TemplateKind::TokenRing => render_token_ring(name, processes),
    }
}

/// Build a set literal like `{1, 2, 3}` for 1..n.
fn proc_set(n: u32) -> String {
    let items: Vec<String> = (1..=n).map(|i| i.to_string()).collect();
    format!("{{{}}}", items.join(", "))
}

// ---------------------------------------------------------------------------
// Template: mutex (Peterson's algorithm for 2 processes)
// ---------------------------------------------------------------------------

fn render_mutex(name: &str, processes: u32) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
\\* Peterson's mutual exclusion algorithm.
\\* Guarantees mutual exclusion and deadlock freedom for shared-variable
\\* concurrency.  The core idea: each process sets a flag and defers to
\\* the other via a shared `turn` variable.

EXTENDS Naturals, FiniteSets

CONSTANTS Procs

VARIABLES pc, flag, turn

vars == <<pc, flag, turn>>

Init ==
    /\\ pc   = [p \\in Procs |-> \"idle\"]
    /\\ flag = [p \\in Procs |-> FALSE]
    /\\ turn = CHOOSE p \\in Procs : TRUE

\\* A process signals interest and sets turn to the other.
Request(p) ==
    /\\ pc[p] = \"idle\"
    /\\ flag' = [flag EXCEPT ![p] = TRUE]
    /\\ turn' = CHOOSE q \\in Procs : q /= p
    /\\ pc'   = [pc EXCEPT ![p] = \"waiting\"]

\\* A process enters the critical section when it is safe.
Enter(p) ==
    /\\ pc[p] = \"waiting\"
    /\\ \\/ turn = p
       \\/ \\A q \\in Procs : q = p \\/ flag[q] = FALSE
    /\\ pc' = [pc EXCEPT ![p] = \"critical\"]
    /\\ UNCHANGED <<flag, turn>>

\\* A process leaves the critical section and clears its flag.
Exit(p) ==
    /\\ pc[p] = \"critical\"
    /\\ flag' = [flag EXCEPT ![p] = FALSE]
    /\\ pc'   = [pc EXCEPT ![p] = \"idle\"]
    /\\ UNCHANGED turn

Next ==
    \\E p \\in Procs : Request(p) \\/ Enter(p) \\/ Exit(p)

TypeOK ==
    /\\ pc   \\in [Procs -> {{\"idle\", \"waiting\", \"critical\"}}]
    /\\ flag \\in [Procs -> BOOLEAN]
    /\\ turn \\in Procs

MutualExclusion ==
    \\A p, q \\in Procs :
        (p /= q) => ~(pc[p] = \"critical\" /\\ pc[q] = \"critical\")

Spec == Init /\\ [][Next]_vars
====
"
    );

    let cfg = format!(
        "\
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT MutualExclusion
CONSTANT Procs = {procs}
",
        procs = proc_set(processes)
    );

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Template: consensus (simple proposal/vote protocol)
// ---------------------------------------------------------------------------

fn render_consensus(name: &str, processes: u32) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
\\* Simple consensus protocol with proposals and votes.
\\* Each process proposes a value and votes for proposals it has seen.
\\* A value is decided when a quorum (majority) of processes vote for it.

EXTENDS Naturals, FiniteSets

CONSTANTS Procs, Values, Quorum

VARIABLES pc, proposed, votes, decided

vars == <<pc, proposed, votes, decided>>

Init ==
    /\\ pc       = [p \\in Procs |-> \"propose\"]
    /\\ proposed = [p \\in Procs |-> CHOOSE v \\in Values : TRUE]
    /\\ votes    = [v \\in Values |-> {{}}]
    /\\ decided  = {{}}

\\* A process proposes its value and transitions to vote.
Propose(p) ==
    /\\ pc[p] = \"propose\"
    /\\ pc' = [pc EXCEPT ![p] = \"vote\"]
    /\\ UNCHANGED <<proposed, votes, decided>>

\\* A process votes for the value proposed by any process.
Vote(p) ==
    /\\ pc[p] = \"vote\"
    /\\ \\E q \\in Procs :
        /\\ votes' = [votes EXCEPT ![proposed[q]] = votes[proposed[q]] \\cup {{p}}]
    /\\ pc' = [pc EXCEPT ![p] = \"voted\"]
    /\\ UNCHANGED <<proposed, decided>>

\\* A value is decided when a quorum of votes is reached.
Decide ==
    /\\ \\E v \\in Values :
        /\\ Cardinality(votes[v]) >= Quorum
        /\\ v \\notin decided
        /\\ decided' = decided \\cup {{v}}
    /\\ UNCHANGED <<pc, proposed, votes>>

Next ==
    \\/ \\E p \\in Procs : Propose(p) \\/ Vote(p)
    \\/ Decide

TypeOK ==
    /\\ pc       \\in [Procs -> {{\"propose\", \"vote\", \"voted\"}}]
    /\\ proposed \\in [Procs -> Values]
    /\\ \\A v \\in Values : votes[v] \\subseteq Procs
    /\\ decided  \\subseteq Values

\\* Agreement: at most one value is ever decided.
Agreement ==
    Cardinality(decided) <= 1

Spec == Init /\\ [][Next]_vars
====
"
    );

    let quorum = (processes / 2) + 1;
    let cfg = format!(
        "\
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT Agreement
CONSTANT Procs = {procs}
CONSTANT Values = {{v1, v2}}
CONSTANT Quorum = {quorum}
",
        procs = proc_set(processes),
        quorum = quorum,
    );

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Template: cache (MSI-like coherence protocol)
// ---------------------------------------------------------------------------

fn render_cache(name: &str, processes: u32) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
\\* MSI cache coherence protocol (Modified / Shared / Invalid).
\\* Multiple processors share a memory address.  Each cache line has one of
\\* three states: Invalid (I), Shared (S), or Modified (M).  The protocol
\\* ensures that at most one cache holds M, and S caches agree with memory.

EXTENDS Naturals, FiniteSets

CONSTANTS Procs

VARIABLES cache_state, memory, cache_value

vars == <<cache_state, memory, cache_value>>

States == {{\"I\", \"S\", \"M\"}}

Init ==
    /\\ cache_state = [p \\in Procs |-> \"I\"]
    /\\ memory = 0
    /\\ cache_value = [p \\in Procs |-> 0]

\\* Processor reads: if Invalid, fetch from memory and go Shared.
PrRead(p) ==
    /\\ cache_state[p] = \"I\"
    /\\ cache_state' = [cache_state EXCEPT ![p] = \"S\"]
    /\\ cache_value' = [cache_value EXCEPT ![p] = memory]
    /\\ UNCHANGED memory

\\* Processor writes: go to Modified, invalidate all others.
PrWrite(p, v) ==
    /\\ cache_state' = [q \\in Procs |->
        IF q = p THEN \"M\" ELSE \"I\"]
    /\\ cache_value' = [q \\in Procs |->
        IF q = p THEN v ELSE cache_value[q]]
    /\\ UNCHANGED memory

\\* Evict: a Modified line writes back to memory and goes Invalid.
Evict(p) ==
    /\\ cache_state[p] = \"M\"
    /\\ memory' = cache_value[p]
    /\\ cache_state' = [cache_state EXCEPT ![p] = \"I\"]
    /\\ UNCHANGED cache_value

\\* Downgrade: a Shared line goes Invalid.
Downgrade(p) ==
    /\\ cache_state[p] = \"S\"
    /\\ cache_state' = [cache_state EXCEPT ![p] = \"I\"]
    /\\ UNCHANGED <<memory, cache_value>>

Next ==
    \\E p \\in Procs :
        \\/ PrRead(p)
        \\/ \\E v \\in 0..1 : PrWrite(p, v)
        \\/ Evict(p)
        \\/ Downgrade(p)

TypeOK ==
    /\\ cache_state \\in [Procs -> States]
    /\\ memory \\in 0..1
    /\\ cache_value \\in [Procs -> 0..1]

\\* Safety: at most one processor is in Modified state.
SingleWriter ==
    \\A p, q \\in Procs :
        (p /= q) => ~(cache_state[p] = \"M\" /\\ cache_state[q] = \"M\")

\\* Safety: all Shared caches agree with memory.
SharedCoherent ==
    \\A p \\in Procs :
        cache_state[p] = \"S\" => cache_value[p] = memory

Spec == Init /\\ [][Next]_vars
====
"
    );

    let cfg = format!(
        "\
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT SingleWriter
INVARIANT SharedCoherent
CONSTANT Procs = {procs}
",
        procs = proc_set(processes),
    );

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Template: queue (bounded producer/consumer)
// ---------------------------------------------------------------------------

fn render_queue(name: &str, processes: u32) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
\\* Bounded FIFO queue with producer/consumer processes.
\\* Producers enqueue items when the queue is not full.
\\* Consumers dequeue items when the queue is not empty.
\\* The queue capacity is fixed at `Capacity`.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers, Consumers, Capacity

VARIABLES queue, pc, produced, consumed

vars == <<queue, pc, produced, consumed>>

AllProcs == Producers \\cup Consumers

Init ==
    /\\ queue    = <<>>
    /\\ pc       = [p \\in AllProcs |-> \"ready\"]
    /\\ produced = 0
    /\\ consumed = 0

\\* A producer enqueues an item.
Produce(p) ==
    /\\ p \\in Producers
    /\\ pc[p] = \"ready\"
    /\\ Len(queue) < Capacity
    /\\ queue'    = Append(queue, produced + 1)
    /\\ produced' = produced + 1
    /\\ pc'       = [pc EXCEPT ![p] = \"done\"]
    /\\ UNCHANGED consumed

\\* A consumer dequeues an item.
Consume(c) ==
    /\\ c \\in Consumers
    /\\ pc[c] = \"ready\"
    /\\ Len(queue) > 0
    /\\ queue'    = Tail(queue)
    /\\ consumed' = consumed + 1
    /\\ pc'       = [pc EXCEPT ![c] = \"done\"]
    /\\ UNCHANGED produced

\\* Reset to ready for repeated production/consumption.
Reset(p) ==
    /\\ pc[p] = \"done\"
    /\\ pc' = [pc EXCEPT ![p] = \"ready\"]
    /\\ UNCHANGED <<queue, produced, consumed>>

Next ==
    \\E p \\in AllProcs : Produce(p) \\/ Consume(p) \\/ Reset(p)

TypeOK ==
    /\\ queue \\in Seq(Nat)
    /\\ Len(queue) <= Capacity
    /\\ pc \\in [AllProcs -> {{\"ready\", \"done\"}}]
    /\\ produced \\in Nat
    /\\ consumed \\in Nat

\\* Safety: consumed items never exceed produced items.
ConsumedLeqProduced ==
    consumed <= produced

\\* Safety: queue length equals produced minus consumed.
QueueSizeCorrect ==
    Len(queue) = produced - consumed

Spec == Init /\\ [][Next]_vars
====
"
    );

    // Split processes: half producers, half consumers (at least 1 each).
    let n_prod = std::cmp::max(1, processes / 2);
    let n_cons = std::cmp::max(1, processes - n_prod);
    let prods: Vec<String> = (1..=n_prod).map(|i| format!("p{i}")).collect();
    let cons: Vec<String> = (1..=n_cons).map(|i| format!("c{i}")).collect();

    let cfg = format!(
        "\
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT ConsumedLeqProduced
INVARIANT QueueSizeCorrect
CONSTANT Producers = {{{prods}}}
CONSTANT Consumers = {{{cons}}}
CONSTANT Capacity = 3
",
        prods = prods.join(", "),
        cons = cons.join(", "),
    );

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Template: leader (leader election in a ring)
// ---------------------------------------------------------------------------

fn render_leader(name: &str, processes: u32) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
\\* Leader election in a unidirectional ring (LCR algorithm).
\\* Each process has a unique ID and sends its ID around the ring.
\\* A process forwards a message only if the received ID is greater
\\* than its own.  The process whose ID traverses the entire ring
\\* becomes the leader.

EXTENDS Naturals, FiniteSets

CONSTANTS N, Ids

ASSUME N \\in Nat \\ {{0}}
ASSUME Cardinality(Ids) = N

VARIABLES pc, inbox, leader

vars == <<pc, inbox, leader>>

Nodes == 1..N

\\* Ring successor: node i's messages go to ((i mod N) + 1).
Succ(i) == (i % N) + 1

\\* Each node is assigned a unique ID from Ids.
\\* For model checking we fix an assignment via CHOOSE.
IdOf == CHOOSE f \\in [Nodes -> Ids] :
    \\A i, j \\in Nodes : i /= j => f[i] /= f[j]

Init ==
    /\\ pc     = [n \\in Nodes |-> \"send\"]
    /\\ inbox  = [n \\in Nodes |-> {{}}]
    /\\ leader = [n \\in Nodes |-> FALSE]

\\* Send own ID to the successor.
SendId(n) ==
    /\\ pc[n] = \"send\"
    /\\ inbox' = [inbox EXCEPT ![Succ(n)] = inbox[Succ(n)] \\cup {{IdOf[n]}}]
    /\\ pc'    = [pc EXCEPT ![n] = \"receive\"]
    /\\ UNCHANGED leader

\\* Receive a message: forward if greater, declare leader if own ID.
Receive(n) ==
    /\\ pc[n] = \"receive\"
    /\\ inbox[n] /= {{}}
    /\\ \\E msg \\in inbox[n] :
        /\\ inbox' = [inbox EXCEPT
            ![n] = inbox[n] \\ {{msg}},
            ![Succ(n)] = IF msg > IdOf[n]
                         THEN inbox[Succ(n)] \\cup {{msg}}
                         ELSE inbox[Succ(n)]]
        /\\ leader' = [leader EXCEPT
            ![n] = IF msg = IdOf[n] THEN TRUE ELSE leader[n]]
    /\\ pc' = [pc EXCEPT ![n] = \"send\"]

Next ==
    \\E n \\in Nodes : SendId(n) \\/ Receive(n)

TypeOK ==
    /\\ pc     \\in [Nodes -> {{\"send\", \"receive\"}}]
    /\\ leader \\in [Nodes -> BOOLEAN]

\\* Safety: at most one leader.
AtMostOneLeader ==
    \\A i, j \\in Nodes :
        (leader[i] /\\ leader[j]) => i = j

Spec == Init /\\ [][Next]_vars
====
"
    );

    let ids = proc_set(processes);
    let cfg = format!(
        "\
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT AtMostOneLeader
CONSTANT N = {processes}
CONSTANT Ids = {ids}
"
    );

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Template: token-ring (token passing)
// ---------------------------------------------------------------------------

fn render_token_ring(name: &str, processes: u32) -> (String, String) {
    let tla = format!(
        "\
---- MODULE {name} ----
\\* Token passing ring protocol.
\\* Exactly one token circulates in a ring of N nodes.  A node holding the
\\* token may enter its critical section, then passes the token to its
\\* successor.  Guarantees mutual exclusion and ensures the token is never
\\* lost or duplicated.

EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \\in Nat \\ {{0}}

VARIABLES token, pc

vars == <<token, pc>>

Nodes == 1..N

\\* Ring successor: node i passes to ((i mod N) + 1).
Succ(i) == (i % N) + 1

Init ==
    /\\ token = 1
    /\\ pc    = [n \\in Nodes |-> IF n = 1 THEN \"has_token\" ELSE \"idle\"]

\\* A node with the token enters the critical section.
EnterCS(n) ==
    /\\ pc[n] = \"has_token\"
    /\\ pc' = [pc EXCEPT ![n] = \"critical\"]
    /\\ UNCHANGED token

\\* A node in the critical section exits and passes the token.
ExitCS(n) ==
    /\\ pc[n] = \"critical\"
    /\\ token' = Succ(n)
    /\\ pc' = [pc EXCEPT
        ![n] = \"idle\",
        ![Succ(n)] = \"has_token\"]

Next ==
    \\E n \\in Nodes : EnterCS(n) \\/ ExitCS(n)

TypeOK ==
    /\\ token \\in Nodes
    /\\ pc \\in [Nodes -> {{\"idle\", \"has_token\", \"critical\"}}]

\\* Safety: at most one node is in the critical section.
MutualExclusion ==
    \\A i, j \\in Nodes :
        (i /= j) => ~(pc[i] = \"critical\" /\\ pc[j] = \"critical\")

\\* Safety: exactly one node holds or is using the token.
TokenUnique ==
    Cardinality({{n \\in Nodes : pc[n] \\in {{\"has_token\", \"critical\"}}}}) = 1

Spec == Init /\\ [][Next]_vars
====
"
    );

    let cfg = format!(
        "\
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT MutualExclusion
INVARIANT TokenUnique
CONSTANT N = {processes}
"
    );

    (tla, cfg)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Validation -----------------------------------------------------------

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
    fn test_validate_module_name_bad_start() {
        assert!(validate_module_name("123Spec").is_err());
        assert!(validate_module_name("-Spec").is_err());
    }

    #[test]
    fn test_validate_module_name_special_chars() {
        assert!(validate_module_name("My-Spec").is_err());
        assert!(validate_module_name("My Spec").is_err());
    }

    #[test]
    fn test_validate_processes_zero() {
        assert!(validate_processes(0).is_err());
    }

    #[test]
    fn test_validate_processes_too_many() {
        assert!(validate_processes(101).is_err());
    }

    #[test]
    fn test_validate_processes_ok() {
        assert!(validate_processes(1).is_ok());
        assert!(validate_processes(3).is_ok());
        assert!(validate_processes(100).is_ok());
    }

    // -- proc_set helper ------------------------------------------------------

    #[test]
    fn test_proc_set() {
        assert_eq!(proc_set(1), "{1}");
        assert_eq!(proc_set(3), "{1, 2, 3}");
        assert_eq!(proc_set(5), "{1, 2, 3, 4, 5}");
    }

    // -- Template content: mutex ----------------------------------------------

    #[test]
    fn test_mutex_template_structure() {
        let (tla, cfg) = render_mutex("TestMutex", 2);
        assert!(tla.contains("---- MODULE TestMutex ----"));
        assert!(tla.contains("EXTENDS Naturals, FiniteSets"));
        assert!(tla.contains("CONSTANTS Procs"));
        assert!(tla.contains("VARIABLES pc, flag, turn"));
        assert!(tla.contains("Init =="));
        assert!(tla.contains("Next =="));
        assert!(tla.contains("MutualExclusion =="));
        assert!(tla.contains("TypeOK =="));
        assert!(tla.ends_with("====\n"));
        assert!(cfg.contains("INIT Init"));
        assert!(cfg.contains("NEXT Next"));
        assert!(cfg.contains("INVARIANT TypeOK"));
        assert!(cfg.contains("INVARIANT MutualExclusion"));
        assert!(cfg.contains("CONSTANT Procs = {1, 2}"));
    }

    // -- Template content: consensus ------------------------------------------

    #[test]
    fn test_consensus_template_structure() {
        let (tla, cfg) = render_consensus("TestConsensus", 3);
        assert!(tla.contains("---- MODULE TestConsensus ----"));
        assert!(tla.contains("CONSTANTS Procs, Values, Quorum"));
        assert!(tla.contains("VARIABLES pc, proposed, votes, decided"));
        assert!(tla.contains("Agreement =="));
        assert!(tla.contains("Cardinality(decided) <= 1"));
        assert!(tla.ends_with("====\n"));
        assert!(cfg.contains("INVARIANT Agreement"));
        assert!(cfg.contains("CONSTANT Quorum = 2"));
        assert!(cfg.contains("CONSTANT Procs = {1, 2, 3}"));
    }

    #[test]
    fn test_consensus_quorum_calculation() {
        // 3 processes -> quorum = 2
        let (_, cfg) = render_consensus("C", 3);
        assert!(cfg.contains("Quorum = 2"));
        // 5 processes -> quorum = 3
        let (_, cfg) = render_consensus("C", 5);
        assert!(cfg.contains("Quorum = 3"));
        // 1 process -> quorum = 1
        let (_, cfg) = render_consensus("C", 1);
        assert!(cfg.contains("Quorum = 1"));
    }

    // -- Template content: cache ----------------------------------------------

    #[test]
    fn test_cache_template_structure() {
        let (tla, cfg) = render_cache("TestCache", 2);
        assert!(tla.contains("---- MODULE TestCache ----"));
        assert!(tla.contains("VARIABLES cache_state, memory, cache_value"));
        assert!(tla.contains("SingleWriter =="));
        assert!(tla.contains("SharedCoherent =="));
        assert!(tla.contains("PrRead(p)"));
        assert!(tla.contains("PrWrite(p, v)"));
        assert!(tla.contains("Evict(p)"));
        assert!(tla.ends_with("====\n"));
        assert!(cfg.contains("INVARIANT SingleWriter"));
        assert!(cfg.contains("INVARIANT SharedCoherent"));
        assert!(cfg.contains("CONSTANT Procs = {1, 2}"));
    }

    // -- Template content: queue ----------------------------------------------

    #[test]
    fn test_queue_template_structure() {
        let (tla, cfg) = render_queue("TestQueue", 4);
        assert!(tla.contains("---- MODULE TestQueue ----"));
        assert!(tla.contains("EXTENDS Naturals, Sequences, FiniteSets"));
        assert!(tla.contains("CONSTANTS Producers, Consumers, Capacity"));
        assert!(tla.contains("Produce(p)"));
        assert!(tla.contains("Consume(c)"));
        assert!(tla.contains("ConsumedLeqProduced =="));
        assert!(tla.contains("QueueSizeCorrect =="));
        assert!(tla.ends_with("====\n"));
        assert!(cfg.contains("INVARIANT ConsumedLeqProduced"));
        assert!(cfg.contains("INVARIANT QueueSizeCorrect"));
        assert!(cfg.contains("CONSTANT Capacity = 3"));
        // 4 processes -> 2 producers, 2 consumers
        assert!(cfg.contains("Producers = {p1, p2}"));
        assert!(cfg.contains("Consumers = {c1, c2}"));
    }

    #[test]
    fn test_queue_single_process() {
        // 1 process -> at least 1 producer and 1 consumer
        let (_, cfg) = render_queue("Q", 1);
        assert!(cfg.contains("Producers = {p1}"));
        assert!(cfg.contains("Consumers = {c1}"));
    }

    // -- Template content: leader election ------------------------------------

    #[test]
    fn test_leader_template_structure() {
        let (tla, cfg) = render_leader("TestLeader", 3);
        assert!(tla.contains("---- MODULE TestLeader ----"));
        assert!(tla.contains("CONSTANTS N, Ids"));
        assert!(tla.contains("VARIABLES pc, inbox, leader"));
        assert!(tla.contains("Succ(i)"));
        assert!(tla.contains("SendId(n)"));
        assert!(tla.contains("Receive(n)"));
        assert!(tla.contains("AtMostOneLeader =="));
        assert!(tla.ends_with("====\n"));
        assert!(cfg.contains("INVARIANT AtMostOneLeader"));
        assert!(cfg.contains("CONSTANT N = 3"));
        assert!(cfg.contains("CONSTANT Ids = {1, 2, 3}"));
    }

    // -- Template content: token ring -----------------------------------------

    #[test]
    fn test_token_ring_template_structure() {
        let (tla, cfg) = render_token_ring("TestRing", 4);
        assert!(tla.contains("---- MODULE TestRing ----"));
        assert!(tla.contains("CONSTANTS N"));
        assert!(tla.contains("VARIABLES token, pc"));
        assert!(tla.contains("EnterCS(n)"));
        assert!(tla.contains("ExitCS(n)"));
        assert!(tla.contains("MutualExclusion =="));
        assert!(tla.contains("TokenUnique =="));
        assert!(tla.ends_with("====\n"));
        assert!(cfg.contains("INVARIANT MutualExclusion"));
        assert!(cfg.contains("INVARIANT TokenUnique"));
        assert!(cfg.contains("CONSTANT N = 4"));
    }

    // -- File I/O: cmd_template -----------------------------------------------

    #[test]
    fn test_cmd_template_creates_files() {
        let dir = std::env::temp_dir().join("tla2_test_template_mutex");
        let _ = std::fs::remove_dir_all(&dir);

        cmd_template(
            TemplateKind::Mutex,
            "PetersonMutex",
            2,
            &dir,
            false,
        )
        .expect("cmd_template should succeed");

        let tla_path = dir.join("PetersonMutex.tla");
        let cfg_path = dir.join("PetersonMutex.cfg");
        assert!(tla_path.exists(), ".tla file should exist");
        assert!(cfg_path.exists(), ".cfg file should exist");

        let tla = std::fs::read_to_string(&tla_path).unwrap();
        assert!(tla.contains("---- MODULE PetersonMutex ----"));

        let cfg = std::fs::read_to_string(&cfg_path).unwrap();
        assert!(cfg.contains("INIT Init"));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cmd_template_all_kinds_produce_valid_structure() {
        let kinds = [
            TemplateKind::Mutex,
            TemplateKind::Consensus,
            TemplateKind::Cache,
            TemplateKind::Queue,
            TemplateKind::Leader,
            TemplateKind::TokenRing,
        ];

        for kind in kinds {
            let (tla, cfg) = render_template(kind, "TestAll", 3);

            // Every template must have the MODULE header and closing.
            assert!(
                tla.contains("---- MODULE TestAll ----"),
                "{kind:?} missing MODULE header"
            );
            assert!(tla.contains("===="), "{kind:?} missing closing ====");
            assert!(tla.contains("Init =="), "{kind:?} missing Init");
            assert!(tla.contains("Next =="), "{kind:?} missing Next");

            // Every config must reference Init and Next.
            assert!(cfg.contains("INIT Init"), "{kind:?} cfg missing INIT");
            assert!(cfg.contains("NEXT Next"), "{kind:?} cfg missing NEXT");

            // Every config must have at least one INVARIANT.
            assert!(
                cfg.contains("INVARIANT"),
                "{kind:?} cfg missing INVARIANT"
            );
        }
    }

    #[test]
    fn test_cmd_template_processes_reflected_in_config() {
        let (_, cfg) = render_mutex("M", 5);
        assert!(cfg.contains("Procs = {1, 2, 3, 4, 5}"));

        let (_, cfg) = render_token_ring("T", 7);
        assert!(cfg.contains("N = 7"));

        let (_, cfg) = render_leader("L", 4);
        assert!(cfg.contains("N = 4"));
        assert!(cfg.contains("Ids = {1, 2, 3, 4}"));
    }

    #[test]
    fn test_cmd_template_rejects_empty_name() {
        let dir = std::env::temp_dir().join("tla2_test_template_empty");
        let result = cmd_template(TemplateKind::Mutex, "", 3, &dir, false);
        assert!(result.is_err());
        assert!(
            result.unwrap_err().to_string().contains("must not be empty"),
            "should reject empty name"
        );
    }

    #[test]
    fn test_cmd_template_rejects_zero_processes() {
        let dir = std::env::temp_dir().join("tla2_test_template_zero");
        let result = cmd_template(TemplateKind::Mutex, "Foo", 0, &dir, false);
        assert!(result.is_err());
        assert!(
            result.unwrap_err().to_string().contains("at least 1"),
            "should reject 0 processes"
        );
    }
}
