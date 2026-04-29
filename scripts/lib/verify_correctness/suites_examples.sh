# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

run_verify_correctness_examples_suite() {
# ===== TLA+ Examples repository specs (TLC equivalence validated) =====

# CigaretteSmokers from tlaplus/Examples - classic concurrency problem
# Tests resource sharing with multiple agents
run_check "CigaretteSmokers" "$HOME/tlaplus-examples/specifications/CigaretteSmokers/CigaretteSmokers.tla" 6 "$HOME/tlaplus-examples/specifications/CigaretteSmokers/CigaretteSmokers.cfg" 1

# TokenRing from tlaplus/Examples (ewd426) - Dijkstra's token ring mutual exclusion
# Tests large state space (46656 states) with modular arithmetic
run_check "TokenRing" "$HOME/tlaplus-examples/specifications/ewd426/TokenRing.tla" 46656 "$HOME/tlaplus-examples/specifications/ewd426/TokenRing.cfg" 1

# MCEcho from tlaplus/Examples - Echo algorithm for distributed systems
# Tests spanning tree construction via message passing
run_check "MCEcho" "$HOME/tlaplus-examples/specifications/echo/MCEcho.tla" 75 "$HOME/tlaplus-examples/specifications/echo/MCEcho.cfg" 1

# GameOfLife from tlaplus/Examples - Conway's Game of Life
# Tests large state space (65536 states) with cellular automata rules
run_check "GameOfLife" "$HOME/tlaplus-examples/specifications/GameOfLife/GameOfLife.tla" 65536 "" 1

# HourClock from Specifying Systems - Lamport's classic example
# Tests simple temporal behavior with cyclic state space
run_check "HourClock" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/HourClock/HourClock.tla" 12 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/HourClock/HourClock.cfg" 1

# HourClock2 from Specifying Systems - variation with different Init
run_check "HourClock2" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/HourClock/HourClock2.tla" 12 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/HourClock/HourClock2.cfg" 1

# SKIPPED: SimTokenRing - designed for TLC's -generate mode, not exhaustive model checking
# The spec has ASSUME TLCGet("config").mode = "generate" which fails in bfs/check mode.
# Use `tla simulate` instead if you want to run this spec (it sets mode="generate").
# SimTokenRing is a statistics collection spec, not a model checking correctness test.
echo "[ SKIP ] SimTokenRing - requires 'generate' mode (use 'tla simulate' instead)"
SKIP=$((SKIP + 1))

# clean from tlaplus/Examples (glowingRaccoon) - pipeline cleaning
# Tests simple concurrent state machine
run_check "clean" "$HOME/tlaplus-examples/specifications/glowingRaccoon/clean.tla" 63 "$HOME/tlaplus-examples/specifications/glowingRaccoon/clean.cfg" 1

# product from tlaplus/Examples (glowingRaccoon) - product pipeline
run_check "product" "$HOME/tlaplus-examples/specifications/glowingRaccoon/product.tla" 305 "$HOME/tlaplus-examples/specifications/glowingRaccoon/product.cfg" 1

# stages from tlaplus/Examples (glowingRaccoon) - staged pipeline
run_check "stages" "$HOME/tlaplus-examples/specifications/glowingRaccoon/stages.tla" 83 "$HOME/tlaplus-examples/specifications/glowingRaccoon/stages.cfg" 1

# TwoPhase from tlaplus/Examples (transaction_commit) - Two-phase commit protocol
# Tests distributed transaction commit with resource managers
run_check "TwoPhase" "$HOME/tlaplus-examples/specifications/transaction_commit/TwoPhase.tla" 288 "$HOME/tlaplus-examples/specifications/transaction_commit/TwoPhase.cfg" 1

# AsynchInterface from SpecifyingSystems - Asynchronous interface
# Tests simple send/receive with type invariant
run_check "AsynchInterface" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/AsynchronousInterface/AsynchInterface.tla" 12 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/AsynchronousInterface/AsynchInterface.cfg" 1

# CoffeeCan100Beans from tlaplus/Examples - Coffee can problem with 100 beans
# Tests combinatorial state space with loop invariant (skip liveness)
run_check "CoffeeCan100Beans" "$HOME/tlaplus-examples/specifications/CoffeeCan/CoffeeCan.tla" 5150 "$HOME/tlaplus-examples/specifications/CoffeeCan/CoffeeCan100Beans.cfg" 1

# ReadersWriters from tlaplus/Examples - Classic readers-writers concurrency problem
# Tests mutual exclusion with multiple readers/writers (skip liveness - complex temporal)
run_check "ReadersWriters" "$HOME/tlaplus-examples/specifications/ReadersWriters/MC.tla" 21527 "$HOME/tlaplus-examples/specifications/ReadersWriters/MC.cfg" 1

# MCMajority from tlaplus/Examples - Boyer-Moore majority vote algorithm
# Tests voting correctness invariants with 1092 initial states
run_check "MCMajority" "$HOME/tlaplus-examples/specifications/Majority/MCMajority.tla" 2733 "$HOME/tlaplus-examples/specifications/Majority/MCMajority.cfg" 1

# MCInternalMemory from SpecifyingSystems - Internal memory abstraction
# Tests request/response memory interface with 4408 states
run_check "MCInternalMemory" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/CachingMemory/MCInternalMemory.tla" 4408 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/CachingMemory/MCInternalMemory.cfg" 1

# LiveHourClock from SpecifyingSystems - Hour clock with liveness
# Tests simple temporal behavior with liveness properties (skip liveness for safety check)
run_check "LiveHourClock" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/Liveness/LiveHourClock.tla" 12 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/Liveness/LiveHourClock.cfg" 1

# MCLiveInternalMemory from SpecifyingSystems - Internal memory with liveness
# Tests liveness properties with 4408 states (skip liveness for safety check)
run_check "MCLiveInternalMemory" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/Liveness/MCLiveInternalMemory.tla" 4408 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/Liveness/MCLiveInternalMemory.cfg" 1

# nbacg_guer01 from tlaplus/Examples - Non-blocking atomic commitment
# Tests distributed atomic commitment with 24922 states (skip liveness)
run_check "nbacg_guer01" "$HOME/tlaplus-examples/specifications/nbacg_guer01/nbacg_guer01.tla" 24922 "$HOME/tlaplus-examples/specifications/nbacg_guer01/nbacg_guer01.cfg" 1

# test16 - one-tuples: tuple literals, quantifiers, comprehensions
run_eval "test16" "$REPO_ROOT/test_specs/test16.tla" 1 "$REPO_ROOT/test_specs/test16.cfg"

# test19 - large initial state space (400K states - actual model checking test!)
run_check "test19" "$REPO_ROOT/test_specs/test19.tla" 400000 "$REPO_ROOT/test_specs/test19.cfg" 1

# test35 - Sequences module: Seq, \o, Len, Append, Head, Tail, SubSeq, SelectSeq
run_eval "test35" "$REPO_ROOT/test_specs/test35.tla" 1 "$REPO_ROOT/test_specs/test35.cfg"

# test37 - FiniteSets module: IsFiniteSet, Cardinality
run_eval "test37" "$REPO_ROOT/test_specs/test37.tla" 1 "$REPO_ROOT/test_specs/test37.cfg"

# TLAPSTest - TLAPS module operators (7 states - tests state transitions too)
run_check "TLAPSTest" "$REPO_ROOT/test_specs/TLAPSTest.tla" 7 "$REPO_ROOT/test_specs/TLAPSTest.cfg" 1

# AddTwoTest - TLAPS operators (5 states - tests state transitions too)
run_check "AddTwoTest" "$REPO_ROOT/test_specs/AddTwoTest.tla" 5 "$REPO_ROOT/test_specs/AddTwoTest.cfg" 1

# test11 - DOMAIN and Function Sets
run_eval "test11" "$REPO_ROOT/test_specs/test11.tla" 1 "$REPO_ROOT/test_specs/test11.cfg"

# Github407 - existential quantifier with set union (4 states - model checking)
run_check "Github407" "$REPO_ROOT/test_specs/Github407.tla" 4 "$REPO_ROOT/test_specs/Github407.cfg" 1

# Github1145 - SubSeq/EXCEPT regression
run_eval "Github1145" "$REPO_ROOT/test_specs/Github1145.tla" 1 "$REPO_ROOT/test_specs/Github1145.cfg"

# test40 - Naturals module: +, -, *, ^, \div, %
run_eval "test40" "$REPO_ROOT/test_specs/test40.tla" 1 "$REPO_ROOT/test_specs/test40.cfg" "--no-deadlock"

# test41 - Integers module: negative numbers, Int membership
run_eval "test41" "$REPO_ROOT/test_specs/test41.tla" 1 "$REPO_ROOT/test_specs/test41.cfg" "--no-deadlock"

# TestFloorDiv631 - Floor division semantics (#631): (-3) \div 2 = -2, (-3) % 2 = 1
# Regression test: TLA+ uses floor-division (Euclidean), not truncation toward zero
run_eval "TestFloorDiv631" "$REPO_ROOT/tests/tlc_comparison/repros/floor_division_631/TestFloorDiv631.tla" 1 "$REPO_ROOT/tests/tlc_comparison/repros/floor_division_631/TestFloorDiv631.cfg" "--no-deadlock"

# test46 - \prec operator, UNION comprehension (6 states - model checking)
run_check "test46" "$REPO_ROOT/test_specs/test46.tla" 6 "$REPO_ROOT/test_specs/test46.cfg" 1 "--no-deadlock"

# test47 - EXTENDS with multiple modules (3 states - model checking)
run_check "test47" "$REPO_ROOT/test_specs/test47.tla" 3 "$REPO_ROOT/test_specs/test47.cfg" 1

# test32 - [A]_e and <<A>>_e stuttering-step expressions
run_eval "test32" "$REPO_ROOT/test_specs/test32.tla" 1 "$REPO_ROOT/test_specs/test32.cfg"

# Huang - Termination detection algorithm using dyadic rationals
# Tests DyadicRationals community module (Zero, One, Add, Half, IsDyadicRational)
# Requires passing Add as higher-order argument to FoldFunction
run_check "Huang" "$HOME/tlaplus-examples/specifications/Huang/Huang.tla" 81256 "$HOME/tlaplus-examples/specifications/Huang/Huang.cfg" 0

# SyncTerminationDetection - Termination detection with synchronous rounds
# Tests INSTANCE with parameter substitution and state space enumeration
run_check "SyncTerminationDetection" "$HOME/tlaplus-examples/specifications/ewd840/SyncTerminationDetection.tla" 129 "$HOME/tlaplus-examples/specifications/ewd840/SyncTerminationDetection.cfg" 0

# MCFindHighest - Find highest element in array (uses TLAPS proof stub)
# Tests TLAPS module stub support and loop invariants
run_check "MCFindHighest" "$HOME/tlaplus-examples/specifications/LearnProofs/MCFindHighest.tla" 742 "$HOME/tlaplus-examples/specifications/LearnProofs/MCFindHighest.cfg" 1

# Lock - Simple lock with auxiliary variables (uses TLAPS proof stub)
# Tests TLAPS stub support and lock semantics
run_check "Lock" "$HOME/tlaplus-examples/specifications/locks_auxiliary_vars/Lock.tla" 12 "$HOME/tlaplus-examples/specifications/locks_auxiliary_vars/Lock.cfg" 1

# Peterson - Peterson's mutual exclusion algorithm (uses TLAPS proof stub)
# Tests TLAPS stub support and refinement proofs
run_check "Peterson" "$HOME/tlaplus-examples/specifications/locks_auxiliary_vars/Peterson.tla" 42 "$HOME/tlaplus-examples/specifications/locks_auxiliary_vars/Peterson.cfg" 0

# MCBakery - Lamport's bakery algorithm with TLAPS proof annotations
# Tests TLAPS module support with proof-annotated spec (uses custom config for regular Spec)
run_check "MCBakery" "$HOME/tlaplus-examples/specifications/Bakery-Boulangerie/MCBakery.tla" 2303 "$REPO_ROOT/test_specs/MCBakery.cfg" 1

# MCPaxos - Paxos consensus algorithm model checking spec
# Tests nested INSTANCE with implicit substitution (Value from outer module)
run_check "MCPaxos" "$HOME/tlaplus-examples/specifications/Paxos/MCPaxos.tla" 25 "$HOME/tlaplus-examples/specifications/Paxos/MCPaxos.cfg" 0

# MCVoting - Voting layer of Paxos
# Tests INSTANCE with implicit substitution: Consensus!chosen uses Voting's chosen operator
# This was previously broken - fixed in #510 by handling implicit VARIABLE substitution
run_check "MCVoting" "$HOME/tlaplus-examples/specifications/Paxos/MCVoting.tla" 77 "$HOME/tlaplus-examples/specifications/Paxos/MCVoting.cfg" 0

# MCYoYoPruning - YoYo leader election with pruning optimization
# Tests ENABLED operator in invariants (FinishIffTerminated uses ENABLED Next)
# Fixed in #512 - ENABLED invariants now route through liveness checker
run_check "MCYoYoPruning" "$HOME/tlaplus-examples/specifications/YoYo/MCYoYoPruning.tla" 102 "$HOME/tlaplus-examples/specifications/YoYo/MCYoYoPruning.cfg" 0

# SingleLaneBridge - Cars crossing a single-lane bridge
# Tests liveness properties with 3605 states and fair progress
run_check "SingleLaneBridge" "$HOME/tlaplus-examples/specifications/SingleLaneBridge/MC.tla" 3605 "$HOME/tlaplus-examples/specifications/SingleLaneBridge/MC.cfg" 0

# SimplifiedFastPaxos/Paxos - Simplified Paxos from Lamport's tutorial
# Tests consensus with symmetry reduction (174 permutations)
run_check "SimplifiedPaxos" "$HOME/tlaplus-examples/specifications/SimplifiedFastPaxos/Paxos.tla" 1207 "$HOME/tlaplus-examples/specifications/SimplifiedFastPaxos/Paxos.cfg" 0

# SimplifiedFastPaxos/FastPaxos - Fast Paxos variant
# Tests consensus with fast path optimization (25617 states, 70s runtime)
run_check "SimplifiedFastPaxos" "$HOME/tlaplus-examples/specifications/SimplifiedFastPaxos/FastPaxos.tla" 25617 "$HOME/tlaplus-examples/specifications/SimplifiedFastPaxos/FastPaxos.cfg" 0

# MCKVsnap - Key-Value store with snapshot isolation
# Tests snapshot isolation invariant and termination (32293 states)
run_check "MCKVsnap" "$HOME/tlaplus-examples/specifications/KeyValueStore/MCKVsnap.tla" 32293 "$HOME/tlaplus-examples/specifications/KeyValueStore/MCKVsnap.cfg" 0

# EnvironmentController-smoke - Eventually perfect failure detector (large)
# Smoke test (limit) to ensure INSTANCE inlining preserves instance-local ops (Age_Channel!Unpack).
run_check "EnvironmentController-smoke" "$HOME/tlaplus-examples/specifications/detector_chan96/EnvironmentController.tla" 1001 "$HOME/tlaplus-examples/specifications/detector_chan96/EnvironmentController.cfg" 1 "--no-trace --max-states 1000"

# MCInnerFIFO from SpecifyingSystems - Inner FIFO queue implementation
# Tests buffered channel with send/receive semantics (3864 states)
run_check "MCInnerFIFO" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/FIFO/MCInnerFIFO.tla" 3864 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/FIFO/MCInnerFIFO.cfg" 1

# MCtcp - TCP connection state machine
# Tests TCP three-way handshake and state transitions (1182 states)
run_check "MCtcp" "$HOME/tlaplus-examples/specifications/tcp/MCtcp.tla" 1182 "$HOME/tlaplus-examples/specifications/tcp/MCtcp.cfg" 0

# nbacc_ray97 - Non-blocking atomic commitment with raynal97
# Tests distributed commit protocol (3016 states)
run_check "nbacc_ray97" "$HOME/tlaplus-examples/specifications/nbacc_ray97/nbacc_ray97.tla" 3016 "$HOME/tlaplus-examples/specifications/nbacc_ray97/nbacc_ray97.cfg" 1

# MCInnerSequential from SpecifyingSystems - Sequential execution model
# Tests linearizable operations with refinement (3528 states)
run_check "MCInnerSequential" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/AdvancedExamples/MCInnerSequential.tla" 3528 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/AdvancedExamples/MCInnerSequential.cfg" 0

# MCWriteThroughCache from SpecifyingSystems - Write-through cache with memory queue
# Tests LET binding error handling: LET r == Head(memQ)[2] IN /\ guard /\ ...
# Previously failed with IndexOutOfBounds when memQ empty (5196 states, TLC verified)
run_check "MCWriteThroughCache" "$HOME/tlaplus-examples/specifications/SpecifyingSystems/CachingMemory/MCWriteThroughCache.tla" 5196 "$HOME/tlaplus-examples/specifications/SpecifyingSystems/CachingMemory/MCWriteThroughCache.cfg" 1

# SpanTree from SpanningTree - Distributed spanning tree construction
# Tests broadcast-based spanning tree with liveness properties (1236 states, TLC verified)
run_check "SpanTree" "$HOME/tlaplus-examples/specifications/SpanningTree/SpanTree.tla" 1236 "$HOME/tlaplus-examples/specifications/SpanningTree/SpanTree.cfg" 0

# Prisoners - 100 prisoners lightbulb problem
# Tests counting strategy with safety and liveness (214 states, TLC verified)
run_check "Prisoners" "$HOME/tlaplus-examples/specifications/Prisoners/Prisoners.tla" 214 "$HOME/tlaplus-examples/specifications/Prisoners/Prisoners.cfg" 0

# Prisoner - Single-switch prisoner puzzle variant
# Tests Init with negated constants (~Light_Unknown) in disjunctions (16 states, TLC verified)
run_check "Prisoner" "$HOME/tlaplus-examples/specifications/Prisoners_Single_Switch/Prisoner.tla" 16 "$HOME/tlaplus-examples/specifications/Prisoners_Single_Switch/Prisoner.cfg" 0

# Chameneos - Concurrency benchmark from Erlang shootout
# Tests rendezvous-style meeting with color changes (34534 states, TLC verified)
run_check "Chameneos" "$HOME/tlaplus-examples/specifications/Chameneos/Chameneos.tla" 34534 "$HOME/tlaplus-examples/specifications/Chameneos/Chameneos.cfg" 1

# MCEWD687a - Dijkstra's distributed termination detection
# Tests tree-based termination detection (18028 states, TLC verified)
run_check "MCEWD687a" "$HOME/tlaplus-examples/specifications/ewd687a/MCEWD687a.tla" 18028 "$HOME/tlaplus-examples/specifications/ewd687a/MCEWD687a.cfg" 0

# === AUDIT 2026-01-05: Specs that were incorrectly skipped ===

# MCYoYoNoPruning - YoYo leader election (was marked as missing IsUndirectedGraph)
run_check "MCYoYoNoPruning" "$HOME/tlaplus-examples/specifications/YoYo/MCYoYoNoPruning.tla" 60 "$HOME/tlaplus-examples/specifications/YoYo/MCYoYoNoPruning.cfg" 0

# Barriers - Multi-barrier synchronization (29279 states, TLC verified)
run_check "Barriers" "$HOME/tlaplus-examples/specifications/barriers/Barriers.tla" 29279 "$HOME/tlaplus-examples/specifications/barriers/Barriers.cfg" 0
}
