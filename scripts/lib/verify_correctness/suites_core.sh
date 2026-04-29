# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

run_verify_correctness_core_suite() {
# Core specs with expected state counts from TLC baseline
# Most specs skip liveness (5th argument=1) because they don't have liveness properties
# DieHard: NotSolved invariant violation is the point (finding big=4 solution)
run_check "DieHard" "$HOME/tlaplus-examples/specifications/DieHard/DieHard.tla" 14 "" 1 "" "invariant"
# Counter: Deadlock when x reaches MAX (5) - Next guard fails
run_check "Counter" "examples/Counter.tla" 6 "" 1 "" "deadlock"
run_check "Barrier" "$HOME/tlaplus-examples/specifications/barriers/Barrier.tla" 64 "" 1
run_check "DiningPhilosophers" "$HOME/tlaplus-examples/specifications/DiningPhilosophers/DiningPhilosophers.tla" 67 "" 1
# MissionariesAndCannibals: Solution invariant violation is the point (all reach other bank)
run_check "MissionariesAndCannibals" "$HOME/tlaplus-examples/specifications/MissionariesAndCannibals/MissionariesAndCannibals.tla" 61 "" 1 "" "invariant"
run_check "TCommit" "$HOME/tlaplus-examples/specifications/transaction_commit/TCommit.tla" 34 "$HOME/tlaplus-examples/specifications/transaction_commit/TCommit.cfg" 1
run_check "MCChangRoberts" "$HOME/tlaplus-examples/specifications/chang_roberts/MCChangRoberts.tla" 137 "$HOME/tlaplus-examples/specifications/chang_roberts/MCChangRoberts.cfg" 1

# MCLamportMutex - smoke test only (full run is ~724K states and slow in sequential mode)
run_check "MCLamportMutex-smoke" "$HOME/tlaplus-examples/specifications/lamport_mutex/MCLamportMutex.tla" 1000 "$HOME/tlaplus-examples/specifications/lamport_mutex/MCLamportMutex.cfg" 1 "--max-states 1000"

# SimpleAllocator - resource allocator with quantified fairness constraints
# Tests \A c \in Clients: WF_vars(Action(c)) style fairness
run_check "SimpleAllocator" "$HOME/tlaplus-examples/specifications/allocator/SimpleAllocator.tla" 400 "$HOME/tlaplus-examples/specifications/allocator/SimpleAllocator.cfg" 1

# SchedulingAllocator - recursive PermSeqs + quantified fairness extracted from Liveness operator
# Tests recursive LET function definitions and fairness extraction from conjuncted operator references.
run_check "SchedulingAllocator" "$HOME/tlaplus-examples/specifications/allocator/SchedulingAllocator.tla" 1690 "$HOME/tlaplus-examples/specifications/allocator/SchedulingAllocator.cfg" 0

# EWD840 with liveness checking enabled (tests the Liveness property)
# Uses custom config that excludes TDSpec (has module reference issues)
run_check "EWD840+Liveness" "$HOME/tlaplus-examples/specifications/ewd840/EWD840.tla" 302 "$REPO_ROOT/test_specs/EWD840_Liveness.cfg" 0

# EnabledFairness tests ENABLED semantics with WF_vars(Next) disjunctive actions
# Tests that []<>(x = MAX) and []<>(x = 0) hold with weak fairness
run_check "EnabledFairness+Liveness" "$REPO_ROOT/test_specs/EnabledFairness.tla" 4 "$REPO_ROOT/test_specs/EnabledFairness.cfg" 0

# EnabledInAction tests ENABLED operator used inside action guards
# Regression test for bug: TLA2 wasn't evaluating ENABLED in action guards
# IncIfDecEnabled == /\ ENABLED Dec /\ Inc - only enabled when x > 0 (Dec can fire)
# Expected: 6 states (x = 5..10), matches TLC exactly
run_check "EnabledInAction" "$REPO_ROOT/test_specs/EnabledInAction.tla" 6 "$REPO_ROOT/test_specs/EnabledInAction.cfg" 1 "--no-deadlock"

# BidirectionalTransitions from TLC baseline (test-model/)
# Tests WF with disjunctive actions and modular arithmetic
# Test1: A \/ B with mod 3 arithmetic (3 states)
run_check "BidirectionalTransitions1" "$REPO_ROOT/test_specs/BidirectionalTransitions.tla" 3 "$REPO_ROOT/test_specs/BidirectionalTransitions1.cfg" 1

# Test2: C \/ D with mod 4 arithmetic (4 states)
run_check "BidirectionalTransitions2" "$REPO_ROOT/test_specs/BidirectionalTransitions.tla" 4 "$REPO_ROOT/test_specs/BidirectionalTransitions2.cfg" 1

# ============================================================================
# NEGATIVE TESTS (W10: Trace comparison between TLA2 and TLC)
# These specs are EXPECTED to find violations. We verify both tools:
# 1. Find the same type of error (invariant/deadlock/liveness)
# 2. Produce traces of the same length
# ============================================================================
echo ""
echo "=== Negative Tests (error trace comparison) ==="

# DieHard: NotSolved invariant violation expected - finding big=4 is the solution
run_negative "DieHard-trace" "$HOME/tlaplus-examples/specifications/DieHard/DieHard.tla" "" "invariant"

# Counter: Deadlock expected when x reaches MAX (5) - Next guard fails
run_negative "Counter-trace" "$REPO_ROOT/examples/Counter.tla" "" "deadlock"

# MissionariesAndCannibals: Solution invariant violation - all reach other bank
run_negative "MissionariesAndCannibals-trace" "$HOME/tlaplus-examples/specifications/MissionariesAndCannibals/MissionariesAndCannibals.tla" "" "invariant"

# ============================================================================
# EVALUATOR-ONLY TESTS (1 state, Next=UNCHANGED)
# These test expression evaluation via ASSUME/invariants, NOT model checking.
# They have no state transitions - only test the evaluator on the Init state.
# WARNING: These do NOT test the model checker's successor generation!
# ============================================================================
echo ""
echo "=== Evaluator Tests (expression evaluation, not model checking) ==="

# BagsTest - Tests Bags module operators via 126 ASSUME statements
run_eval "BagsTest" "$REPO_ROOT/test_specs/BagsTest.tla" 1 "$REPO_ROOT/test_specs/BagsTest.cfg" "--no-deadlock"

# TLCExtTest - tests TLCModelValue creation and equality via ASSUME statements
run_eval "TLCExtTest" "$REPO_ROOT/test_specs/TLCExtTest.tla" 1 "$REPO_ROOT/test_specs/TLCExtTest.cfg" "--no-deadlock"

# EmptyExistentialQuantifier - tests that \E i \in {}: P is FALSE
run_eval "EmptyExistentialQuantifier" "$REPO_ROOT/test_specs/EmptyExistentialQuantifier.tla" 1 "$REPO_ROOT/test_specs/EmptyExistentialQuantifier.cfg" "--no-deadlock"

# SubSeqExceptTest - tests SubSeq/EXCEPT behavior on seq-like functions
run_eval "SubSeqExceptTest" "$REPO_ROOT/test_specs/SubSeqExceptTest.tla" 1 "$REPO_ROOT/test_specs/SubSeqExceptTest.cfg" "--no-deadlock"

# FunctionOverrideTest - tests @@ (function override) across Records/Seqs/Funcs
run_eval "FunctionOverrideTest" "$REPO_ROOT/test_specs/FunctionOverrideTest.tla" 1 "$REPO_ROOT/test_specs/FunctionOverrideTest.cfg" "--no-deadlock"

# ConstLevelInvariant - constant-level invariant C \subseteq Nat
# Tests that invariants referencing only constants work correctly with infinite sets
# Bug fixed in #528: compiled_guard.rs now handles ModelValue (Nat/Int/Real) in Subseteq
run_check "ConstLevelInvariant" "$REPO_ROOT/test_specs/ConstLevelInvariant.tla" 2 "$REPO_ROOT/test_specs/ConstLevelInvariant.cfg"

# test30 - operator replacement via config
run_eval "test30" "$REPO_ROOT/test_specs/test30.tla" 1 "$REPO_ROOT/test_specs/test30.cfg"

# test7 - predicate logic (\E, \A, CHOOSE)
run_eval "test7" "$REPO_ROOT/test_specs/test7.tla" 1 "$REPO_ROOT/test_specs/test7.cfg"

# test14 - IF/THEN/ELSE, CASE/OTHER, nested junctions
run_eval "test14" "$REPO_ROOT/test_specs/test14.tla" 1 "$REPO_ROOT/test_specs/test14.cfg"

# test21 - priming semantics: primed operator calls, LET/IN with primes
# Note: This has 2 states so it's a mini model-checking test, not pure evaluator
run_check "test21" "$REPO_ROOT/test_specs/test21.tla" 2 "$REPO_ROOT/test_specs/test21.cfg" 1

# test24 - UNCHANGED semantics with quantifiers, CHOOSE, DOMAIN
# Note: This has 2 states so it's a mini model-checking test, not pure evaluator
run_check "test24" "$REPO_ROOT/test_specs/test24.tla" 2 "$REPO_ROOT/test_specs/test24.cfg" 1

# test1 - set equality: literals, comprehensions, SUBSET, UNION, intervals
run_eval "test1" "$REPO_ROOT/test_specs/test1.tla" 1 "$REPO_ROOT/test_specs/test1.cfg"

# test2 - function equality: funcs vs tuples, funcs vs records, EXCEPT
run_eval "test2" "$REPO_ROOT/test_specs/test2.tla" 1 "$REPO_ROOT/test_specs/test2.cfg"

# test3 - function application, EXCEPT with @[idx] syntax
run_eval "test3" "$REPO_ROOT/test_specs/test3.tla" 1 "$REPO_ROOT/test_specs/test3.cfg"

# test4 - fingerprinting of sets: different representations produce same state
run_eval "test4" "$REPO_ROOT/test_specs/test4.tla" 1 "$REPO_ROOT/test_specs/test4.cfg"

# test5 - cartesian product (\X) semantics over finite/infinite sets
run_eval "test5" "$REPO_ROOT/test_specs/test5.tla" 1 "$REPO_ROOT/test_specs/test5.cfg"

# test6 - propositional logic: /\, \/, ~, =>, <=>, \equiv, BOOLEAN
run_eval "test6" "$REPO_ROOT/test_specs/test6.tla" 1 "$REPO_ROOT/test_specs/test6.cfg"

# test8 - set operators: \cup, \cap, \subseteq, \, Seq operations
run_eval "test8" "$REPO_ROOT/test_specs/test8.tla" 1 "$REPO_ROOT/test_specs/test8.cfg"

# test15 - empty set handling: SUBSET {}, UNION {}, quantifiers over {}, 1..0
run_eval "test15" "$REPO_ROOT/test_specs/test15.tla" 1 "$REPO_ROOT/test_specs/test15.cfg"

# test9 - set constructors: {x \in S : P(x)}, {e(x) : x \in S}
run_eval "test9" "$REPO_ROOT/test_specs/test9.tla" 1 "$REPO_ROOT/test_specs/test9.cfg"

# test10 - function definition/application: multi-arg funcs, EXCEPT
run_eval "test10" "$REPO_ROOT/test_specs/test10.tla" 1 "$REPO_ROOT/test_specs/test10.cfg"
}
