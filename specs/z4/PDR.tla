--------------------------- MODULE PDR ---------------------------
\* Property-Directed Reachability (PDR/IC3) for Safety Verification
\*
\* Models the PDR algorithm used in z4-chc for Constrained Horn Clause
\* solving. The algorithm maintains a sequence of frames (over-approximations
\* of reachable states at each depth) and refines them by blocking
\* counterexample cubes.
\*
\* Design choice: frames are SETS OF STATES rather than sets of clauses.
\* This is the semantic interpretation: frame F_i is the set of states
\* that the PDR frame over-approximation allows at depth i.
\*
\* Frame indexing (1-based TLA+ sequences):
\*   frames[1] = F_1: first over-approximation (initialized to Safety)
\*   frames[2] = F_2: second over-approximation
\*   ...
\*   frames[k] = F_k: frontier frame
\*
\* Init is NOT stored as a frame; it is used directly for the base case.
\* This matches z4-chc where frame[0] represents the initial constraint
\* and obligations at level 0 are checked against Init.
\*
\* Key PDR invariants:
\*   - Init \subseteq F_1 (initial states are in every frame)
\*   - F_{i+1} \subseteq F_i (monotonicity)
\*   - F_i \subseteq Safety for all i >= 1 (safety)
\*   - Fixpoint F_i = F_{i+1} implies safety (inductive invariant found)
\*
\* Reference: z4-chc/src/pdr/ (PdrSolver, strengthen, check_fixed_point)
\*           Bradley, "SAT-Based Model Checking without Unrolling" (VMCAI 2011)
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Copyright 2026 Andrew Yates. | Apache 2.0

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    NumProps,   \* Number of boolean propositions (e.g. 2 or 3)
    Init,       \* Set of initial states (each state is a SUBSET of 1..NumProps)
    Trans,      \* Transition relation: set of <<source, dest>> state pairs
    Safety,     \* Set of safe states (SUBSET of SUBSET(1..NumProps))
    MaxDepth    \* Maximum number of frames (bounds exploration for model checking)

VARIABLES
    frames,       \* Sequence of frames. Each frame is a SET OF STATES.
                  \* frames[i] = F_i, the over-approximation at depth i.
    obligations,  \* Set of <<state, frame_index>> pairs to block.
                  \* frame_index is in 1..Len(frames).
    status        \* "running", "safe", "unsafe"

vars == <<frames, obligations, status>>

\* ==== All possible states ====

AllStates == SUBSET (1..NumProps)

\* ==== Predecessor helpers ====

\* States in a given set that can transition to state s
PredecessorsIn(stateSet, s) ==
    {p \in stateSet : <<p, s>> \in Trans}

\* ==== Initial state ====

InitPDR ==
    \* Start with one frame F_1 = Safety (all safe states).
    \* Init must be a subset of Safety for the system to be non-trivially unsafe.
    /\ frames = << Safety >>
    /\ obligations = {}
    /\ status = IF Init \subseteq Safety
                THEN "running"
                ELSE "unsafe"  \* Init immediately violates safety

\* ==== Actions ====

\* Unfold: add a new frame, extending the exploration depth.
\* The new frame starts as a copy of the current last frame (inherits all
\* blocking constraints). Corresponds to z4-chc's push_frame().
Unfold ==
    /\ status = "running"
    /\ obligations = {}
    /\ Len(frames) < MaxDepth
    /\ frames' = Append(frames, frames[Len(frames)])
    /\ UNCHANGED <<obligations, status>>

\* CreateObligation: discover a bad state in the current frontier frame
\* and create an obligation to block it. Models z4-chc's strengthen()
\* creating proof obligations from query clauses.
CreateObligation ==
    /\ status = "running"
    /\ LET k == Len(frames)
       IN \E s \in frames[k] \ Safety :
          /\ <<s, k>> \notin obligations
          /\ obligations' = obligations \union {<<s, k>>}
          /\ UNCHANGED <<frames, status>>

\* Block: process an obligation <<s, i>>. This is the core PDR step.
\*
\* At frame i > 1: check if s has a predecessor in frame i-1.
\*   - No predecessor: block s (remove from frames[i]).
\*   - Has predecessor p: push obligation to <<p, i-1>>.
\*
\* At frame i = 1: check if s is reachable from Init in one step.
\*   - Reachable from Init: genuine counterexample -> UNSAFE.
\*   - Not reachable from Init: block s at frame 1.
\*
\* An obligation is also resolved UNSAFE if the state s itself is in Init
\* (at frame 1), because Init -> s -> ... -> bad_state is a counterexample.
\*
\* Corresponds to z4-chc's strengthen() obligation loop with
\* BlockResult::Blocked vs BlockResult::Reachable.
Block ==
    /\ status = "running"
    /\ \E ob \in obligations :
        LET s == ob[1]
            i == ob[2]
        IN
        /\ s \in frames[i]  \* state still in frame (not yet blocked)
        /\ IF i = 1
           THEN
              \* Base case: check reachability from Init
              IF s \in Init \/ PredecessorsIn(Init, s) /= {}
              THEN
                  \* Init can reach s (directly or in one step).
                  \* Combined with the obligation chain, this yields a
                  \* counterexample from Init to the bad state.
                  /\ status' = "unsafe"
                  /\ obligations' = obligations \ {ob}
                  /\ UNCHANGED frames
              ELSE
                  \* s is not reachable from Init: block at frame 1
                  /\ frames' = [frames EXCEPT ![1] = frames[1] \ {s}]
                  /\ obligations' = obligations \ {ob}
                  /\ UNCHANGED status
           ELSE
              \* Inductive case: check predecessors in prior frame
              IF PredecessorsIn(frames[i - 1], s) = {}
              THEN
                  \* No predecessor: block s at frame i
                  /\ frames' = [frames EXCEPT ![i] = frames[i] \ {s}]
                  /\ obligations' = obligations \ {ob}
                  /\ UNCHANGED status
              ELSE
                  \* Has predecessor: push obligation backwards
                  \E p \in PredecessorsIn(frames[i - 1], s) :
                      /\ obligations' = (obligations \ {ob}) \union {<<p, i - 1>>}
                      /\ UNCHANGED <<frames, status>>

\* Propagate: strengthen frame i+1 by removing a state that is not
\* reachable from frame i in one transition step, and is not in Init.
\* Models z4-chc's push_lemmas(): pushing blocking clauses forward when
\* they are inductive relative to the next frame.
Propagate ==
    /\ status = "running"
    /\ \E i \in 1..(Len(frames) - 1) :
        \E s \in frames[i + 1] :
            /\ PredecessorsIn(frames[i], s) = {}
            /\ s \notin Init
            /\ frames' = [frames EXCEPT ![i + 1] = frames[i + 1] \ {s}]
            /\ UNCHANGED <<obligations, status>>

\* DetectFixpoint: if two consecutive frames have the same state set,
\* the algorithm has converged. The shared frame is an inductive invariant
\* that proves safety. Corresponds to z4-chc's check_fixed_point().
DetectFixpoint ==
    /\ status = "running"
    /\ \E i \in 1..(Len(frames) - 1) :
        /\ frames[i] = frames[i + 1]
        /\ status' = "safe"
        /\ UNCHANGED <<frames, obligations>>

\* Done: terminal state (stuttering when finished)
Done ==
    /\ status \in {"safe", "unsafe"}
    /\ UNCHANGED vars

Next == Unfold \/ CreateObligation \/ Block \/ Propagate
        \/ DetectFixpoint \/ Done

\* ==== Invariants ====

\* Frame monotonicity: each frame is a subset of the previous one.
\* F_1 is the most permissive, F_k the tightest.
FrameMonotonicity ==
    \A i \in 1..(Len(frames) - 1) :
        frames[i + 1] \subseteq frames[i]

\* All initial states are in F_1 (the first frame)
InitContainment ==
    status /= "unsafe" => Init \subseteq frames[1]

\* Every frame only allows safe states (unless system is unsafe).
SafetyContainment ==
    status /= "unsafe" =>
        \A i \in 1..Len(frames) :
            frames[i] \subseteq Safety

\* Type invariant
TypeOK ==
    /\ Len(frames) >= 1
    /\ status \in {"running", "safe", "unsafe"}
    /\ \A i \in 1..Len(frames) :
        frames[i] \subseteq AllStates
    /\ \A ob \in obligations :
        /\ ob[1] \in AllStates
        /\ ob[2] \in 1..Len(frames)

Spec == InitPDR /\ [][Next]_vars
=============================================================================
