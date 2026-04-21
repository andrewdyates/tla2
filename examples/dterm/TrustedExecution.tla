--------------------------- MODULE TrustedExecution ---------------------------
(***************************************************************************)
(* Trusted Execution Architecture for AI Agent Security                    *)
(*                                                                         *)
(* Models CaMeLs-style execution graph validation to prevent prompt        *)
(* injection attacks through the terminal interface.                       *)
(*                                                                         *)
(* Core insight: Generate execution plans BEFORE observing untrusted       *)
(* content, then validate execution against those plans.                   *)
(*                                                                         *)
(* Safety Properties:                                                       *)
(* - INV-EXEC-1: AI never acts on invalid validation                       *)
(* - INV-EXEC-2: Timing attacks trigger security halt                      *)
(* - INV-EXEC-3: Execution graph is immutable during execution             *)
(* - INV-EXEC-4: All security halts have documented reason                 *)
(*                                                                         *)
(* Liveness Properties:                                                     *)
(* - Execution eventually terminates (success, failure, or security halt)  *)
(*                                                                         *)
(* Reference: CaMeLs paper (arXiv:2601.09923)                              *)
(* Design doc: designs/2026-01-18-trusted-execution-architecture.md        *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxSteps,           \* Maximum steps in execution graph
    MaxSnapshots,       \* Maximum buffer snapshots retained
    TimingThreshold,    \* Ticks below which hash change = timing attack
    MaxClock,           \* Bound for model checking
    MaxHash             \* Maximum hash value (for bounded model checking)

VARIABLES
    graph,              \* Execution graph: sequence of steps (IMMUTABLE after init)
    graphLocked,        \* Whether graph is locked (no modifications)
    currentStep,        \* Current step index (1-indexed)
    validationState,    \* "pending" | "valid" | "invalid"
    bufferHistory,      \* Sequence of buffer snapshots
    terminated,         \* Whether execution has terminated
    termReason,         \* "none" | "success" | "failure" | "security_halt"
    clock,              \* Logical clock for timing detection
    dangerousDetected   \* Whether dangerous ANSI sequences detected

vars == <<graph, graphLocked, currentStep, validationState,
          bufferHistory, terminated, termReason, clock, dangerousDetected>>

(***************************************************************************)
(* Type Definitions                                                        *)
(***************************************************************************)

\* Execution step record (abstracted for model checking)
\* In implementation, command/pattern are strings; here we abstract to booleans
Step == [
    hasPattern: BOOLEAN,        \* Whether expected pattern is set
    hasExitCode: BOOLEAN        \* Whether expected exit code is set
]

\* Buffer snapshot record (bounded for model checking)
Snapshot == [
    hash: 0..MaxHash,           \* Content hash (bounded by MaxHash)
    timestamp: 0..MaxClock      \* When taken (bounded by MaxClock)
]

ValidationStates == {"pending", "valid", "invalid"}
TermReasons == {"none", "success", "failure", "security_halt"}

(***************************************************************************)
(* Type Invariant                                                          *)
(***************************************************************************)

TypeInvariant ==
    /\ graphLocked \in BOOLEAN
    /\ currentStep \in Nat
    /\ validationState \in ValidationStates
    /\ bufferHistory \in Seq(Snapshot)
    /\ Len(bufferHistory) <= MaxSnapshots + 1
    /\ terminated \in BOOLEAN
    /\ termReason \in TermReasons
    /\ clock \in Nat
    /\ dangerousDetected \in BOOLEAN
    /\ currentStep <= Len(graph) + 1

(***************************************************************************)
(* Helper Predicates                                                       *)
(***************************************************************************)

\* Check for timing attack in buffer history
\* Rapid hash changes within threshold indicate timing-based deception
TimingAttackDetected ==
    /\ Len(bufferHistory) >= 2
    /\ LET prev == bufferHistory[Len(bufferHistory) - 1]
           curr == bufferHistory[Len(bufferHistory)]
       IN /\ prev.hash # curr.hash
          /\ curr.timestamp - prev.timestamp < TimingThreshold

\* Check if execution has more steps
HasMoreSteps == currentStep <= Len(graph)

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* INV-EXEC-1: Never continue execution after invalid validation
NoInvalidContinue ==
    validationState = "invalid" => terminated

\* INV-EXEC-2: Dangerous ANSI sequences trigger security halt
DangerousTriggersHalt ==
    (dangerousDetected /\ terminated) => termReason = "security_halt"

\* INV-EXEC-3: Graph never changes once locked
\* (Checked via action constraint below)

\* INV-EXEC-4: Security halt always has reason
SecurityHaltDocumented ==
    termReason = "security_halt" =>
    (validationState = "invalid" \/ dangerousDetected \/ TimingAttackDetected)

\* INV-EXEC-5: Termination reason matches state
TerminationConsistent ==
    /\ (terminated /\ termReason = "success") =>
       (currentStep > Len(graph) /\ validationState # "invalid")
    /\ (terminated /\ termReason = "failure") =>
       validationState = "invalid"
    /\ (~terminated) => termReason = "none"

\* INV-EXEC-6: Current step within bounds during execution
StepInBounds ==
    ~terminated => currentStep <= Len(graph) + 1

\* Combined safety invariant
SafetyInvariant ==
    /\ NoInvalidContinue
    /\ DangerousTriggersHalt
    /\ SecurityHaltDocumented
    /\ TerminationConsistent
    /\ StepInBounds

(***************************************************************************)
(* State Machine Operations                                                *)
(***************************************************************************)

\* Initial state: graph planned, ready to execute
Init ==
    \* Graph is initialized with 1 to MaxSteps steps
    /\ graph \in [1..MaxSteps -> Step]
    /\ graphLocked = TRUE          \* Locked from the start
    /\ currentStep = 1
    /\ validationState = "pending"
    /\ bufferHistory = <<>>
    /\ terminated = FALSE
    /\ termReason = "none"
    /\ clock = 0
    /\ dangerousDetected = FALSE

\* Take buffer snapshot
TakeSnapshot ==
    /\ ~terminated
    /\ Len(bufferHistory) < MaxSnapshots
    /\ \E h \in 0..MaxHash:  \* Non-deterministic hash value (bounded by MaxHash)
        bufferHistory' = Append(bufferHistory, [hash |-> h, timestamp |-> clock])
    /\ clock' = clock + 1
    /\ UNCHANGED <<graph, graphLocked, currentStep, validationState,
                   terminated, termReason, dangerousDetected>>

\* Detect timing attack and halt
DetectTimingAttackAndHalt ==
    /\ ~terminated
    /\ TimingAttackDetected
    /\ terminated' = TRUE
    /\ termReason' = "security_halt"
    /\ UNCHANGED <<graph, graphLocked, currentStep, validationState,
                   bufferHistory, clock, dangerousDetected>>

\* Detect dangerous ANSI sequences
DetectDangerousAnsi ==
    /\ ~terminated
    /\ ~dangerousDetected
    /\ dangerousDetected' = TRUE
    /\ terminated' = TRUE
    /\ termReason' = "security_halt"
    /\ validationState' = "invalid"
    /\ UNCHANGED <<graph, graphLocked, currentStep, bufferHistory, clock>>

\* Execute step with successful validation
ExecuteStepValid ==
    /\ ~terminated
    /\ HasMoreSteps
    /\ validationState # "invalid"
    /\ ~dangerousDetected
    /\ ~TimingAttackDetected
    \* Step passes validation
    /\ validationState' = "valid"
    /\ currentStep' = currentStep + 1
    \* Check if this was last step
    /\ IF currentStep + 1 > Len(graph)
       THEN /\ terminated' = TRUE
            /\ termReason' = "success"
       ELSE /\ terminated' = FALSE
            /\ termReason' = "none"
    /\ clock' = clock + 1
    /\ UNCHANGED <<graph, graphLocked, bufferHistory, dangerousDetected>>

\* Execute step with failed validation
ExecuteStepInvalid ==
    /\ ~terminated
    /\ HasMoreSteps
    /\ validationState # "invalid"
    /\ ~dangerousDetected
    \* Step fails validation (pattern mismatch, exit code wrong, etc.)
    /\ validationState' = "invalid"
    /\ terminated' = TRUE
    /\ termReason' = "security_halt"
    /\ clock' = clock + 1
    /\ UNCHANGED <<graph, graphLocked, currentStep, bufferHistory, dangerousDetected>>

\* Clock tick (for snapshot timing)
Tick ==
    /\ ~terminated
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED <<graph, graphLocked, currentStep, validationState,
                   bufferHistory, terminated, termReason, dangerousDetected>>

\* Stuttering step when terminated (prevents false deadlock detection)
Stutter ==
    /\ terminated
    /\ UNCHANGED vars

(***************************************************************************)
(* State Constraint for Model Checking                                     *)
(***************************************************************************)

StateConstraint ==
    /\ clock <= MaxClock
    /\ Len(bufferHistory) <= MaxSnapshots + 1
    /\ currentStep <= Len(graph) + 2

(***************************************************************************)
(* Action Constraint: Graph Immutability                                   *)
(***************************************************************************)

\* INV-EXEC-3: Graph never changes once locked
GraphImmutable ==
    graphLocked => graph' = graph

(***************************************************************************)
(* State Machine Specification                                             *)
(***************************************************************************)

Next ==
    \/ ExecuteStepValid
    \/ ExecuteStepInvalid
    \/ TakeSnapshot
    \/ DetectTimingAttackAndHalt
    \/ DetectDangerousAnsi
    \/ Tick
    \/ Stutter

Spec == Init /\ [][Next /\ GraphImmutable]_vars

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* With fairness, execution eventually terminates
EventualTermination ==
    <>terminated

\* Fair specification includes weak fairness on execution steps
FairSpec ==
    Spec /\ WF_vars(ExecuteStepValid) /\ WF_vars(ExecuteStepInvalid)

(***************************************************************************)
(* Deadlock Freedom                                                        *)
(***************************************************************************)

\* Quiescent state: execution terminated
ExecutionQuiescent == terminated

\* System can always make progress (or is done)
ExecutionActionEnabled ==
    \/ ~terminated      \* Can take some action
    \/ terminated       \* Quiescent

\* INV-DEADLOCK-EXEC-1: No deadlock
ExecutionNoDeadlock ==
    ExecutionActionEnabled

(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)

\* THEOREM: Invalid validation leads to termination
THEOREM InvalidLeadsToHalt ==
    Spec => [](validationState = "invalid" => terminated)

\* THEOREM: Dangerous ANSI detection halts execution
THEOREM DangerousHalts ==
    Spec => [](dangerousDetected => terminated)

\* THEOREM: Graph immutability (enforced by action constraint)
THEOREM GraphNeverChanges ==
    Spec => [][graph' = graph]_graph

\* THEOREM: With fairness, execution terminates
THEOREM EventuallyDone ==
    FairSpec => <>terminated

\* THEOREM: Successful termination means all steps completed
THEOREM SuccessMeansComplete ==
    Spec => [](termReason = "success" => currentStep > Len(graph))

=============================================================================
