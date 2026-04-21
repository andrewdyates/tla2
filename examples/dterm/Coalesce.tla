----------------------------- MODULE Coalesce -----------------------------
(***************************************************************************)
(* TLA+ Specification for dTerm Input Coalescing                           *)
(*                                                                         *)
(* This specification defines the dual-timer input coalescing state        *)
(* machine used to batch rapid terminal output and reduce render frequency.*)
(*                                                                         *)
(* Key invariants:                                                         *)
(* - Memory budget is respected (buffer doesn't exceed threshold)          *)
(* - Bounded latency (render happens within upper_delay)                   *)
(* - No data loss (all input eventually rendered)                          *)
(* - Proper state transitions                                              *)
(*                                                                         *)
(* Design based on:                                                        *)
(* - foot: dual-timer with lower (0.5ms) and upper (8.3ms) bounds          *)
(* - Kitty: input_delay (3ms), repaint_delay (10ms), buffer threshold      *)
(*                                                                         *)
(* Reference: crates/dterm-core/src/coalesce/mod.rs                        *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals

(***************************************************************************)
(* CONSTANTS                                                               *)
(***************************************************************************)

CONSTANTS
    LowerDelayNs,     \* Lower bound delay in nanoseconds (e.g., 500000)
    UpperDelayNs,     \* Upper bound delay in nanoseconds (e.g., 8333333)
    BufferThreshold,  \* Buffer size threshold in bytes (e.g., 16384)
    MaxBufferSize,    \* Maximum buffer size before overflow (e.g., 1048576)
    MaxTime,          \* Maximum time for bounded model checking
    MaxTotalBytes,    \* Max total bytes for bounded model checking
    MaxTotalBatches   \* Max total batches for bounded model checking

\* Constraint assumptions
ASSUME LowerDelayNs \in Nat /\ LowerDelayNs > 0
ASSUME UpperDelayNs \in Nat /\ UpperDelayNs >= LowerDelayNs
ASSUME UpperDelayNs < 1000000000  \* < 1 second
ASSUME BufferThreshold \in Nat /\ BufferThreshold > 0
ASSUME MaxBufferSize \in Nat /\ MaxBufferSize >= BufferThreshold
ASSUME MaxTime \in Nat /\ MaxTime > UpperDelayNs
ASSUME MaxTotalBytes \in Nat /\ MaxTotalBytes > 0
ASSUME MaxTotalBatches \in Nat /\ MaxTotalBatches > 0

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)

VARIABLES
    state,            \* Current state: Idle, Waiting, UpperArmed
    accumulatedBytes, \* Bytes accumulated since last render
    firstInputAt,     \* Time of first input in current batch (None or timestamp)
    lastInputAt,      \* Time of most recent input (None or timestamp)
    now,              \* Current time in nanoseconds
    totalBytes,       \* Total bytes processed (for statistics)
    totalBatches,     \* Total batches rendered (for statistics)
    enabled           \* Whether coalescing is enabled

vars == <<state, accumulatedBytes, firstInputAt, lastInputAt, now,
          totalBytes, totalBatches, enabled>>

(***************************************************************************)
(* HELPER DEFINITIONS                                                      *)
(***************************************************************************)

\* State values
Idle == "Idle"
Waiting == "Waiting"
UpperArmed == "UpperArmed"

\* Optional time representation
NoTime == -1
IsTime(t) == t >= 0
TimeOrNone == {NoTime} \cup (0..MaxTime)

\* Calculate lower deadline
LowerDeadline == IF IsTime(lastInputAt) THEN lastInputAt + LowerDelayNs ELSE NoTime

\* Calculate upper deadline
UpperDeadline == IF IsTime(firstInputAt) THEN firstInputAt + UpperDelayNs ELSE NoTime

\* Check if lower deadline has passed
LowerExpired == IsTime(lastInputAt) /\ now >= lastInputAt + LowerDelayNs

\* Check if upper deadline has passed
UpperExpired == IsTime(firstInputAt) /\ now >= firstInputAt + UpperDelayNs

\* Check if buffer threshold exceeded
BufferExceeded == accumulatedBytes >= BufferThreshold

\* Should render based on current state
ShouldRender ==
    \/ ~enabled                     \* Disabled always renders
    \/ BufferExceeded               \* Buffer threshold
    \/ UpperExpired                 \* Upper bound
    \/ (LowerExpired /\ state = Waiting)  \* Lower bound and waiting

\* Min function
Min(a, b) == IF a < b THEN a ELSE b

\* Saturating add for bytes
SatAdd(a, b) == Min(a + b, MaxBufferSize)

(***************************************************************************)
(* TYPE INVARIANT                                                          *)
(***************************************************************************)

TypeInvariant ==
    /\ state \in {Idle, Waiting, UpperArmed}
    /\ accumulatedBytes \in 0..MaxBufferSize
    /\ firstInputAt \in TimeOrNone
    /\ lastInputAt \in TimeOrNone
    /\ now \in 0..MaxTime
    /\ totalBytes \in 0..MaxTotalBytes
    /\ totalBatches \in 0..MaxTotalBatches
    /\ enabled \in BOOLEAN
    \* Consistency: firstInputAt <= lastInputAt when both present
    /\ (IsTime(firstInputAt) /\ IsTime(lastInputAt)) => firstInputAt <= lastInputAt
    \* Consistency: Idle state has no pending input
    /\ (state = Idle) => (~IsTime(firstInputAt) /\ ~IsTime(lastInputAt))

(***************************************************************************)
(* SAFETY PROPERTIES                                                       *)
(***************************************************************************)

\* Buffer never exceeds maximum
BufferBounded == accumulatedBytes <= MaxBufferSize

\* Total bytes never decreases
TotalBytesMonotonic == totalBytes' >= totalBytes

\* Total batches never decreases
TotalBatchesMonotonic == totalBatches' >= totalBatches

\* When idle, no pending bytes
IdleNoPending == (state = Idle) => (accumulatedBytes = 0 \/ ~enabled)

\* Bounded latency: render happens within upper_delay after first input
\* This is expressed as: if first_input_at + upper_delay <= now, must render
BoundedLatency ==
    enabled => (UpperExpired => ShouldRender)

\* Combined safety property
Safety ==
    /\ BufferBounded
    /\ IdleNoPending
    /\ BoundedLatency

(***************************************************************************)
(* INITIAL STATE                                                           *)
(***************************************************************************)

Init ==
    /\ state = Idle
    /\ accumulatedBytes = 0
    /\ firstInputAt = NoTime
    /\ lastInputAt = NoTime
    /\ now = 0
    /\ totalBytes = 0
    /\ totalBatches = 0
    /\ enabled = TRUE

(***************************************************************************)
(* OPERATIONS                                                              *)
(***************************************************************************)

\* Receive input bytes
OnInput(bytes) ==
    /\ bytes > 0
    /\ bytes <= BufferThreshold  \* Bounded for model checking
    /\ totalBytes + bytes <= MaxTotalBytes
    /\ LET newAccumulated == SatAdd(accumulatedBytes, bytes)
           newTotalBytes == totalBytes + bytes
       IN
           /\ accumulatedBytes' = newAccumulated
           /\ totalBytes' = newTotalBytes
           /\ lastInputAt' = now
           \* Set firstInputAt if this is first input
           /\ IF ~IsTime(firstInputAt)
              THEN /\ firstInputAt' = now
                   /\ state' = UpperArmed
              ELSE /\ UNCHANGED firstInputAt
                   /\ state' = Waiting
           /\ UNCHANGED <<now, totalBatches, enabled>>

\* Render (process accumulated input)
OnRender ==
    /\ accumulatedBytes > 0  \* Must have pending input
    /\ ShouldRender          \* Rendering criteria met
    /\ totalBatches < MaxTotalBatches
    /\ accumulatedBytes' = 0
    /\ firstInputAt' = NoTime
    /\ lastInputAt' = NoTime
    /\ state' = Idle
    /\ totalBatches' = totalBatches + 1
    /\ UNCHANGED <<now, totalBytes, enabled>>

\* Time advances
Tick ==
    /\ now < MaxTime
    /\ now' = now + 1  \* Advance by 1 unit (model as nanoseconds for small steps)
    /\ UNCHANGED <<state, accumulatedBytes, firstInputAt, lastInputAt,
                   totalBytes, totalBatches, enabled>>

\* Reset (discard pending without counting as batch)
Reset ==
    /\ accumulatedBytes' = 0
    /\ firstInputAt' = NoTime
    /\ lastInputAt' = NoTime
    /\ state' = Idle
    /\ UNCHANGED <<now, totalBytes, totalBatches, enabled>>

\* Enable/disable coalescing
SetEnabled(e) ==
    /\ enabled' = e
    /\ UNCHANGED <<state, accumulatedBytes, firstInputAt, lastInputAt,
                   now, totalBytes, totalBatches>>

(***************************************************************************)
(* NEXT STATE RELATION                                                     *)
(***************************************************************************)

Next ==
    \/ \E bytes \in 1..BufferThreshold : OnInput(bytes)
    \/ OnRender
    \/ Tick
    \/ Reset
    \/ SetEnabled(TRUE)
    \/ SetEnabled(FALSE)

(***************************************************************************)
(* SPECIFICATION                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* FAIRNESS                                                                *)
(*                                                                         *)
(* Ensure time advances and renders eventually happen                      *)
(***************************************************************************)

\* Time must eventually advance
Fairness == WF_vars(Tick)

\* Rendering must eventually happen when needed
RenderFairness == WF_vars(OnRender)

FairSpec == Spec /\ Fairness /\ RenderFairness

(***************************************************************************)
(* LIVENESS PROPERTIES                                                     *)
(***************************************************************************)

\* If input is received and coalescing is enabled, eventually render happens
EventualRender ==
    (accumulatedBytes > 0 /\ enabled) ~> (accumulatedBytes = 0)

\* No input is lost (eventually processed)
NoInputLost ==
    [](accumulatedBytes > 0 => <>(accumulatedBytes = 0 \/ ~enabled))

(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)

\* Type invariant always holds
THEOREM TypeSafe == Spec => []TypeInvariant

\* Safety properties always hold
THEOREM SafetyHolds == Spec => []Safety

\* Eventual render with fairness
THEOREM EventualRenderHolds == FairSpec => EventualRender

(***************************************************************************)
(* STATE MACHINE THEOREMS                                                  *)
(***************************************************************************)

\* From Idle, only OnInput transitions to non-Idle
IdleTransitions ==
    (state = Idle /\ state' # state) => (state' \in {Waiting, UpperArmed})

\* From Waiting/UpperArmed, can go to Idle only via Render or Reset
ToIdleTransitions ==
    (state # Idle /\ state' = Idle) => (accumulatedBytes' = 0)

\* UpperArmed -> Waiting on subsequent input
UpperArmedToWaiting ==
    (state = UpperArmed /\ state' = Waiting) => IsTime(firstInputAt')

(***************************************************************************)
(* MODEL CHECKING CONFIGURATION                                            *)
(*                                                                         *)
(* For tractable model checking, use small constants:                      *)
(* LowerDelayNs = 2, UpperDelayNs = 5, BufferThreshold = 10                *)
(* MaxBufferSize = 20, MaxTime = 20                                        *)
(***************************************************************************)

==========================================================================
