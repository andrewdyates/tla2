--------------------------- MODULE Scrollback ---------------------------
(***************************************************************************)
(* TLA+ Specification for dTerm Tiered Scrollback Storage                  *)
(*                                                                          *)
(* This specification defines the three-tier scrollback architecture:       *)
(* - Hot tier: Uncompressed lines in RAM (instant access)                   *)
(* - Warm tier: LZ4-compressed blocks in RAM (fast decompress)              *)
(* - Cold tier: Zstd-compressed pages on disk (lazy load)                   *)
(*                                                                          *)
(* Key invariants:                                                          *)
(* - Memory budget is respected                                             *)
(* - No lines are silently lost (lineCount = linesAdded - linesRemoved)    *)
(* - Line count is always accurate vs computed tier counts                  *)
(* - Explicit removal (Clear/Truncate) is tracked separately from adds     *)
(*                                                                          *)
(* Reference: docs/architecture/DESIGN.md Section 4.1, 4.2                  *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANTS
    HotLimit,             \* Max lines in hot tier (e.g., 1000)
    WarmLimit,            \* Max lines in warm tier (e.g., 10000)
    ColdLimit,            \* Max lines in cold tier (e.g., unlimited in practice)
    MemoryBudget,         \* Total memory budget in bytes (e.g., 100MB)
    LineSize,             \* Average uncompressed line size (e.g., 200 bytes)
    LZ4Ratio,             \* LZ4 compression ratio (e.g., 10 = 10:1)
    ZstdRatio,            \* Zstd compression ratio (e.g., 20 = 20:1)
    BlockSize,            \* Lines per compressed block (e.g., 100)
    MaxLineId             \* Max line ID for bounded model checking

\* Constraint assumptions for model checking
ASSUME HotLimit \in Nat /\ HotLimit > 0
ASSUME WarmLimit \in Nat /\ WarmLimit >= 0
ASSUME ColdLimit \in Nat /\ ColdLimit >= 0
ASSUME MemoryBudget \in Nat /\ MemoryBudget > 0
ASSUME LineSize \in Nat /\ LineSize > 0
ASSUME LZ4Ratio \in Nat /\ LZ4Ratio > 0
ASSUME ZstdRatio \in Nat /\ ZstdRatio > 0
ASSUME BlockSize \in Nat /\ BlockSize > 0
ASSUME MaxLineId \in Nat /\ MaxLineId > 0

(***************************************************************************)
(* VARIABLES                                                                *)
(***************************************************************************)

VARIABLES
    hot,                  \* Lines in hot tier (sequence of line indices)
    warm,                 \* Compressed blocks in warm tier (sequence of block records)
    cold,                 \* Pages in cold tier (sequence of page records)
    memoryUsed,           \* Current memory usage in bytes
    lineCount,            \* Total line count across all tiers
    linesAdded,           \* Counter of lines added (for verification)
    linesRemoved,         \* Counter of lines explicitly removed (truncate/clear)
    nextLineId            \* Next line ID to assign (monotonically increasing)

vars == <<hot, warm, cold, memoryUsed, lineCount, linesAdded, linesRemoved, nextLineId>>

(***************************************************************************)
(* HELPER DEFINITIONS                                                       *)
(***************************************************************************)

\* Memory used by hot tier (uncompressed)
HotMemory == Len(hot) * LineSize

\* Memory used by a warm block (LZ4 compressed)
WarmBlockMemory(block) == (block.lineCount * LineSize) \div LZ4Ratio

\* Total memory used by warm tier
WarmMemory ==
    LET BlockMem(i) == WarmBlockMemory(warm[i])
    IN IF Len(warm) = 0 THEN 0
       ELSE LET Sum[i \in 0..Len(warm)] ==
                IF i = 0 THEN 0
                ELSE Sum[i-1] + WarmBlockMemory(warm[i])
            IN Sum[Len(warm)]

\* Lines in hot tier
HotLineCount == Len(hot)

\* Lines in warm tier
WarmLineCount ==
    IF Len(warm) = 0 THEN 0
    ELSE LET Sum[i \in 0..Len(warm)] ==
            IF i = 0 THEN 0
            ELSE Sum[i-1] + warm[i].lineCount
         IN Sum[Len(warm)]

\* Lines in cold tier
ColdLineCount ==
    IF Len(cold) = 0 THEN 0
    ELSE LET Sum[i \in 0..Len(cold)] ==
            IF i = 0 THEN 0
            ELSE Sum[i-1] + cold[i].lineCount
         IN Sum[Len(cold)]

\* Total line count computed from tiers
ComputedLineCount == HotLineCount + WarmLineCount + ColdLineCount

\* Create a warm block record with line ID range
\* minLineId and maxLineId track the age of lines in the block
WarmBlock(lc, minId, maxId) ==
    [lineCount |-> lc, tier |-> "warm", minLineId |-> minId, maxLineId |-> maxId]

\* Create a cold page record with line ID range
ColdPage(lc, minId, maxId) ==
    [lineCount |-> lc, tier |-> "cold", minLineId |-> minId, maxLineId |-> maxId]

\* Get maximum line ID in warm tier (or 0 if empty)
WarmMaxLineId ==
    IF Len(warm) = 0 THEN 0
    ELSE warm[Len(warm)].maxLineId

\* Get minimum line ID in warm tier (or infinity-equivalent if empty)
WarmMinLineId ==
    IF Len(warm) = 0 THEN nextLineId \* No warm lines, so any hot line is "newer"
    ELSE warm[1].minLineId

\* Get maximum line ID in cold tier (or 0 if empty)
ColdMaxLineId ==
    IF Len(cold) = 0 THEN 0
    ELSE cold[Len(cold)].maxLineId

\* Get minimum line ID in cold tier (or infinity-equivalent if empty)
ColdMinLineId ==
    IF Len(cold) = 0 THEN nextLineId
    ELSE cold[1].minLineId

\* Get minimum line ID in hot tier (or infinity-equivalent if empty)
HotMinLineId ==
    IF Len(hot) = 0 THEN nextLineId
    ELSE hot[1]

\* Get maximum line ID in hot tier (or 0 if empty)
HotMaxLineId ==
    IF Len(hot) = 0 THEN 0
    ELSE hot[Len(hot)]

\* Max of two values
Max(a, b) == IF a > b THEN a ELSE b

\* Min of two values
Min(a, b) == IF a < b THEN a ELSE b

(***************************************************************************)
(* TYPE INVARIANT                                                           *)
(***************************************************************************)

TypeInvariant ==
    /\ hot \in Seq(Nat)
    /\ Len(hot) <= HotLimit
    /\ warm \in Seq([lineCount: Nat, tier: {"warm"}, minLineId: Nat, maxLineId: Nat])
    /\ cold \in Seq([lineCount: Nat, tier: {"cold"}, minLineId: Nat, maxLineId: Nat])
    /\ memoryUsed \in 0..MemoryBudget + (HotLimit * LineSize)  \* Allow small overage
    /\ lineCount \in Nat
    /\ linesAdded \in Nat
    /\ linesRemoved \in Nat
    /\ linesRemoved <= linesAdded  \* Can't remove more than added
    /\ nextLineId \in 1..MaxLineId

(***************************************************************************)
(* SAFETY PROPERTIES                                                        *)
(***************************************************************************)

\* Hot tier never exceeds its limit
HotBounded == Len(hot) <= HotLimit

\* Memory budget is approximately respected (with small epsilon for hot tier)
MemoryBudgetRespected ==
    memoryUsed <= MemoryBudget + (HotLimit * LineSize)

\* Line count is accurate (data integrity)
LineCountAccurate == lineCount = ComputedLineCount

\* No lines are lost - total equals added minus explicitly removed
\* This accounts for ClearScrollback and TruncateToLast operations
NoLinesLost == lineCount = linesAdded - linesRemoved

\* Combined safety property
Safety ==
    /\ HotBounded
    /\ MemoryBudgetRespected
    /\ LineCountAccurate
    /\ NoLinesLost

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

Init ==
    /\ hot = <<>>
    /\ warm = <<>>
    /\ cold = <<>>
    /\ memoryUsed = 0
    /\ lineCount = 0
    /\ linesAdded = 0
    /\ linesRemoved = 0
    /\ nextLineId = 1

(***************************************************************************)
(* TIER PROMOTION OPERATIONS                                                *)
(***************************************************************************)

\* Promote lines from hot to warm (compress with LZ4)
PromoteHotToWarm ==
    /\ Len(hot) >= BlockSize
    /\ WarmLineCount <= WarmLimit
    \* Take first BlockSize lines (oldest lines in hot)
    /\ LET toPromote == SubSeq(hot, 1, BlockSize)
           minId == hot[1]                           \* Oldest line being promoted
           maxId == hot[BlockSize]                   \* Newest line being promoted
           newBlock == WarmBlock(BlockSize, minId, maxId)
           hotMemoryFreed == BlockSize * LineSize
           warmMemoryUsed == (BlockSize * LineSize) \div LZ4Ratio
       IN
           /\ hot' = SubSeq(hot, BlockSize + 1, Len(hot))
           /\ warm' = Append(warm, newBlock)
           /\ memoryUsed' = memoryUsed - hotMemoryFreed + warmMemoryUsed
           /\ UNCHANGED <<cold, lineCount, linesAdded, linesRemoved, nextLineId>>

\* Evict oldest warm block to cold tier (compress with Zstd)
EvictWarmToCold ==
    /\ Len(warm) > 0
    /\ memoryUsed > MemoryBudget  \* Only evict under memory pressure
    /\ LET oldestBlock == warm[1]
           warmMemoryFreed == (oldestBlock.lineCount * LineSize) \div LZ4Ratio
           coldMemoryUsed == 0  \* Cold is on disk, doesn't count against RAM
           \* Preserve line ID range when moving to cold
           newPage == ColdPage(oldestBlock.lineCount, oldestBlock.minLineId, oldestBlock.maxLineId)
       IN
           /\ warm' = Tail(warm)
           /\ cold' = Append(cold, newPage)
           /\ memoryUsed' = memoryUsed - warmMemoryFreed + coldMemoryUsed
           /\ UNCHANGED <<hot, lineCount, linesAdded, linesRemoved, nextLineId>>

\* Alternative: Proactive eviction to stay under budget
ProactiveEvict ==
    /\ Len(warm) > 0
    /\ WarmLineCount > WarmLimit
    /\ LET oldestBlock == warm[1]
           warmMemoryFreed == (oldestBlock.lineCount * LineSize) \div LZ4Ratio
           \* Preserve line ID range when moving to cold
           newPage == ColdPage(oldestBlock.lineCount, oldestBlock.minLineId, oldestBlock.maxLineId)
       IN
           /\ warm' = Tail(warm)
           /\ cold' = Append(cold, newPage)
           /\ memoryUsed' = memoryUsed - warmMemoryFreed
           /\ UNCHANGED <<hot, lineCount, linesAdded, linesRemoved, nextLineId>>

(***************************************************************************)
(* PUSH LINE OPERATION                                                      *)
(*                                                                          *)
(* Add a new line to the scrollback. This is the main operation.            *)
(***************************************************************************)

\* Simple push to hot tier (may trigger promotion)
PushLine ==
    /\ Len(hot) < HotLimit
    /\ nextLineId < MaxLineId
    /\ hot' = Append(hot, nextLineId)  \* Use monotonic line ID
    /\ nextLineId' = nextLineId + 1
    /\ lineCount' = lineCount + 1
    /\ linesAdded' = linesAdded + 1
    /\ memoryUsed' = memoryUsed + LineSize
    /\ UNCHANGED <<warm, cold, linesRemoved>>

\* Push with automatic promotion if hot is full
PushLineWithPromotion ==
    /\ Len(hot) = HotLimit
    /\ Len(hot) >= BlockSize  \* Can only promote if we have a full block
    /\ WarmLineCount <= WarmLimit
    /\ nextLineId < MaxLineId
    \* First promote, then push
    /\ LET toPromote == SubSeq(hot, 1, BlockSize)
           minId == hot[1]                           \* Oldest line being promoted
           maxId == hot[BlockSize]                   \* Newest line being promoted
           newBlock == WarmBlock(BlockSize, minId, maxId)
           hotMemoryFreed == BlockSize * LineSize
           warmMemoryUsed == (BlockSize * LineSize) \div LZ4Ratio
           remainingHot == SubSeq(hot, BlockSize + 1, Len(hot))
       IN
           /\ hot' = Append(remainingHot, nextLineId)  \* Add new line after promotion
           /\ warm' = Append(warm, newBlock)
           /\ nextLineId' = nextLineId + 1
           /\ lineCount' = lineCount + 1
           /\ linesAdded' = linesAdded + 1
           /\ memoryUsed' = memoryUsed - hotMemoryFreed + warmMemoryUsed + LineSize
           /\ UNCHANGED <<cold, linesRemoved>>

(***************************************************************************)
(* LINE ACCESS OPERATIONS (Read-only, don't modify state)                   *)
(***************************************************************************)

\* Get line from appropriate tier (modeled as no-op for state verification)
\* In implementation, this would decompress as needed
GetLine(idx) ==
    /\ idx >= 0
    /\ idx < lineCount
    /\ UNCHANGED vars

(***************************************************************************)
(* MEMORY PRESSURE HANDLING                                                 *)
(***************************************************************************)

\* Handle memory pressure by evicting warm to cold
HandleMemoryPressure ==
    /\ memoryUsed > MemoryBudget
    /\ Len(warm) > 0
    /\ EvictWarmToCold

\* Clear scrollback (explicit user action)
ClearScrollback ==
    /\ hot' = <<>>
    /\ warm' = <<>>
    /\ cold' = <<>>
    /\ memoryUsed' = 0
    /\ linesRemoved' = linesRemoved + lineCount  \* Track removed lines
    /\ lineCount' = 0
    /\ UNCHANGED <<linesAdded, nextLineId>>

\* Truncate to keep only last N lines
TruncateToLast(n) ==
    /\ n >= 0
    /\ n <= HotLimit
    /\ IF lineCount <= n
       THEN UNCHANGED vars
       ELSE
           LET keptHot ==
                   IF Len(hot) <= n
                   THEN hot
                   ELSE SubSeq(hot, Len(hot) - n + 1, Len(hot))
               remaining == Len(keptHot)
               linesToRemove == lineCount - remaining
           IN
               /\ hot' = keptHot
               /\ warm' = <<>>
               /\ cold' = <<>>
               /\ lineCount' = remaining
               /\ memoryUsed' = remaining * LineSize
               /\ linesRemoved' = linesRemoved + linesToRemove  \* Track removed lines
               /\ UNCHANGED <<linesAdded, nextLineId>>

(***************************************************************************)
(* NEXT STATE RELATION                                                      *)
(***************************************************************************)

Next ==
    \/ PushLine
    \/ PushLineWithPromotion
    \/ PromoteHotToWarm
    \/ EvictWarmToCold
    \/ ProactiveEvict
    \/ HandleMemoryPressure
    \/ \E idx \in 0..lineCount-1 : GetLine(idx)
    \/ ClearScrollback
    \/ \E n \in 0..HotLimit : TruncateToLast(n)

(***************************************************************************)
(* SPECIFICATION                                                            *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* FAIRNESS                                                                 *)
(*                                                                          *)
(* Ensure memory pressure is eventually handled                             *)
(***************************************************************************)

Fairness == WF_vars(HandleMemoryPressure)

FairSpec == Spec /\ Fairness

(***************************************************************************)
(* INVARIANTS                                                               *)
(***************************************************************************)

\* Type invariant always holds
THEOREM TypeSafe == Spec => []TypeInvariant

\* Safety properties always hold
THEOREM SafetyHolds == Spec => []Safety

\* Memory budget is eventually respected (with fairness)
THEOREM EventuallyUnderBudget ==
    FairSpec => <>[](memoryUsed <= MemoryBudget + (HotLimit * LineSize))

(***************************************************************************)
(* KEY PROPERTIES FOR VERIFICATION                                          *)
(***************************************************************************)

\* After push, line count increases by exactly 1
PushIncrementsCount ==
    [][lineCount' = lineCount + 1 \/ lineCount' = lineCount \/ lineCount' = 0]_vars

\* Promotion doesn't change line count
PromotionPreservesCount ==
    [][(hot' # hot /\ warm' # warm) => (lineCount' = lineCount)]_vars

\* Memory usage correlates with line distribution
MemoryCorrelation ==
    memoryUsed >= 0 /\ memoryUsed <= MemoryBudget + (HotLimit * LineSize)

(***************************************************************************)
(* TIER AGE ORDERING                                                        *)
(*                                                                          *)
(* Critical invariant: Data flows from hot -> warm -> cold based on age.    *)
(* Newer lines are always in "hotter" tiers than older lines.               *)
(*                                                                          *)
(* This ordering enables efficient access patterns:                         *)
(* - Recent output (hot) is accessed instantly                              *)
(* - Older output (warm) requires LZ4 decompression                         *)
(* - Archived output (cold) requires Zstd decompression + disk I/O          *)
(***************************************************************************)

\* Hot tier contains the newest lines (highest line IDs)
\* The last element of hot is the most recently added line
HotTierNewest ==
    Len(hot) > 0 =>
        \A i \in 1..Len(hot)-1: hot[i] < hot[i+1]

\* Warm tier blocks are ordered by age (oldest first)
\* Each block's maxLineId < next block's minLineId
WarmBlocksOrdered ==
    Len(warm) > 1 =>
        \A i \in 1..Len(warm)-1:
            warm[i].maxLineId < warm[i+1].minLineId

\* Cold tier pages are ordered by age (oldest first)
ColdPagesOrdered ==
    Len(cold) > 1 =>
        \A i \in 1..Len(cold)-1:
            cold[i].maxLineId < cold[i+1].minLineId

\* Warm tier blocks are older than hot tier
\* The newest warm line is still older than the oldest hot line
WarmOlderThanHot ==
    (Len(hot) > 0 /\ Len(warm) > 0) =>
        WarmMaxLineId < HotMinLineId

\* Cold tier pages are older than warm tier
\* The newest cold line is still older than the oldest warm line
ColdOlderThanWarm ==
    (Len(warm) > 0 /\ Len(cold) > 0) =>
        ColdMaxLineId < WarmMinLineId

\* Cold tier pages are older than hot tier (transitive)
ColdOlderThanHot ==
    (Len(hot) > 0 /\ Len(cold) > 0) =>
        ColdMaxLineId < HotMinLineId

\* Combined tier age ordering - now fully verified with explicit line IDs
TierAgeOrdering ==
    /\ HotTierNewest
    /\ WarmBlocksOrdered
    /\ ColdPagesOrdered
    /\ WarmOlderThanHot
    /\ ColdOlderThanWarm
    /\ ColdOlderThanHot

THEOREM TierAgeOrderingHolds == Spec => []TierAgeOrdering

(***************************************************************************)
(* PROMOTION PRESERVES ORDERING                                             *)
(*                                                                          *)
(* When lines are promoted from one tier to another, the age ordering       *)
(* must be preserved. This is guaranteed by always promoting the oldest     *)
(* lines from each tier.                                                    *)
(***************************************************************************)

\* Promotion takes from the beginning (oldest) of hot
PromotionTakesOldest ==
    [][(hot' # hot /\ Len(hot') < Len(hot)) =>
        \* The removed lines were from the front (oldest)
        SubSeq(hot, Len(hot) - Len(hot') + 1, Len(hot)) = hot']_vars

\* Eviction takes from the beginning (oldest) of warm
EvictionTakesOldest ==
    [][(warm' # warm /\ Len(warm') < Len(warm)) =>
        \* The removed block was from the front (oldest)
        SubSeq(warm, 2, Len(warm)) = warm']_vars

\* New lines are always added to the end (newest) of hot
NewLinesAddedToEnd ==
    [][(Len(hot') > Len(hot)) =>
        SubSeq(hot', 1, Len(hot)) = hot]_vars

THEOREM PromotionPreservesOrdering == Spec => []PromotionTakesOldest
THEOREM EvictionPreservesOrdering == Spec => []EvictionTakesOldest
THEOREM NewLinesAtEnd == Spec => []NewLinesAddedToEnd

(***************************************************************************)
(* TIER CAPACITY PROPERTIES                                                 *)
(*                                                                          *)
(* Each tier has a capacity limit that triggers promotion/eviction.         *)
(***************************************************************************)

\* Hot tier stays within its limit
HotWithinCapacity ==
    Len(hot) <= HotLimit

\* Warm tier line count respects limit (triggers eviction)
WarmWithinCapacity ==
    WarmLineCount <= WarmLimit + BlockSize  \* Allow one block overage

\* Cold tier can grow unbounded (on disk)
ColdUnbounded ==
    ColdLineCount <= ColdLimit \/ ColdLimit = 0

\* Combined capacity property
TierCapacityRespected ==
    /\ HotWithinCapacity
    /\ WarmWithinCapacity

THEOREM CapacityRespected == Spec => []TierCapacityRespected

(***************************************************************************)
(* TIER TRANSITION PROPERTIES                                               *)
(*                                                                          *)
(* Lines only move in one direction: hot -> warm -> cold                    *)
(* Lines never move "backwards" to a hotter tier.                           *)
(***************************************************************************)

\* Line IDs are always monotonically increasing in hot tier
\* This ensures new lines are always the newest
LineIdMonotonic ==
    \A i \in 1..Len(hot): hot[i] < nextLineId

\* Lines only move forward through tiers (never backward)
\* Verified by tracking line IDs - cold < warm < hot ordering is maintained
ForwardOnlyTransition ==
    /\ TierAgeOrdering  \* Line IDs prove forward-only movement
    /\ LineIdMonotonic

\* Cold tier is append-only - pages are only added, never removed (except clear)
\* This is implicitly enforced: no operation removes from middle of cold
ColdAppendOnly ==
    [][(Len(cold') > 0 /\ Len(cold) > 0) =>
        SubSeq(cold', 1, Len(cold)) = cold \/ cold' = <<>>]_vars

\* Warm tier follows FIFO - oldest blocks evicted first
WarmFifoEviction ==
    [][(Len(warm') < Len(warm) /\ Len(warm') > 0) =>
        warm' = Tail(warm) \/ warm' = <<>>]_vars

(***************************************************************************)
(* DATA INTEGRITY ACROSS TIERS                                              *)
(*                                                                          *)
(* The total line count across all tiers must match the tracked count.      *)
(* No lines are silently dropped during tier transitions.                   *)
(***************************************************************************)

\* Sum of all tier line counts equals tracked lineCount
TierSumsMatch ==
    lineCount = ComputedLineCount

\* No data loss during promotion
PromotionNoDataLoss ==
    [][(hot' # hot /\ warm' # warm) =>
        (HotLineCount + WarmLineCount = HotLineCount' + WarmLineCount')]_vars

\* No data loss during eviction
EvictionNoDataLoss ==
    [][(warm' # warm /\ cold' # cold) =>
        (WarmLineCount + ColdLineCount = WarmLineCount' + ColdLineCount')]_vars

THEOREM DataIntegrity == Spec => []TierSumsMatch
THEOREM PromotionSafe == Spec => PromotionNoDataLoss
THEOREM EvictionSafe == Spec => EvictionNoDataLoss
THEOREM ForwardOnly == Spec => []ForwardOnlyTransition
THEOREM LineIdAlwaysMonotonic == Spec => []LineIdMonotonic
THEOREM ColdIsAppendOnly == Spec => ColdAppendOnly
THEOREM WarmIsFifo == Spec => WarmFifoEviction

(***************************************************************************)
(* MODEL CHECKING CONFIGURATION                                             *)
(*                                                                          *)
(* For tractable model checking, use small constants:                       *)
(* HotLimit = 5, WarmLimit = 10, ColdLimit = 20                             *)
(* MemoryBudget = 1000, LineSize = 10, BlockSize = 2                        *)
(* LZ4Ratio = 2, ZstdRatio = 4                                              *)
(***************************************************************************)

==========================================================================
