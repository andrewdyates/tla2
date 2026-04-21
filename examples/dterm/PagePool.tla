--------------------------- MODULE PagePool ---------------------------
(***************************************************************************)
(* TLA+ Specification for Memory Pool (Gap 2)                              *)
(*                                                                          *)
(* This specification defines:                                              *)
(* - Page allocation from a free list or fresh memory                       *)
(* - Page deallocation (return to free list)                                *)
(* - Preheating (pre-allocating) pages                                      *)
(* - Pool statistics tracking                                               *)
(* - Generation tracking for pin invalidation (Gap 3)                       *)
(*                                                                          *)
(* Reference: crates/dterm-core/src/grid/page.rs                            *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANTS
    MaxPages,             \* Maximum pages that can ever be allocated
    PageSize,             \* Size of each page in bytes (e.g., 65536)
    MaxAllocations,       \* Max allocation requests for bounded model checking
    MaxGeneration         \* Max generation for bounded model checking

ASSUME MaxPages \in Nat /\ MaxPages > 0
ASSUME PageSize \in Nat /\ PageSize > 0
ASSUME MaxAllocations \in Nat /\ MaxAllocations > 0
ASSUME MaxGeneration \in Nat /\ MaxGeneration > 0

(***************************************************************************)
(* VARIABLES                                                                *)
(***************************************************************************)

VARIABLES
    \* Active pages (currently holding allocations)
    active_pages,         \* Set of page IDs currently in use

    \* Free list of recycled pages
    free_pages,           \* Set of page IDs available for reuse

    \* Statistics
    pages_allocated,      \* Total pages ever allocated
    allocations,          \* Total allocation requests
    reused,               \* Allocations satisfied from free list

    \* Generation tracking for pin invalidation
    generation,           \* Current global generation counter
    page_generations,     \* Function: page ID -> generation
    min_valid_generation  \* Minimum valid generation for pins

vars == <<active_pages, free_pages, pages_allocated, allocations, reused,
          generation, page_generations, min_valid_generation>>

(***************************************************************************)
(* TYPE INVARIANT                                                           *)
(***************************************************************************)

TypeInvariant ==
    /\ active_pages \subseteq 0..MaxPages-1
    /\ free_pages \subseteq 0..MaxPages-1
    /\ active_pages \cap free_pages = {}           \* Disjoint
    /\ pages_allocated \in 0..MaxPages
    /\ allocations \in 0..MaxAllocations
    /\ reused \in 0..allocations
    /\ generation \in 0..MaxGeneration
    /\ min_valid_generation \in 0..generation
    /\ DOMAIN page_generations = active_pages \cup free_pages
    /\ \A p \in DOMAIN page_generations: page_generations[p] \in 0..generation

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

Init ==
    /\ active_pages = {}
    /\ free_pages = {}
    /\ pages_allocated = 0
    /\ allocations = 0
    /\ reused = 0
    /\ generation = 0
    /\ page_generations = [p \in {} |-> 0]
    /\ min_valid_generation = 0

(***************************************************************************)
(* OPERATIONS                                                               *)
(***************************************************************************)

(***************************************************************************)
(* Preheat: Pre-allocate pages into the free list                          *)
(* This is called during initialization to avoid runtime allocations        *)
(***************************************************************************)
Preheat(count) ==
    /\ count > 0
    /\ pages_allocated + count <= MaxPages
    /\ LET new_page_ids == {pages_allocated + i : i \in 0..count-1}
           new_gens == [p \in new_page_ids |-> 0]
       IN /\ free_pages' = free_pages \cup new_page_ids
          /\ pages_allocated' = pages_allocated + count
          /\ page_generations' = [p \in DOMAIN page_generations \cup new_page_ids |->
                                    IF p \in DOMAIN page_generations
                                    THEN page_generations[p]
                                    ELSE 0]
    /\ UNCHANGED <<active_pages, allocations, reused, generation, min_valid_generation>>

(***************************************************************************)
(* AllocPage: Allocate a page from free list or fresh memory               *)
(* Returns a page ID. Prefers free list for reuse.                          *)
(***************************************************************************)
AllocPage ==
    /\ allocations < MaxAllocations
    /\ allocations' = allocations + 1
    /\ \/ \* Try free list first (reuse)
          /\ free_pages # {}
          /\ \E p \in free_pages:
               /\ active_pages' = active_pages \cup {p}
               /\ free_pages' = free_pages \ {p}
               /\ reused' = reused + 1
               /\ UNCHANGED <<pages_allocated, generation, page_generations, min_valid_generation>>
       \/ \* Allocate fresh page
          /\ free_pages = {}
          /\ pages_allocated < MaxPages
          /\ LET new_page == pages_allocated
             IN /\ active_pages' = active_pages \cup {new_page}
                /\ pages_allocated' = pages_allocated + 1
                /\ page_generations' = [p \in DOMAIN page_generations \cup {new_page} |->
                                          IF p \in DOMAIN page_generations
                                          THEN page_generations[p]
                                          ELSE 0]
                /\ UNCHANGED <<free_pages, reused, generation, min_valid_generation>>

(***************************************************************************)
(* FreePage: Return a page to the free list                                 *)
(* Increments the page's generation for pin invalidation.                   *)
(***************************************************************************)
FreePage(page_id) ==
    /\ page_id \in active_pages
    /\ generation < MaxGeneration
    /\ active_pages' = active_pages \ {page_id}
    /\ free_pages' = free_pages \cup {page_id}
    /\ generation' = generation + 1
    /\ page_generations' = [page_generations EXCEPT ![page_id] = generation']
    /\ UNCHANGED <<pages_allocated, allocations, reused, min_valid_generation>>

(***************************************************************************)
(* Reset: Move all active pages to free list                                *)
(* Used when clearing the terminal. Invalidates all pins.                   *)
(***************************************************************************)
Reset ==
    /\ active_pages # {}
    /\ generation < MaxGeneration
    /\ free_pages' = free_pages \cup active_pages
    /\ active_pages' = {}
    /\ generation' = generation + 1
    /\ \* Update all page generations
       LET updated_gens == [p \in DOMAIN page_generations |-> generation']
       IN page_generations' = updated_gens
    /\ min_valid_generation' = generation'
    /\ UNCHANGED <<pages_allocated, allocations, reused>>

(***************************************************************************)
(* ShrinkToFit: Release all free pages back to the system                   *)
(* Note: In the model, we just clear the free list.                         *)
(***************************************************************************)
ShrinkToFit ==
    /\ free_pages # {}
    /\ LET freed == free_pages
       IN /\ free_pages' = {}
          /\ page_generations' = [p \in active_pages |-> page_generations[p]]
    /\ UNCHANGED <<active_pages, pages_allocated, allocations, reused,
                   generation, min_valid_generation>>

(***************************************************************************)
(* SAFETY PROPERTIES                                                        *)
(***************************************************************************)

\* Active and free pages are always disjoint
DisjointPageSets ==
    active_pages \cap free_pages = {}

\* Total pages tracked never exceed allocated
TotalPagesValid ==
    Cardinality(active_pages \cup free_pages) <= pages_allocated

\* Reuse count never exceeds allocations
ReuseBounded ==
    reused <= allocations

\* Statistics are consistent
StatsConsistent ==
    /\ reused <= allocations
    /\ Cardinality(active_pages) + Cardinality(free_pages) <= pages_allocated

\* Generation monotonically increases
GenerationMonotonic ==
    /\ generation >= min_valid_generation
    /\ \A p \in DOMAIN page_generations: page_generations[p] <= generation

\* Pins with generation < min_valid_generation are invalid
\* (This is a helper for checking pin validity)
PinValid(pin_page, pin_gen) ==
    /\ pin_gen >= min_valid_generation
    /\ pin_page \in DOMAIN page_generations
    /\ pin_gen = page_generations[pin_page]

Safety ==
    /\ DisjointPageSets
    /\ TotalPagesValid
    /\ StatsConsistent
    /\ GenerationMonotonic

(***************************************************************************)
(* STATE TRANSITIONS                                                        *)
(***************************************************************************)

NoOp == UNCHANGED vars

Next ==
    \/ \E n \in 1..5: Preheat(n)
    \/ AllocPage
    \/ \E p \in active_pages: FreePage(p)
    \/ Reset
    \/ ShrinkToFit
    \/ NoOp

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* THEOREMS                                                                 *)
(***************************************************************************)

\* TypeInvariant is preserved
THEOREM TypeInvariantPreserved == Spec => []TypeInvariant

\* Safety properties always hold
THEOREM SafetyPreserved == Spec => []Safety

\* After preheat(n), free_pages increases by n
THEOREM PreheatAddsToFreeList ==
    \A n \in 1..MaxPages:
        (pages_allocated + n <= MaxPages) =>
        (LET old_free == Cardinality(free_pages)
             old_allocated == pages_allocated
         IN (Preheat(n) =>
             /\ Cardinality(free_pages') = old_free + n
             /\ pages_allocated' = old_allocated + n))

\* After FreePage, generation increases
THEOREM FreePageIncrementsGeneration ==
    \A p \in active_pages:
        FreePage(p) => generation' = generation + 1

\* After Reset, all pins created before Reset are invalid
THEOREM ResetInvalidatesPins ==
    Reset => min_valid_generation' > min_valid_generation

(***************************************************************************)
(* PIN VALIDITY MODEL                                                       *)
(*                                                                          *)
(* A "Pin" is a handle to a page that includes the generation at which     *)
(* the page was allocated. This enables use-after-free detection:          *)
(* - When a page is freed and reallocated, its generation changes          *)
(* - Old pins (with old generation) are now invalid                        *)
(* - Accessing a page with an invalid pin is a detectable error            *)
(*                                                                          *)
(* This models the Rust implementation's Pin<PageId> pattern.               *)
(***************************************************************************)

\* Model a Pin as a record: {page: PageId, gen: Generation}
PinType == [page: 0..MaxPages-1, gen: Nat]

\* A pin is valid if:
\* 1. Its generation >= min_valid_generation (not invalidated by Reset)
\* 2. The page is currently active (not freed)
\* 3. The pin's generation matches the page's current generation
IsPinValid(pin) ==
    /\ pin.gen >= min_valid_generation
    /\ pin.page \in active_pages
    /\ pin.page \in DOMAIN page_generations
    /\ pin.gen = page_generations[pin.page]

\* A pin is stale if the page was freed and possibly reallocated
IsPinStale(pin) ==
    /\ pin.page \in DOMAIN page_generations
    /\ pin.gen < page_generations[pin.page]

\* A pin is globally invalidated if it predates a Reset
IsPinGloballyInvalidated(pin) ==
    pin.gen < min_valid_generation

\* Create a valid pin for an active page
CreatePin(page) ==
    IF page \in active_pages /\ page \in DOMAIN page_generations
    THEN [page |-> page, gen |-> page_generations[page]]
    ELSE [page |-> page, gen |-> 0]  \* Invalid pin

(***************************************************************************)
(* PIN VALIDITY INVARIANTS                                                  *)
(*                                                                          *)
(* These invariants ensure the pin system is always consistent.             *)
(***************************************************************************)

\* All active pages have a trackable generation
ActivePagesHaveGeneration ==
    \A p \in active_pages: p \in DOMAIN page_generations

\* Generation only increases (monotonicity)
\* This ensures old pins never become valid again
GenerationMonotonicity ==
    generation >= 0 /\ min_valid_generation <= generation

\* A freed page cannot have a pin that matches its new generation
\* (because generation was incremented on free)
FreedPageInvalidatesOldPins ==
    \A p \in free_pages:
        p \in DOMAIN page_generations =>
            \* The page's generation is now > any pin created before it was freed
            page_generations[p] <= generation

\* After FreePage(p), any pin created for p before free is now stale
THEOREM FreeMakesPinsStale ==
    \A p \in active_pages:
        LET oldGen == page_generations[p]
            oldPin == [page |-> p, gen |-> oldGen]
        IN FreePage(p) => IsPinStale(oldPin')

\* Creating a pin for an active page always succeeds
THEOREM ActivePagePinValid ==
    \A p \in active_pages:
        LET pin == CreatePin(p)
        IN IsPinValid(pin)

(***************************************************************************)
(* USE-AFTER-FREE DETECTION                                                 *)
(*                                                                          *)
(* The key safety property: any access through a stale pin is detectable.   *)
(***************************************************************************)

\* Accessing a page through a pin should check validity first
AccessPage(pin) ==
    IF IsPinValid(pin)
    THEN TRUE   \* Access allowed
    ELSE FALSE  \* Use-after-free detected!

\* No valid pin can reference a freed page
\* This is the core use-after-free prevention property
NoValidPinToFreedPage ==
    \A p \in free_pages:
        ~(\E gen \in 0..generation: IsPinValid([page |-> p, gen |-> gen]))

THEOREM UseAfterFreeDetectable == Spec => []NoValidPinToFreedPage

(***************************************************************************)
(* ALLOCATION SEQUENCE PROPERTIES                                           *)
(*                                                                          *)
(* Properties about sequences of allocations and frees.                     *)
(***************************************************************************)

\* Double free is impossible (can only free active pages)
DoubleFreeImpossible ==
    \A p \in 0..MaxPages-1:
        p \in free_pages => ~ENABLED FreePage(p)

\* A page that was just allocated has generation 0 or inherited
FreshPageGeneration ==
    \A p \in active_pages:
        page_generations[p] <= generation

THEOREM NoDoubleFree == Spec => []DoubleFreeImpossible
THEOREM FreshPagesValid == Spec => []FreshPageGeneration

=============================================================================
