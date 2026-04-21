--------------------------- MODULE HandleAccessLock ---------------------------
(***************************************************************************)
(* TLA+ Specification for DTermTerminal handleAccessLock Protocol          *)
(*                                                                         *)
(* Models the locking protocol for the terminal's opaque handle:           *)
(*   - Swift-side lock (handleAccessLock): declared NSRecursiveLock        *)
(*   - Rust-side lock (SyncTerminal::sync): std::sync::RwLock<()>         *)
(*                                                                         *)
(* PARAMETERIZED: SwiftLockRecursive controls whether the Swift lock       *)
(* actually allows same-thread re-entry. This lets us test both:           *)
(*   TRUE  = lock works as documented (NSRecursiveLock)                    *)
(*   FALSE = lock behaves as plain mutex (observed in production profile)  *)
(*                                                                         *)
(* DEADLOCK FOUND IN PRODUCTION (2026-03-31):                              *)
(* Main thread blocks on handleAccessLock re-entry during palette init.    *)
(* Stack: setPaletteColor -> withHandleOrThrow [lock] ->                   *)
(*   checkPaletteChangesLocked -> delegate callback ->                     *)
(*   paletteColor -> withHandleOrThrow [re-lock] -> BLOCKS                *)
(*                                                                         *)
(* Reference files:                                                        *)
(*   DTermTerminal.swift:525               lock declaration                *)
(*   DTermTerminal+Lifecycle.swift:144     withHandleOrThrow               *)
(*   DTermTerminal+Palette.swift:111-128   setPaletteColorResult           *)
(*   DTermTerminal+Palette.swift:190-214   checkPaletteChangesLocked       *)
(*   TerminalSession+Delegate.swift:331    updatePaletteIndex callback     *)
(*   crates/dterm-core/ffi_bridge/terminal/sync.rs  RwLock<()>            *)
(*   crates/dterm-core-ffi/src/osc.rs      palette FFI functions           *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Naturals

(***************************************************************************)
(* CONSTANTS                                                               *)
(***************************************************************************)

CONSTANTS
    MaxPaletteOps,        \* Bound on palette set operations
    MaxProcessCalls,      \* Bound on PTY process() calls
    SwiftLockRecursive    \* TRUE = NSRecursiveLock, FALSE = plain mutex

ASSUME MaxPaletteOps \in Nat /\ MaxPaletteOps > 0
ASSUME MaxProcessCalls \in Nat /\ MaxProcessCalls > 0
ASSUME SwiftLockRecursive \in BOOLEAN

(***************************************************************************)
(* THREADS                                                                 *)
(***************************************************************************)

Threads == {"Main", "IO"}

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)

VARIABLES
    \* --- Swift handleAccessLock ---
    swiftOwner,       \* "None" or thread name
    swiftDepth,       \* Recursive depth (0 = unlocked)

    \* --- Rust RwLock<()> (SyncTerminal::sync) ---
    \* Models: readers = set of threads holding read lock
    \*         writer = "None" or thread holding write lock
    rustReaders,      \* Set of threads holding read lock
    rustWriter,       \* "None" or thread holding write lock

    \* --- Thread program counters ---
    mainPC,
    ioPC,

    \* --- Bounded operation counters ---
    paletteOps,
    processCalls

vars == <<swiftOwner, swiftDepth, rustReaders, rustWriter,
          mainPC, ioPC, paletteOps, processCalls>>

(***************************************************************************)
(* LOCK PREDICATES                                                         *)
(***************************************************************************)

\* Can thread T acquire the Swift lock?
\* If SwiftLockRecursive is FALSE, same-thread re-entry BLOCKS.
CanAcquireSwift(t) ==
    \/ swiftOwner = "None"
    \/ (SwiftLockRecursive /\ swiftOwner = t)

\* Can thread T acquire Rust RwLock for reading?
\* Multiple readers OK, but not while a writer holds it.
CanAcquireRustRead(t) ==
    rustWriter = "None"

\* Can thread T acquire Rust RwLock for writing?
\* No readers and no other writer.
CanAcquireRustWrite(t) ==
    /\ rustWriter = "None"
    /\ rustReaders = {}

(***************************************************************************)
(* INITIAL STATE                                                           *)
(***************************************************************************)

Init ==
    /\ swiftOwner = "None"
    /\ swiftDepth = 0
    /\ rustReaders = {}
    /\ rustWriter = "None"
    /\ mainPC = "idle"
    /\ ioPC = "idle"
    /\ paletteOps = 0
    /\ processCalls = 0

(***************************************************************************)
(* MAIN THREAD — setPaletteColor path                                      *)
(*                                                                         *)
(* Exact sequence from production code:                                    *)
(*                                                                         *)
(* setPaletteColorResult (Palette.swift:111):                              *)
(*   withHandleResult -> withHandleOrThrow:                                *)
(*     handleAccessLock.lock()              [SWIFT LOCK]                   *)
(*     body(handle):                                                       *)
(*       dterm_terminal_set_palette_color_v2  -> terminal_write_ffi:       *)
(*         sync.write()                     [RUST WRITE LOCK]              *)
(*         closure: set_palette_color_components (pure write)              *)
(*         sync.write() released            [RUST WRITE UNLOCK]            *)
(*       checkPaletteChangesLocked:                                        *)
(*         dterm_terminal_get_palette_snapshot -> terminal_read_ffi:       *)
(*           sync.read()                    [RUST READ LOCK]               *)
(*           closure: read 256 colors                                      *)
(*           sync.read() released           [RUST READ UNLOCK]             *)
(*         diffPaletteSnapshot -> changed indices                          *)
(*         for each changed:                                               *)
(*           colorDelegate.terminalColorDidChange(self, index:)            *)
(*             -> TerminalSession.updatePaletteIndex(index)                *)
(*               -> terminal.paletteColor(index:)                          *)
(*                 -> paletteColorResult -> withHandleResult:              *)
(*                   withHandleOrThrow:                                    *)
(*                     handleAccessLock.lock()  [SWIFT RE-LOCK!]           *)
(*                     body(handle):                                        *)
(*                       dterm_terminal_get_palette_color_v2:              *)
(*                         sync.read()      [RUST READ LOCK]              *)
(*                         closure: read 1 color                           *)
(*                         sync.read() released [RUST READ UNLOCK]         *)
(*                     handleAccessLock.unlock() [SWIFT RE-UNLOCK]         *)
(*     handleAccessLock.unlock()            [SWIFT UNLOCK]                 *)
(***************************************************************************)

\* Step 1: Acquire Swift lock
MainAcquireSwift ==
    /\ mainPC = "idle"
    /\ paletteOps < MaxPaletteOps
    /\ CanAcquireSwift("Main")
    /\ mainPC' = "m_has_swift"
    /\ swiftOwner' = "Main"
    /\ swiftDepth' = swiftDepth + 1
    /\ paletteOps' = paletteOps + 1
    /\ UNCHANGED <<rustReaders, rustWriter, ioPC, processCalls>>

\* Step 2: Acquire Rust WRITE lock for set_palette_color
MainAcquireRustWrite ==
    /\ mainPC = "m_has_swift"
    /\ CanAcquireRustWrite("Main")
    /\ mainPC' = "m_has_swift_rustW"
    /\ rustWriter' = "Main"
    /\ UNCHANGED <<swiftOwner, swiftDepth, rustReaders, ioPC,
                   paletteOps, processCalls>>

\* Step 3: Rust set_palette returns, release Rust WRITE lock
MainReleaseRustWrite ==
    /\ mainPC = "m_has_swift_rustW"
    /\ mainPC' = "m_has_swift_preSnapshot"
    /\ rustWriter' = "None"
    /\ UNCHANGED <<swiftOwner, swiftDepth, rustReaders, ioPC,
                   paletteOps, processCalls>>

\* Step 4: Acquire Rust READ lock for get_palette_snapshot
MainAcquireRustReadSnapshot ==
    /\ mainPC = "m_has_swift_preSnapshot"
    /\ CanAcquireRustRead("Main")
    /\ mainPC' = "m_has_swift_rustR_snapshot"
    /\ rustReaders' = rustReaders \union {"Main"}
    /\ UNCHANGED <<swiftOwner, swiftDepth, rustWriter, ioPC,
                   paletteOps, processCalls>>

\* Step 5: Release Rust READ lock after snapshot
MainReleaseRustReadSnapshot ==
    /\ mainPC = "m_has_swift_rustR_snapshot"
    /\ mainPC' = "m_has_swift_preDelegate"
    /\ rustReaders' = rustReaders \ {"Main"}
    /\ UNCHANGED <<swiftOwner, swiftDepth, rustWriter, ioPC,
                   paletteOps, processCalls>>

\* Step 6: Delegate callback — try to re-acquire Swift lock
MainDelegateReacquireSwift ==
    /\ mainPC = "m_has_swift_preDelegate"
    /\ CanAcquireSwift("Main")
    /\ mainPC' = "m_has_swift2"
    /\ swiftDepth' = swiftDepth + 1
    /\ UNCHANGED <<swiftOwner, rustReaders, rustWriter, ioPC,
                   paletteOps, processCalls>>

\* Step 7: Acquire Rust READ lock for get_palette_color
MainDelegateAcquireRustRead ==
    /\ mainPC = "m_has_swift2"
    /\ CanAcquireRustRead("Main")
    /\ mainPC' = "m_has_swift2_rustR"
    /\ rustReaders' = rustReaders \union {"Main"}
    /\ UNCHANGED <<swiftOwner, swiftDepth, rustWriter, ioPC,
                   paletteOps, processCalls>>

\* Step 8: Release Rust READ lock
MainDelegateReleaseRustRead ==
    /\ mainPC = "m_has_swift2_rustR"
    /\ mainPC' = "m_has_swift2_done"
    /\ rustReaders' = rustReaders \ {"Main"}
    /\ UNCHANGED <<swiftOwner, swiftDepth, rustWriter, ioPC,
                   paletteOps, processCalls>>

\* Step 9: Release inner Swift lock (reentrant depth -1)
MainDelegateReleaseSwift ==
    /\ mainPC = "m_has_swift2_done"
    /\ mainPC' = "m_release_outer"
    /\ swiftDepth' = swiftDepth - 1
    /\ UNCHANGED <<swiftOwner, rustReaders, rustWriter, ioPC,
                   paletteOps, processCalls>>

\* Step 10: Release outer Swift lock
MainReleaseSwift ==
    /\ mainPC = "m_release_outer"
    /\ swiftDepth' = swiftDepth - 1
    /\ swiftOwner' = IF swiftDepth - 1 = 0 THEN "None" ELSE swiftOwner
    /\ mainPC' = "idle"
    /\ UNCHANGED <<rustReaders, rustWriter, ioPC, paletteOps, processCalls>>

(***************************************************************************)
(* IO THREAD — PTY process() path                                         *)
(*                                                                         *)
(* PTYSession+IO.swift -> terminal.process(data:) ->                       *)
(*   withHandleOrThrow [Swift lock] ->                                     *)
(*     Rust process() -> terminal_write_ffi [Rust WRITE lock]              *)
(*     (Rust callbacks use DispatchQueue.main.async, NOT sync)             *)
(***************************************************************************)

IOAcquireSwift ==
    /\ ioPC = "idle"
    /\ processCalls < MaxProcessCalls
    /\ CanAcquireSwift("IO")
    /\ ioPC' = "io_has_swift"
    /\ swiftOwner' = "IO"
    /\ swiftDepth' = swiftDepth + 1
    /\ processCalls' = processCalls + 1
    /\ UNCHANGED <<rustReaders, rustWriter, mainPC, paletteOps>>

IOAcquireRustWrite ==
    /\ ioPC = "io_has_swift"
    /\ CanAcquireRustWrite("IO")
    /\ ioPC' = "io_has_swift_rustW"
    /\ rustWriter' = "IO"
    /\ UNCHANGED <<swiftOwner, swiftDepth, rustReaders, mainPC,
                   paletteOps, processCalls>>

IOReleaseRustWrite ==
    /\ ioPC = "io_has_swift_rustW"
    /\ ioPC' = "io_release_swift"
    /\ rustWriter' = "None"
    /\ UNCHANGED <<swiftOwner, swiftDepth, rustReaders, mainPC,
                   paletteOps, processCalls>>

IOReleaseSwift ==
    /\ ioPC = "io_release_swift"
    /\ swiftDepth' = swiftDepth - 1
    /\ swiftOwner' = IF swiftDepth - 1 = 0 THEN "None" ELSE swiftOwner
    /\ ioPC' = "idle"
    /\ UNCHANGED <<rustReaders, rustWriter, mainPC, paletteOps, processCalls>>

(***************************************************************************)
(* NEXT STATE RELATION                                                     *)
(***************************************************************************)

Next ==
    \/ MainAcquireSwift
    \/ MainAcquireRustWrite
    \/ MainReleaseRustWrite
    \/ MainAcquireRustReadSnapshot
    \/ MainReleaseRustReadSnapshot
    \/ MainDelegateReacquireSwift
    \/ MainDelegateAcquireRustRead
    \/ MainDelegateReleaseRustRead
    \/ MainDelegateReleaseSwift
    \/ MainReleaseSwift
    \/ IOAcquireSwift
    \/ IOAcquireRustWrite
    \/ IOReleaseRustWrite
    \/ IOReleaseSwift

Spec == Init /\ [][Next]_vars

Fairness ==
    /\ WF_vars(MainAcquireSwift)
    /\ WF_vars(MainAcquireRustWrite)
    /\ WF_vars(MainReleaseRustWrite)
    /\ WF_vars(MainAcquireRustReadSnapshot)
    /\ WF_vars(MainReleaseRustReadSnapshot)
    /\ WF_vars(MainDelegateReacquireSwift)
    /\ WF_vars(MainDelegateAcquireRustRead)
    /\ WF_vars(MainDelegateReleaseRustRead)
    /\ WF_vars(MainDelegateReleaseSwift)
    /\ WF_vars(MainReleaseSwift)
    /\ WF_vars(IOAcquireSwift)
    /\ WF_vars(IOAcquireRustWrite)
    /\ WF_vars(IOReleaseRustWrite)
    /\ WF_vars(IOReleaseSwift)

FairSpec == Spec /\ Fairness

(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)

\* I1: Swift lock depth consistent with ownership
SwiftLockConsistent ==
    /\ (swiftOwner = "None") <=> (swiftDepth = 0)
    /\ swiftDepth >= 0
    /\ swiftDepth <= 3

\* I2: RwLock mutual exclusion — no readers while writing
RwLockConsistent ==
    /\ (rustWriter /= "None") => (rustReaders = {})
    /\ rustWriter \in {"None"} \cup Threads

\* I3: Lock ordering preserved — Rust lock requires Swift lock
LockOrderPreserved ==
    /\ (rustWriter /= "None") => (swiftOwner = rustWriter)
    /\ \A t \in Threads : (t \in rustReaders) => (swiftOwner = t)

(***************************************************************************)
(* DEADLOCK FREEDOM                                                        *)
(*                                                                         *)
(* NoDeadlock: at least one thread can always make progress, OR all        *)
(* threads have finished their bounded work.                               *)
(*                                                                         *)
(* When SwiftLockRecursive = FALSE, this SHOULD FAIL because:              *)
(*   Main holds Swift at depth 1, tries to re-acquire at step 6.           *)
(*   With non-recursive lock, re-entry blocks.                             *)
(*   If IO is idle, Main is the only thread and it's stuck -> DEADLOCK.    *)
(*                                                                         *)
(* When SwiftLockRecursive = TRUE, this should pass.                       *)
(***************************************************************************)

MainCanProgress ==
    \/ mainPC = "idle"
    \/ (mainPC = "idle" /\ paletteOps >= MaxPaletteOps)
    \/ (mainPC = "m_has_swift" /\ CanAcquireRustWrite("Main"))
    \/ mainPC = "m_has_swift_rustW"
    \/ (mainPC = "m_has_swift_preSnapshot" /\ CanAcquireRustRead("Main"))
    \/ mainPC = "m_has_swift_rustR_snapshot"
    \/ (mainPC = "m_has_swift_preDelegate" /\ CanAcquireSwift("Main"))
    \/ (mainPC = "m_has_swift2" /\ CanAcquireRustRead("Main"))
    \/ mainPC = "m_has_swift2_rustR"
    \/ mainPC = "m_has_swift2_done"
    \/ mainPC = "m_release_outer"

IOCanProgress ==
    \/ ioPC = "idle"
    \/ (ioPC = "idle" /\ processCalls >= MaxProcessCalls)
    \/ (ioPC = "io_has_swift" /\ CanAcquireRustWrite("IO"))
    \/ ioPC = "io_has_swift_rustW"
    \/ ioPC = "io_release_swift"

NoDeadlock ==
    \/ MainCanProgress
    \/ IOCanProgress

(***************************************************************************)
(* LIVENESS                                                                *)
(***************************************************************************)

\* If main starts palette op, it eventually finishes
MainEventuallyIdle ==
    mainPC /= "idle" ~> mainPC = "idle"

\* If IO starts process, it eventually finishes
IOEventuallyIdle ==
    ioPC /= "idle" ~> ioPC = "idle"

=============================================================================
