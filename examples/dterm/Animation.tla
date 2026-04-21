---------------------------- MODULE Animation ----------------------------
(****************************************************************************)
(* TLA+ Specification for Graphics Animation State Machine                  *)
(*                                                                          *)
(* This specification defines:                                              *)
(* - Animation states (Stopped, Running, Paused)                           *)
(* - Frame management (add, remove, advance)                               *)
(* - Loop control (infinite, finite loops)                                 *)
(* - Memory bounds (frame count limits)                                    *)
(*                                                                          *)
(* Reference: Kitty Graphics Protocol                                       *)
(* Implementation: crates/dterm-core/src/kitty_graphics/storage.rs         *)
(****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets

(****************************************************************************)
(* CONSTANTS                                                                *)
(****************************************************************************)

CONSTANTS
    MaxFrames,            \* Maximum frames per image (1000 in impl)
    MaxLoops,             \* Maximum loop count for testing
    MaxImages             \* Maximum images for model checking

\* Constraint assumptions
ASSUME MaxFrames \in Nat /\ MaxFrames > 0
ASSUME MaxLoops \in Nat
ASSUME MaxImages \in Nat /\ MaxImages > 0

(****************************************************************************)
(* ANIMATION STATE DEFINITIONS                                              *)
(****************************************************************************)

\* Animation states (matching AnimationState enum)
AnimationStates == {"Stopped", "Running", "Paused"}

\* Loop modes
\* 0 = not set (play once)
\* 1 = infinite loop
\* >1 = loop (n-1) times
LoopModes == 0..MaxLoops

(****************************************************************************)
(* VARIABLES                                                                *)
(****************************************************************************)

VARIABLES
    \* Per-image state (simplified to single image for model checking)
    animation_state,      \* Current animation state
    frame_count,          \* Number of frames (not including root)
    current_frame,        \* Current frame index (0 = root)
    max_loops,            \* Loop count setting
    current_loop          \* Current loop iteration

vars == <<animation_state, frame_count, current_frame, max_loops, current_loop>>

(****************************************************************************)
(* TYPE INVARIANT                                                           *)
(****************************************************************************)

TypeInvariant ==
    /\ animation_state \in AnimationStates
    /\ frame_count \in 0..MaxFrames
    /\ current_frame \in 0..MaxFrames
    /\ max_loops \in LoopModes
    /\ current_loop \in 0..MaxLoops

(****************************************************************************)
(* SAFETY INVARIANTS                                                        *)
(****************************************************************************)

\* INV-ANIM-1: Frame count never exceeds maximum
FrameCountBounded ==
    frame_count <= MaxFrames

\* INV-ANIM-2: Current frame within valid range
CurrentFrameValid ==
    current_frame <= frame_count

\* INV-ANIM-3: Current loop doesn't exceed max (when set)
LoopCountValid ==
    (max_loops > 1) => (current_loop < max_loops)

\* INV-ANIM-4: Animation only runs if there are frames
RunningImpliesFrames ==
    (animation_state = "Running") => (frame_count > 0)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ FrameCountBounded
    /\ CurrentFrameValid
    /\ LoopCountValid

(****************************************************************************)
(* INITIAL STATE                                                            *)
(****************************************************************************)

Init ==
    /\ animation_state = "Stopped"
    /\ frame_count = 0
    /\ current_frame = 0
    /\ max_loops = 0
    /\ current_loop = 0

(****************************************************************************)
(* FRAME MANAGEMENT ACTIONS                                                 *)
(****************************************************************************)

\* Add a new frame (a=f action)
AddFrame ==
    /\ frame_count < MaxFrames
    /\ frame_count' = frame_count + 1
    /\ UNCHANGED <<animation_state, current_frame, max_loops, current_loop>>

\* Remove a specific frame
RemoveFrame ==
    /\ frame_count > 0
    /\ frame_count' = frame_count - 1
    \* Clamp current frame if it was at the removed frame
    /\ current_frame' = IF current_frame > frame_count' THEN frame_count' ELSE current_frame
    /\ UNCHANGED <<animation_state, max_loops, current_loop>>

\* Clear all frames (d=F action)
ClearFrames ==
    /\ frame_count' = 0
    /\ current_frame' = 0
    /\ current_loop' = 0
    /\ animation_state' = "Stopped"
    /\ UNCHANGED <<max_loops>>

(****************************************************************************)
(* ANIMATION CONTROL ACTIONS                                                *)
(****************************************************************************)

\* Start animation (a=a,s=1 action)
StartAnimation ==
    /\ frame_count > 0  \* Need frames to animate
    /\ animation_state = "Stopped"
    /\ animation_state' = "Running"
    /\ current_frame' = 0
    /\ current_loop' = 0
    /\ UNCHANGED <<frame_count, max_loops>>

\* Pause animation (a=a,s=2 action)
PauseAnimation ==
    /\ animation_state = "Running"
    /\ animation_state' = "Paused"
    /\ UNCHANGED <<frame_count, current_frame, max_loops, current_loop>>

\* Resume animation (a=a,s=1 from paused)
ResumeAnimation ==
    /\ animation_state = "Paused"
    /\ animation_state' = "Running"
    /\ UNCHANGED <<frame_count, current_frame, max_loops, current_loop>>

\* Stop animation (a=a,s=3 action)
StopAnimation ==
    /\ animation_state' = "Stopped"
    /\ UNCHANGED <<frame_count, current_frame, max_loops, current_loop>>

\* Set loop count (a=a,v=N action)
\* Can only be set when animation is stopped to prevent
\* max_loops < current_loop invariant violation.
\* Also resets current_loop to 0 to ensure invariant holds.
SetLoopCount(n) ==
    /\ animation_state = "Stopped"
    /\ n \in LoopModes
    /\ max_loops' = n
    /\ current_loop' = 0
    /\ UNCHANGED <<animation_state, frame_count, current_frame>>

(****************************************************************************)
(* FRAME ADVANCE ACTIONS                                                    *)
(****************************************************************************)

\* Advance to next frame (called by timer)
AdvanceFrame ==
    /\ animation_state = "Running"
    /\ frame_count > 0
    /\ LET next == current_frame + 1
       IN IF next > frame_count
          THEN \* End of frames
               IF max_loops = 1
               THEN \* Infinite loop - restart
                    /\ current_frame' = 0
                    /\ UNCHANGED <<animation_state, frame_count, max_loops, current_loop>>
               ELSE IF max_loops > 1 /\ current_loop + 1 < max_loops
               THEN \* Finite loops - check if more loops
                    /\ current_frame' = 0
                    /\ current_loop' = current_loop + 1
                    /\ UNCHANGED <<animation_state, frame_count, max_loops>>
               ELSE \* Stop animation
                    /\ animation_state' = "Stopped"
                    /\ current_frame' = frame_count  \* Stay at last frame
                    /\ UNCHANGED <<frame_count, max_loops, current_loop>>
          ELSE \* Normal advance
               /\ current_frame' = next
               /\ UNCHANGED <<animation_state, frame_count, max_loops, current_loop>>

\* Jump to specific frame
JumpToFrame(n) ==
    /\ n \in 0..frame_count
    /\ current_frame' = n
    /\ UNCHANGED <<animation_state, frame_count, max_loops, current_loop>>

(****************************************************************************)
(* NEXT STATE RELATION                                                      *)
(****************************************************************************)

Next ==
    \/ AddFrame
    \/ RemoveFrame
    \/ ClearFrames
    \/ StartAnimation
    \/ PauseAnimation
    \/ ResumeAnimation
    \/ StopAnimation
    \/ \E n \in LoopModes : SetLoopCount(n)
    \/ AdvanceFrame
    \/ \E n \in 0..MaxFrames : JumpToFrame(n)

(****************************************************************************)
(* SPECIFICATION                                                            *)
(****************************************************************************)

Spec == Init /\ [][Next]_vars

(****************************************************************************)
(* LIVENESS PROPERTIES                                                      *)
(****************************************************************************)

\* Animation eventually stops (for finite loops)
AnimationTerminates ==
    (max_loops > 1) => <>(animation_state = "Stopped")

(****************************************************************************)
(* THEOREMS                                                                 *)
(****************************************************************************)

\* Frame count is always bounded
THEOREM FrameBoundTheorem == Spec => []FrameCountBounded

\* Current frame is always valid
THEOREM CurrentFrameTheorem == Spec => []CurrentFrameValid

\* Type invariant is maintained
THEOREM TypeTheorem == Spec => []TypeInvariant

=============================================================================
