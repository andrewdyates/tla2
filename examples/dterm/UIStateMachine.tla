------------------------ MODULE UIStateMachine ------------------------
(***************************************************************************)
(* UI Integration State Machine                                           *)
(*                                                                         *)
(* Models the UI bridge between platform UI and dterm-core:                *)
(* - Event intake and queueing                                             *)
(* - UI state transitions (idle, processing, rendering, callbacks)         *)
(* - Terminal lifecycle management                                         *)
(* - Callback dispatch and completion                                      *)
(*                                                                         *)
(* Safety Properties:                                                      *)
(* - No event loss across enqueue/process                                 *)
(* - No duplicate event IDs                                                *)
(* - Disposed terminals never resurrect                                   *)
(* - UI state consistent with in-flight work                              *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* CONSTANTS                                                               *)
(***************************************************************************)

CONSTANTS
    MaxTerminals,       \* Maximum terminals tracked by UI bridge
    MaxQueue,           \* Maximum pending events in queue
    MaxEvents,          \* Maximum unique event IDs
    MaxCallbacks,       \* Maximum unique callback IDs
    NULL                \* Sentinel for "no terminal/callback"

ASSUME MaxTerminals \in Nat /\ MaxTerminals > 0
ASSUME MaxQueue \in Nat /\ MaxQueue > 0
ASSUME MaxEvents \in Nat /\ MaxEvents > 0
ASSUME MaxCallbacks \in Nat /\ MaxCallbacks > 0

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)

VARIABLES
    ui_state,           \* Current UI state
    terminal_states,    \* Map: terminal ID -> terminal state
    pending_events,     \* FIFO queue of pending events
    current_event,      \* Event currently being processed (or NULL)
    callbacks_pending,  \* Set of outstanding callback IDs
    render_pending,     \* Set of terminals awaiting render completion
    received_events,    \* Set of event IDs observed by UI
    processed_events    \* Set of event IDs already processed

vars == <<ui_state, terminal_states, pending_events, current_event,
          callbacks_pending, render_pending, received_events, processed_events>>

(***************************************************************************)
(* TYPE DEFINITIONS                                                        *)
(***************************************************************************)

UIStates == {"Idle", "Processing", "Rendering", "WaitingForCallback", "ShuttingDown"}

TerminalStates == {"Inactive", "Active", "Disposed"}

EventKinds == {"Input", "Resize", "Render", "CreateTerminal",
               "DestroyTerminal", "RequestCallback", "Shutdown"}

TerminalIds == 0..(MaxTerminals - 1)
EventIds == 0..(MaxEvents - 1)
CallbackIds == 0..(MaxCallbacks - 1)

ASSUME NULL \notin TerminalIds
ASSUME NULL \notin EventIds
ASSUME NULL \notin CallbackIds

Event == [
    id: EventIds,
    kind: EventKinds,
    terminal: TerminalIds \cup {NULL},
    callback: CallbackIds \cup {NULL}
]

ValidEvent(e) ==
    /\ e.kind \in EventKinds
    /\ IF e.kind = "Shutdown" THEN
        /\ e.terminal = NULL
        /\ e.callback = NULL
      ELSE
        /\ e.terminal \in TerminalIds
        /\ IF e.kind = "RequestCallback"
              THEN e.callback \in CallbackIds
              ELSE e.callback = NULL

Events == {e \in Event: ValidEvent(e)}

(***************************************************************************)
(* HELPER FUNCTIONS                                                        *)
(***************************************************************************)

Range(seq) == {seq[i]: i \in 1..Len(seq)}

PendingEventIds == {e.id: e \in Range(pending_events)}

CurrentEventIds == IF current_event = NULL THEN {} ELSE {current_event.id}

MakeEvent(eid, kind, term, cb) ==
    [id |-> eid, kind |-> kind, terminal |-> term, callback |-> cb]

InvalidEvent(e) ==
    CASE e.kind = "CreateTerminal" ->
            terminal_states[e.terminal] # "Inactive"
       [] e.kind = "DestroyTerminal" ->
            terminal_states[e.terminal] # "Active"
       [] e.kind = "Render" ->
            terminal_states[e.terminal] # "Active"
       [] e.kind = "Resize" ->
            terminal_states[e.terminal] # "Active"
       [] e.kind = "Input" ->
            terminal_states[e.terminal] # "Active"
       [] e.kind = "RequestCallback" ->
            terminal_states[e.terminal] # "Active" \/
            e.callback \in callbacks_pending
       [] e.kind = "Shutdown" -> FALSE

(***************************************************************************)
(* TYPE INVARIANT                                                          *)
(***************************************************************************)

TypeInvariant ==
    /\ ui_state \in UIStates
    /\ terminal_states \in [TerminalIds -> TerminalStates]
    /\ pending_events \in Seq(Events)
    /\ current_event \in Events \cup {NULL}
    /\ callbacks_pending \subseteq CallbackIds
    /\ render_pending \subseteq TerminalIds
    /\ received_events \subseteq EventIds
    /\ processed_events \subseteq EventIds
    /\ Len(pending_events) <= MaxQueue
    /\ (ui_state = "Processing") <=> (current_event # NULL)
    /\ (ui_state = "Idle" =>
        /\ current_event = NULL
        /\ callbacks_pending = {}
        /\ render_pending = {})
    /\ (render_pending # {} => ui_state = "Rendering")
    /\ (callbacks_pending # {} => ui_state = "WaitingForCallback")
    /\ (ui_state = "ShuttingDown" => current_event = NULL)

(***************************************************************************)
(* SAFETY INVARIANTS                                                       *)
(***************************************************************************)

EventsPreserved ==
    received_events = processed_events \cup PendingEventIds \cup CurrentEventIds

ProcessedSubsetReceived ==
    processed_events \subseteq received_events

NoDuplicatePendingIds ==
    \A i, j \in 1..Len(pending_events):
        i # j => pending_events[i].id # pending_events[j].id

NoDuplicateEventIds ==
    /\ NoDuplicatePendingIds
    /\ PendingEventIds \cap processed_events = {}
    /\ CurrentEventIds \cap PendingEventIds = {}
    /\ CurrentEventIds \cap processed_events = {}

SafetyInvariant ==
    /\ EventsPreserved
    /\ ProcessedSubsetReceived
    /\ NoDuplicateEventIds

(***************************************************************************)
(* INITIAL STATE                                                           *)
(***************************************************************************)

Init ==
    /\ ui_state = "Idle"
    /\ terminal_states = [tid \in TerminalIds |-> "Inactive"]
    /\ pending_events = <<>>
    /\ current_event = NULL
    /\ callbacks_pending = {}
    /\ render_pending = {}
    /\ received_events = {}
    /\ processed_events = {}

(***************************************************************************)
(* EVENT INTAKE                                                            *)
(***************************************************************************)

EnqueueEvent(kind, term, cb) ==
    /\ ui_state # "ShuttingDown"
    /\ Len(pending_events) < MaxQueue
    /\ \E eid \in EventIds \ received_events:
        LET newEvent == MakeEvent(eid, kind, term, cb)
        IN
            /\ ValidEvent(newEvent)
            /\ pending_events' = Append(pending_events, newEvent)
            /\ received_events' = received_events \cup {eid}
            /\ UNCHANGED <<ui_state, terminal_states, current_event,
                          callbacks_pending, render_pending, processed_events>>

StartProcessing ==
    /\ ui_state = "Idle"
    /\ pending_events # <<>>
    /\ current_event = NULL
    /\ LET ev == Head(pending_events)
       IN
           /\ current_event' = ev
           /\ pending_events' = Tail(pending_events)
           /\ ui_state' = "Processing"
           /\ UNCHANGED <<terminal_states, callbacks_pending, render_pending,
                          received_events, processed_events>>

(***************************************************************************)
(* EVENT PROCESSING                                                        *)
(***************************************************************************)

ProcessInputResize ==
    /\ ui_state = "Processing"
    /\ current_event.kind \in {"Input", "Resize"}
    /\ terminal_states[current_event.terminal] = "Active"
    /\ current_event' = NULL
    /\ processed_events' = processed_events \cup {current_event.id}
    /\ ui_state' = "Idle"
    /\ UNCHANGED <<terminal_states, pending_events, callbacks_pending,
                  render_pending, received_events>>

ProcessCreateTerminal ==
    /\ ui_state = "Processing"
    /\ current_event.kind = "CreateTerminal"
    /\ terminal_states[current_event.terminal] = "Inactive"
    /\ terminal_states' = [terminal_states EXCEPT
        ![current_event.terminal] = "Active"]
    /\ current_event' = NULL
    /\ processed_events' = processed_events \cup {current_event.id}
    /\ ui_state' = "Idle"
    /\ UNCHANGED <<pending_events, callbacks_pending, render_pending,
                  received_events>>

ProcessDestroyTerminal ==
    /\ ui_state = "Processing"
    /\ current_event.kind = "DestroyTerminal"
    /\ terminal_states[current_event.terminal] = "Active"
    /\ terminal_states' = [terminal_states EXCEPT
        ![current_event.terminal] = "Disposed"]
    /\ current_event' = NULL
    /\ processed_events' = processed_events \cup {current_event.id}
    /\ ui_state' = "Idle"
    /\ UNCHANGED <<pending_events, callbacks_pending, render_pending,
                  received_events>>

ProcessRender ==
    /\ ui_state = "Processing"
    /\ current_event.kind = "Render"
    /\ terminal_states[current_event.terminal] = "Active"
    /\ render_pending' = render_pending \cup {current_event.terminal}
    /\ current_event' = NULL
    /\ processed_events' = processed_events \cup {current_event.id}
    /\ ui_state' = "Rendering"
    /\ UNCHANGED <<terminal_states, pending_events, callbacks_pending,
                  received_events>>

ProcessRequestCallback ==
    /\ ui_state = "Processing"
    /\ current_event.kind = "RequestCallback"
    /\ terminal_states[current_event.terminal] = "Active"
    /\ current_event.callback \notin callbacks_pending
    /\ callbacks_pending' = callbacks_pending \cup {current_event.callback}
    /\ current_event' = NULL
    /\ processed_events' = processed_events \cup {current_event.id}
    /\ ui_state' = "WaitingForCallback"
    /\ UNCHANGED <<terminal_states, pending_events, render_pending,
                  received_events>>

ProcessShutdown ==
    /\ ui_state = "Processing"
    /\ current_event.kind = "Shutdown"
    /\ pending_events' = <<>>
    /\ current_event' = NULL
    /\ callbacks_pending' = {}
    /\ render_pending' = {}
    /\ processed_events' = processed_events \cup PendingEventIds \cup {current_event.id}
    /\ ui_state' = "ShuttingDown"
    /\ UNCHANGED <<terminal_states, received_events>>

DropInvalidEvent ==
    /\ ui_state = "Processing"
    /\ current_event # NULL
    /\ InvalidEvent(current_event)
    /\ current_event' = NULL
    /\ processed_events' = processed_events \cup {current_event.id}
    /\ ui_state' = "Idle"
    /\ UNCHANGED <<terminal_states, pending_events, callbacks_pending,
                  render_pending, received_events>>

(***************************************************************************)
(* ASYNC COMPLETIONS                                                       *)
(***************************************************************************)

CompleteRender ==
    /\ ui_state = "Rendering"
    /\ render_pending # {}
    /\ LET t == CHOOSE tid \in render_pending: TRUE
       IN
           /\ render_pending' = render_pending \ {t}
           /\ ui_state' = IF render_pending' = {} THEN "Idle" ELSE "Rendering"
           /\ UNCHANGED <<terminal_states, pending_events, current_event,
                          callbacks_pending, received_events, processed_events>>

CompleteCallback ==
    /\ ui_state = "WaitingForCallback"
    /\ callbacks_pending # {}
    /\ LET cb == CHOOSE cid \in callbacks_pending: TRUE
       IN
           /\ callbacks_pending' = callbacks_pending \ {cb}
           /\ ui_state' = IF callbacks_pending' = {} THEN "Idle" ELSE "WaitingForCallback"
           /\ UNCHANGED <<terminal_states, pending_events, current_event,
                          render_pending, received_events, processed_events>>

(***************************************************************************)
(* STATE MACHINE SPECIFICATION                                             *)
(***************************************************************************)

Next ==
    \/ \E kind \in EventKinds,
         term \in TerminalIds \cup {NULL},
         cb \in CallbackIds \cup {NULL}:
        EnqueueEvent(kind, term, cb)
    \/ StartProcessing
    \/ ProcessInputResize
    \/ ProcessCreateTerminal
    \/ ProcessDestroyTerminal
    \/ ProcessRender
    \/ ProcessRequestCallback
    \/ ProcessShutdown
    \/ DropInvalidEvent
    \/ CompleteRender
    \/ CompleteCallback

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* THEOREMS                                                                *)
(***************************************************************************)

DisposedMonotonicAction ==
    \A t \in TerminalIds:
        terminal_states[t] = "Disposed" => terminal_states'[t] = "Disposed"

THEOREM TypeInvariantHolds ==
    Spec => []TypeInvariant

THEOREM SafetyInvariantHolds ==
    Spec => []SafetyInvariant

THEOREM DisposedMonotonicHolds ==
    Spec => [][DisposedMonotonicAction]_terminal_states

=============================================================================
