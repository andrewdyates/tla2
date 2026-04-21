----------------------- MODULE TmuxControlMode -----------------------
(***************************************************************************)
(* TLA+ Specification for dterm tmux Control Mode (-CC) Protocol           *)
(*                                                                         *)
(* This specification models:                                              *)
(* 1. Parser state machine (Idle, InBlock, Broken)                         *)
(* 2. Control mode state machine (Inactive, Active)                        *)
(* 3. Command block protocol (%begin/%end/%error)                          *)
(* 4. Session lifecycle (attach, detach, session-changed, exit)            *)
(* 5. Message ordering invariants                                          *)
(*                                                                         *)
(* Reference: tmux manual "control mode" section                           *)
(* Implementation: crates/dterm-core/src/tmux/{mod.rs, parser.rs}          *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* CONSTANTS                                                               *)
(***************************************************************************)

CONSTANTS
    \* Parser states
    Idle,
    InBlock,
    Broken,

    \* Control mode states
    Inactive,
    Active,

    \* Line types
    BeginLine,
    EndLine,
    ErrorLine,
    DataLine,
    NotificationLine,

    \* Notification types
    SessionChanged,
    Exit,
    Output,
    WindowAdd,
    WindowClose,
    Other,

    \* Maximum values for bounded model checking
    MAX_SESSION_ID,
    MAX_WINDOW_ID,
    MAX_PANE_ID,
    MAX_CMD_NUM,
    MAX_TIMESTAMP,
    MAX_PENDING_BLOCKS

ParserStates == {Idle, InBlock, Broken}
ControlModeStates == {Inactive, Active}
LineTypes == {BeginLine, EndLine, ErrorLine, DataLine, NotificationLine}
NotificationTypes == {SessionChanged, Exit, Output, WindowAdd, WindowClose, Other}

SessionIds == 0..MAX_SESSION_ID
WindowIds == 0..MAX_WINDOW_ID
PaneIds == 0..MAX_PANE_ID
CmdNums == 0..MAX_CMD_NUM
Timestamps == 0..MAX_TIMESTAMP

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)

VARIABLES
    \* Parser state
    parserState,
    currentBlockCmdNum,     \* cmd_num of current block (when InBlock)
    currentBlockTimestamp,  \* timestamp of current block (when InBlock)
    currentBlockFlags,      \* flags of current block (when InBlock)

    \* Control mode state
    controlModeActive,
    sessionId,              \* Current session ID (when active)
    sessionName,            \* Current session name (when active)

    \* Protocol tracking
    commandCounter,         \* Next command number to issue
    pendingBlocks,          \* Set of pending block cmd_nums (for ordering)

    \* For specification - trace of events
    eventTrace

vars == <<parserState, currentBlockCmdNum, currentBlockTimestamp, currentBlockFlags,
          controlModeActive, sessionId, sessionName, commandCounter, pendingBlocks, eventTrace>>

(***************************************************************************)
(* TYPE INVARIANT                                                          *)
(***************************************************************************)

TypeInvariant ==
    /\ parserState \in ParserStates
    /\ currentBlockCmdNum \in CmdNums \cup {-1}
    /\ currentBlockTimestamp \in Timestamps \cup {-1}
    /\ currentBlockFlags \in 0..65535 \cup {-1}
    /\ controlModeActive \in BOOLEAN
    /\ sessionId \in SessionIds \cup {-1}
    /\ sessionName \in {"", "default", "main", "dev", "work"}
    /\ commandCounter \in CmdNums
    /\ pendingBlocks \subseteq CmdNums
    /\ Cardinality(pendingBlocks) <= MAX_PENDING_BLOCKS
    /\ eventTrace \in Seq(LineTypes)
    /\ Len(eventTrace) <= 100

(***************************************************************************)
(* SAFETY INVARIANTS                                                       *)
(***************************************************************************)

\* INV-TM-1: Session info only valid when control mode is active
SessionInfoValidity ==
    (sessionId # -1 /\ sessionName # "") => controlModeActive

\* INV-TM-2: Block state only valid when parser is InBlock
BlockStateValidity ==
    (parserState = InBlock) <=> (currentBlockCmdNum # -1)

\* INV-TM-3: Pending blocks only exist when control mode is active
PendingBlocksValidity ==
    (pendingBlocks # {}) => controlModeActive

\* INV-TM-4: Parser cannot be InBlock when control mode is inactive
InBlockRequiresActive ==
    (parserState = InBlock) => controlModeActive

\* Combined safety invariant
SafetyInvariant ==
    /\ SessionInfoValidity
    /\ BlockStateValidity
    /\ PendingBlocksValidity
    /\ InBlockRequiresActive

(***************************************************************************)
(* INITIAL STATE                                                           *)
(***************************************************************************)

Init ==
    /\ parserState = Idle
    /\ currentBlockCmdNum = -1
    /\ currentBlockTimestamp = -1
    /\ currentBlockFlags = -1
    /\ controlModeActive = FALSE
    /\ sessionId = -1
    /\ sessionName = ""
    /\ commandCounter = 0
    /\ pendingBlocks = {}
    /\ eventTrace = <<>>

(***************************************************************************)
(* CONTROL MODE ACTIONS                                                    *)
(***************************************************************************)

\* Activate control mode (tmux -CC detected)
Activate ==
    /\ ~controlModeActive
    /\ controlModeActive' = TRUE
    /\ parserState' = Idle
    /\ currentBlockCmdNum' = -1
    /\ currentBlockTimestamp' = -1
    /\ currentBlockFlags' = -1
    /\ pendingBlocks' = {}
    /\ UNCHANGED <<sessionId, sessionName, commandCounter, eventTrace>>

\* Deactivate control mode (exit or disconnect)
Deactivate ==
    /\ controlModeActive
    /\ controlModeActive' = FALSE
    /\ parserState' = Idle
    /\ currentBlockCmdNum' = -1
    /\ currentBlockTimestamp' = -1
    /\ currentBlockFlags' = -1
    /\ sessionId' = -1
    /\ sessionName' = ""
    /\ pendingBlocks' = {}
    /\ UNCHANGED <<commandCounter, eventTrace>>

(***************************************************************************)
(* PARSER ACTIONS                                                          *)
(***************************************************************************)

\* Process %begin line: enter InBlock state
ProcessBegin(ts, cmdNum, flags) ==
    /\ controlModeActive
    /\ parserState = Idle
    /\ ts \in Timestamps
    /\ cmdNum \in CmdNums
    /\ flags \in 0..65535
    /\ parserState' = InBlock
    /\ currentBlockTimestamp' = ts
    /\ currentBlockCmdNum' = cmdNum
    /\ currentBlockFlags' = flags
    /\ pendingBlocks' = pendingBlocks \cup {cmdNum}
    /\ eventTrace' = Append(eventTrace, BeginLine)
    /\ UNCHANGED <<controlModeActive, sessionId, sessionName, commandCounter>>

\* Process %end line: return to Idle, must match cmd_num
ProcessEnd(ts, cmdNum, flags) ==
    /\ controlModeActive
    /\ parserState = InBlock
    /\ cmdNum = currentBlockCmdNum  \* Must match!
    /\ ts \in Timestamps
    /\ flags \in 0..65535
    /\ parserState' = Idle
    /\ currentBlockTimestamp' = -1
    /\ currentBlockCmdNum' = -1
    /\ currentBlockFlags' = -1
    /\ pendingBlocks' = pendingBlocks \ {cmdNum}
    /\ eventTrace' = Append(eventTrace, EndLine)
    /\ UNCHANGED <<controlModeActive, sessionId, sessionName, commandCounter>>

\* Process %error line: return to Idle, must match cmd_num
ProcessError(ts, cmdNum, flags) ==
    /\ controlModeActive
    /\ parserState = InBlock
    /\ cmdNum = currentBlockCmdNum  \* Must match!
    /\ ts \in Timestamps
    /\ flags \in 0..65535
    /\ parserState' = Idle
    /\ currentBlockTimestamp' = -1
    /\ currentBlockCmdNum' = -1
    /\ currentBlockFlags' = -1
    /\ pendingBlocks' = pendingBlocks \ {cmdNum}
    /\ eventTrace' = Append(eventTrace, ErrorLine)
    /\ UNCHANGED <<controlModeActive, sessionId, sessionName, commandCounter>>

\* Process data line (only valid inside block)
ProcessDataLine ==
    /\ controlModeActive
    /\ parserState = InBlock
    /\ eventTrace' = Append(eventTrace, DataLine)
    /\ UNCHANGED <<parserState, currentBlockCmdNum, currentBlockTimestamp, currentBlockFlags,
                   controlModeActive, sessionId, sessionName, commandCounter, pendingBlocks>>

\* Process data line outside block (ignored)
IgnoreDataLine ==
    /\ controlModeActive
    /\ parserState = Idle
    /\ UNCHANGED vars

(***************************************************************************)
(* NOTIFICATION HANDLERS                                                   *)
(***************************************************************************)

\* Process %session-changed notification
ProcessSessionChanged(newSessionId, newName) ==
    /\ controlModeActive
    /\ parserState = Idle  \* Notifications outside blocks
    /\ newSessionId \in SessionIds
    /\ newName \in {"default", "main", "dev", "work"}
    /\ sessionId' = newSessionId
    /\ sessionName' = newName
    /\ eventTrace' = Append(eventTrace, NotificationLine)
    /\ UNCHANGED <<parserState, currentBlockCmdNum, currentBlockTimestamp, currentBlockFlags,
                   controlModeActive, commandCounter, pendingBlocks>>

\* Process %exit notification
ProcessExit ==
    /\ controlModeActive
    /\ parserState = Idle
    /\ eventTrace' = Append(eventTrace, NotificationLine)
    \* Exit triggers deactivation
    /\ controlModeActive' = FALSE
    /\ parserState' = Idle
    /\ currentBlockCmdNum' = -1
    /\ currentBlockTimestamp' = -1
    /\ currentBlockFlags' = -1
    /\ sessionId' = -1
    /\ sessionName' = ""
    /\ pendingBlocks' = {}
    /\ UNCHANGED <<commandCounter>>

\* Process other notifications (output, window-add, etc.)
ProcessOtherNotification ==
    /\ controlModeActive
    /\ parserState = Idle
    /\ eventTrace' = Append(eventTrace, NotificationLine)
    /\ UNCHANGED <<parserState, currentBlockCmdNum, currentBlockTimestamp, currentBlockFlags,
                   controlModeActive, sessionId, sessionName, commandCounter, pendingBlocks>>

(***************************************************************************)
(* COMMAND ISSUING                                                         *)
(***************************************************************************)

\* Issue a new command (increment counter)
IssueCommand ==
    /\ controlModeActive
    /\ commandCounter < MAX_CMD_NUM
    /\ commandCounter' = commandCounter + 1
    /\ UNCHANGED <<parserState, currentBlockCmdNum, currentBlockTimestamp, currentBlockFlags,
                   controlModeActive, sessionId, sessionName, pendingBlocks, eventTrace>>

\* Command counter wrapping (when it reaches MAX)
WrapCommandCounter ==
    /\ controlModeActive
    /\ commandCounter = MAX_CMD_NUM
    /\ commandCounter' = 0
    /\ UNCHANGED <<parserState, currentBlockCmdNum, currentBlockTimestamp, currentBlockFlags,
                   controlModeActive, sessionId, sessionName, pendingBlocks, eventTrace>>

(***************************************************************************)
(* PARSER RESET                                                            *)
(***************************************************************************)

\* Reset parser (e.g., on protocol error recovery)
ResetParser ==
    /\ controlModeActive
    /\ parserState' = Idle
    /\ currentBlockCmdNum' = -1
    /\ currentBlockTimestamp' = -1
    /\ currentBlockFlags' = -1
    /\ UNCHANGED <<controlModeActive, sessionId, sessionName, commandCounter, pendingBlocks, eventTrace>>

(***************************************************************************)
(* NEXT STATE RELATION                                                     *)
(***************************************************************************)

Next ==
    \/ Activate
    \/ Deactivate
    \/ \E ts \in Timestamps, cmdNum \in CmdNums, flags \in 0..10:
          ProcessBegin(ts, cmdNum, flags)
    \/ \E ts \in Timestamps, cmdNum \in CmdNums, flags \in 0..10:
          ProcessEnd(ts, cmdNum, flags)
    \/ \E ts \in Timestamps, cmdNum \in CmdNums, flags \in 0..10:
          ProcessError(ts, cmdNum, flags)
    \/ ProcessDataLine
    \/ IgnoreDataLine
    \/ \E sid \in SessionIds, name \in {"default", "main", "dev", "work"}:
          ProcessSessionChanged(sid, name)
    \/ ProcessExit
    \/ ProcessOtherNotification
    \/ IssueCommand
    \/ WrapCommandCounter
    \/ ResetParser

(***************************************************************************)
(* SPECIFICATION                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* LIVENESS PROPERTIES                                                     *)
(***************************************************************************)

\* Eventually, if activated, control mode can be deactivated
CanDeactivate == controlModeActive ~> ~controlModeActive

\* A block that starts will eventually end
BlockEventuallyEnds ==
    (parserState = InBlock) ~> (parserState = Idle)

(***************************************************************************)
(* THEOREMS                                                                *)
(***************************************************************************)

\* Type safety is preserved
THEOREM Spec => []TypeInvariant

\* Safety invariants are preserved
THEOREM Spec => []SafetyInvariant

=============================================================================
\* Modification History
\* Created: 2026-01-19 by dterm RESEARCHER
\* Issue: #173 - tmux module has no TLA+ specification
