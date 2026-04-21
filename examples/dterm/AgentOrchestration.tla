------------------------ MODULE AgentOrchestration ------------------------
(***************************************************************************)
(* Agent Orchestration State Machine                                        *)
(*                                                                         *)
(* Models the orchestration of multiple AI agents executing terminal        *)
(* commands with approval workflows in dterm:                              *)
(* - Agent lifecycle: spawn, assign, execute, complete, fail               *)
(* - Command routing to capable agents                                      *)
(* - Concurrent execution with resource management                         *)
(* - Terminal session pool allocation                                       *)
(* - Dependency ordering between commands                                   *)
(*                                                                         *)
(* Integration: Works with AgentApproval.tla for command approval.         *)
(*                                                                         *)
(* Safety Properties:                                                       *)
(* - No command assigned to multiple agents simultaneously                 *)
(* - No orphaned executions without assigned agents                        *)
(* - Terminal exclusivity (one execution per terminal)                     *)
(* - Dependencies respected (command waits for predecessors)               *)
(* - Agent capability matching enforced                                    *)
(*                                                                         *)
(* Liveness Properties:                                                     *)
(* - Assigned commands eventually complete or fail                         *)
(* - Queued commands eventually get assigned                               *)
(* - Released terminals become available                                   *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxAgents,          \* Maximum number of concurrent agents
    MaxCommands,        \* Maximum commands in queue
    MaxTerminals,       \* Terminal session pool size
    MaxExecutions,      \* Maximum concurrent executions
    Capabilities,       \* Set of capability types (e.g., {"shell", "file", "net"})
    CommandTypes        \* Set of command types

(***************************************************************************)
(* Helper Functions (defined early for use in invariants)                  *)
(***************************************************************************)

\* Get sequence elements as a set
Range(s) == {s[i]: i \in 1..Len(s)}

VARIABLES
    agents,             \* Function: AgentId -> Agent record
    commandQueue,       \* Sequence of pending commands awaiting assignment
    executions,         \* Function: ExecutionId -> Execution record
    terminals,          \* Function: TerminalId -> Terminal record
    completedCommands,  \* Set of completed command IDs for dependency resolution
    nextAgentId,        \* Next agent ID to assign
    nextCommandId,      \* Next command ID to assign
    nextExecutionId     \* Next execution ID to assign

(***************************************************************************)
(* Type Definitions                                                        *)
(***************************************************************************)

AgentStates == {"Idle", "Assigned", "Executing", "Completed", "Failed", "Cancelled"}

Agent == [
    id: Nat,
    state: AgentStates,
    capabilities: SUBSET Capabilities,
    currentCommandId: Nat \union {-1},    \* -1 means no command
    currentExecutionId: Nat \union {-1}   \* -1 means no execution
]

Command == [
    id: Nat,
    commandType: CommandTypes,
    requiredCapabilities: SUBSET Capabilities,
    dependencies: SUBSET Nat,              \* Set of command IDs that must complete first
    approved: BOOLEAN                      \* Whether approved via AgentApproval workflow
]

ExecutionStates == {"Running", "Succeeded", "Failed", "Cancelled"}

Execution == [
    id: Nat,
    agentId: Nat,
    commandId: Nat,
    terminalId: Nat,
    state: ExecutionStates,
    startTime: Nat,
    endTime: Nat \union {-1}              \* -1 means still running
]

TerminalStates == {"Available", "InUse", "Closed"}

Terminal == [
    id: Nat,
    state: TerminalStates,
    currentExecutionId: Nat \union {-1}   \* -1 means not in use
]

(***************************************************************************)
(* Type Invariant                                                          *)
(***************************************************************************)

TypeInvariant ==
    /\ nextAgentId \in Nat
    /\ nextCommandId \in Nat
    /\ nextExecutionId \in Nat
    /\ DOMAIN agents \subseteq 0..(MaxAgents - 1)
    /\ DOMAIN executions \subseteq 0..(MaxExecutions - 1)
    /\ DOMAIN terminals \subseteq 0..(MaxTerminals - 1)
    /\ completedCommands \subseteq Nat
    /\ commandQueue \in Seq(Command)
    /\ Len(commandQueue) <= MaxCommands
    /\ \A aid \in DOMAIN agents:
        /\ agents[aid].id = aid
        /\ agents[aid].state \in AgentStates
        /\ agents[aid].capabilities \subseteq Capabilities
    /\ \A eid \in DOMAIN executions:
        /\ executions[eid].id = eid
        /\ executions[eid].state \in ExecutionStates
    /\ \A tid \in DOMAIN terminals:
        /\ terminals[tid].id = tid
        /\ terminals[tid].state \in TerminalStates

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* INV-ORCH-1: No command assigned to multiple agents simultaneously
NoDoubleAssignment ==
    \A aid1, aid2 \in DOMAIN agents:
        (aid1 # aid2 /\ agents[aid1].currentCommandId # -1) =>
        agents[aid1].currentCommandId # agents[aid2].currentCommandId

\* INV-ORCH-2: Every execution has an assigned agent
NoOrphanedExecutions ==
    \A eid \in DOMAIN executions:
        executions[eid].state = "Running" =>
        \E aid \in DOMAIN agents:
            /\ agents[aid].currentExecutionId = eid
            /\ agents[aid].state = "Executing"

\* INV-ORCH-3: Terminal used by at most one execution at a time
TerminalExclusivity ==
    \A tid \in DOMAIN terminals:
        terminals[tid].state = "InUse" =>
        Cardinality({eid \in DOMAIN executions:
            executions[eid].terminalId = tid /\
            executions[eid].state = "Running"}) = 1

\* INV-ORCH-4: Command only executes after dependencies complete
DependencyRespected ==
    \A eid \in DOMAIN executions:
        LET cmdId == executions[eid].commandId
            cmd == CHOOSE c \in {c \in Range(commandQueue): c.id = cmdId}: TRUE
        IN
            \* All dependencies must be in completedCommands before execution starts
            cmd.dependencies \subseteq completedCommands

\* INV-ORCH-5: Agent has required capabilities for assigned command
AgentCapabilityMatch ==
    \A aid \in DOMAIN agents:
        agents[aid].currentCommandId # -1 =>
        LET cmdId == agents[aid].currentCommandId
        IN \A c \in Range(commandQueue):
            c.id = cmdId => c.requiredCapabilities \subseteq agents[aid].capabilities

\* INV-ORCH-6: Executing agent has valid terminal
ExecutingAgentHasTerminal ==
    \A aid \in DOMAIN agents:
        agents[aid].state = "Executing" =>
        \E eid \in DOMAIN executions:
            /\ agents[aid].currentExecutionId = eid
            /\ \E tid \in DOMAIN terminals:
                /\ executions[eid].terminalId = tid
                /\ terminals[tid].state = "InUse"
                /\ terminals[tid].currentExecutionId = eid

\* INV-ORCH-7: Only approved commands can execute
OnlyApprovedExecute ==
    \A eid \in DOMAIN executions:
        LET cmdId == executions[eid].commandId
        IN \A c \in Range(commandQueue):
            c.id = cmdId => c.approved

\* Combined safety invariant
SafetyInvariant ==
    /\ NoDoubleAssignment
    /\ NoOrphanedExecutions
    /\ TerminalExclusivity
    /\ AgentCapabilityMatch
    /\ ExecutingAgentHasTerminal
    /\ OnlyApprovedExecute

(***************************************************************************)
(* Helper Functions                                                        *)
(***************************************************************************)

\* Available terminals
AvailableTerminals == {tid \in DOMAIN terminals: terminals[tid].state = "Available"}

\* Idle agents
IdleAgents == {aid \in DOMAIN agents: agents[aid].state = "Idle"}

\* Check if command dependencies are satisfied
DependenciesSatisfied(cmd) ==
    cmd.dependencies \subseteq completedCommands

\* Check if agent can handle command
CanHandle(agentId, cmd) ==
    /\ agentId \in DOMAIN agents
    /\ cmd.requiredCapabilities \subseteq agents[agentId].capabilities

\* Commands ready for assignment (approved, dependencies met, not assigned)
ReadyCommands ==
    {i \in 1..Len(commandQueue):
        /\ commandQueue[i].approved
        /\ DependenciesSatisfied(commandQueue[i])
        /\ ~\E aid \in DOMAIN agents: agents[aid].currentCommandId = commandQueue[i].id}

(***************************************************************************)
(* State Machine Operations                                                *)
(***************************************************************************)

\* Initial state
Init ==
    /\ agents = [aid \in {} |-> <<>>]
    /\ commandQueue = <<>>
    /\ executions = [eid \in {} |-> <<>>]
    /\ terminals = [tid \in 0..(MaxTerminals - 1) |->
        [id |-> tid, state |-> "Available", currentExecutionId |-> -1]]
    /\ completedCommands = {}
    /\ nextAgentId = 0
    /\ nextCommandId = 0
    /\ nextExecutionId = 0

\* SpawnAgent: Create new agent with capabilities
SpawnAgent(caps) ==
    /\ nextAgentId < MaxAgents
    /\ caps # {}                          \* Must have at least one capability
    /\ caps \subseteq Capabilities
    /\ LET newId == nextAgentId
           newAgent == [
               id |-> newId,
               state |-> "Idle",
               capabilities |-> caps,
               currentCommandId |-> -1,
               currentExecutionId |-> -1
           ]
       IN
           /\ agents' = agents @@ (newId :> newAgent)
           /\ nextAgentId' = nextAgentId + 1
           /\ UNCHANGED <<commandQueue, executions, terminals, completedCommands,
                         nextCommandId, nextExecutionId>>

\* QueueCommand: Add command to queue (pre-approval or auto-approved)
QueueCommand(cmdType, reqCaps, deps, approved) ==
    /\ Len(commandQueue) < MaxCommands
    /\ cmdType \in CommandTypes
    /\ reqCaps \subseteq Capabilities
    /\ deps \subseteq completedCommands \union {c.id: c \in Range(commandQueue)}
    /\ LET newCmd == [
           id |-> nextCommandId,
           commandType |-> cmdType,
           requiredCapabilities |-> reqCaps,
           dependencies |-> deps,
           approved |-> approved
       ]
       IN
           /\ commandQueue' = Append(commandQueue, newCmd)
           /\ nextCommandId' = nextCommandId + 1
           /\ UNCHANGED <<agents, executions, terminals, completedCommands,
                         nextAgentId, nextExecutionId>>

\* ApproveCommand: Mark queued command as approved (integration with AgentApproval)
ApproveCommand(cmdId) ==
    /\ \E i \in 1..Len(commandQueue):
        /\ commandQueue[i].id = cmdId
        /\ ~commandQueue[i].approved
        /\ commandQueue' = [commandQueue EXCEPT ![i].approved = TRUE]
    /\ UNCHANGED <<agents, executions, terminals, completedCommands,
                  nextAgentId, nextCommandId, nextExecutionId>>

\* AssignCommand: Route command to idle agent with matching capabilities
AssignCommand(agentId, cmdIndex) ==
    /\ agentId \in IdleAgents
    /\ cmdIndex \in ReadyCommands
    /\ CanHandle(agentId, commandQueue[cmdIndex])
    /\ agents' = [agents EXCEPT
        ![agentId].state = "Assigned",
        ![agentId].currentCommandId = commandQueue[cmdIndex].id]
    /\ UNCHANGED <<commandQueue, executions, terminals, completedCommands,
                  nextAgentId, nextCommandId, nextExecutionId>>

\* BeginExecution: Start command execution, allocate terminal
BeginExecution(agentId) ==
    /\ agentId \in DOMAIN agents
    /\ agents[agentId].state = "Assigned"
    /\ agents[agentId].currentCommandId # -1
    /\ AvailableTerminals # {}
    /\ nextExecutionId < MaxExecutions
    /\ LET termId == CHOOSE tid \in AvailableTerminals: TRUE
           execId == nextExecutionId
           newExec == [
               id |-> execId,
               agentId |-> agentId,
               commandId |-> agents[agentId].currentCommandId,
               terminalId |-> termId,
               state |-> "Running",
               startTime |-> 0,    \* Would be clock in real impl
               endTime |-> -1
           ]
       IN
           /\ agents' = [agents EXCEPT
               ![agentId].state = "Executing",
               ![agentId].currentExecutionId = execId]
           /\ executions' = executions @@ (execId :> newExec)
           /\ terminals' = [terminals EXCEPT
               ![termId].state = "InUse",
               ![termId].currentExecutionId = execId]
           /\ nextExecutionId' = nextExecutionId + 1
           /\ UNCHANGED <<commandQueue, completedCommands, nextAgentId, nextCommandId>>

\* CompleteExecution: Mark execution as succeeded, release resources
CompleteExecution(agentId) ==
    /\ agentId \in DOMAIN agents
    /\ agents[agentId].state = "Executing"
    /\ agents[agentId].currentExecutionId # -1
    /\ LET execId == agents[agentId].currentExecutionId
           cmdId == agents[agentId].currentCommandId
           termId == executions[execId].terminalId
       IN
           /\ agents' = [agents EXCEPT
               ![agentId].state = "Completed",
               ![agentId].currentCommandId = -1,
               ![agentId].currentExecutionId = -1]
           /\ executions' = [executions EXCEPT
               ![execId].state = "Succeeded",
               ![execId].endTime = 1]   \* Would be clock in real impl
           /\ terminals' = [terminals EXCEPT
               ![termId].state = "Available",
               ![termId].currentExecutionId = -1]
           /\ completedCommands' = completedCommands \union {cmdId}
           /\ UNCHANGED <<commandQueue, nextAgentId, nextCommandId, nextExecutionId>>

\* FailExecution: Mark execution as failed, release resources
FailExecution(agentId) ==
    /\ agentId \in DOMAIN agents
    /\ agents[agentId].state = "Executing"
    /\ agents[agentId].currentExecutionId # -1
    /\ LET execId == agents[agentId].currentExecutionId
           termId == executions[execId].terminalId
       IN
           /\ agents' = [agents EXCEPT
               ![agentId].state = "Failed",
               ![agentId].currentCommandId = -1,
               ![agentId].currentExecutionId = -1]
           /\ executions' = [executions EXCEPT
               ![execId].state = "Failed",
               ![execId].endTime = 1]
           /\ terminals' = [terminals EXCEPT
               ![termId].state = "Available",
               ![termId].currentExecutionId = -1]
           /\ UNCHANGED <<commandQueue, completedCommands, nextAgentId,
                         nextCommandId, nextExecutionId>>

\* CancelExecution: Cancel in-progress execution
CancelExecution(agentId) ==
    /\ agentId \in DOMAIN agents
    /\ agents[agentId].state \in {"Assigned", "Executing"}
    /\ LET hasExec == agents[agentId].currentExecutionId # -1
           execId == agents[agentId].currentExecutionId
       IN
           /\ agents' = [agents EXCEPT
               ![agentId].state = "Cancelled",
               ![agentId].currentCommandId = -1,
               ![agentId].currentExecutionId = -1]
           /\ IF hasExec THEN
                  LET termId == executions[execId].terminalId
                  IN
                      /\ executions' = [executions EXCEPT
                          ![execId].state = "Cancelled",
                          ![execId].endTime = 1]
                      /\ terminals' = [terminals EXCEPT
                          ![termId].state = "Available",
                          ![termId].currentExecutionId = -1]
              ELSE
                  /\ UNCHANGED <<executions, terminals>>
           /\ UNCHANGED <<commandQueue, completedCommands, nextAgentId,
                         nextCommandId, nextExecutionId>>

\* ResetAgent: Return completed/failed/cancelled agent to idle state
ResetAgent(agentId) ==
    /\ agentId \in DOMAIN agents
    /\ agents[agentId].state \in {"Completed", "Failed", "Cancelled"}
    /\ agents' = [agents EXCEPT ![agentId].state = "Idle"]
    /\ UNCHANGED <<commandQueue, executions, terminals, completedCommands,
                  nextAgentId, nextCommandId, nextExecutionId>>

\* CloseTerminal: Mark terminal as closed (cleanup)
CloseTerminal(termId) ==
    /\ termId \in DOMAIN terminals
    /\ terminals[termId].state = "Available"
    /\ terminals' = [terminals EXCEPT ![termId].state = "Closed"]
    /\ UNCHANGED <<agents, commandQueue, executions, completedCommands,
                  nextAgentId, nextCommandId, nextExecutionId>>

(***************************************************************************)
(* State Machine Specification                                             *)
(***************************************************************************)

Next ==
    \/ \E caps \in SUBSET Capabilities: caps # {} /\ SpawnAgent(caps)
    \/ \E ct \in CommandTypes, caps \in SUBSET Capabilities,
          deps \in SUBSET completedCommands, appr \in BOOLEAN:
        QueueCommand(ct, caps, deps, appr)
    \/ \E cmdId \in {c.id: c \in Range(commandQueue)}: ApproveCommand(cmdId)
    \/ \E aid \in IdleAgents, idx \in ReadyCommands: AssignCommand(aid, idx)
    \/ \E aid \in DOMAIN agents: BeginExecution(aid)
    \/ \E aid \in DOMAIN agents: CompleteExecution(aid)
    \/ \E aid \in DOMAIN agents: FailExecution(aid)
    \/ \E aid \in DOMAIN agents: CancelExecution(aid)
    \/ \E aid \in DOMAIN agents: ResetAgent(aid)
    \/ \E tid \in DOMAIN terminals: CloseTerminal(tid)

Spec == Init /\ [][Next]_<<agents, commandQueue, executions, terminals,
                          completedCommands, nextAgentId, nextCommandId,
                          nextExecutionId>>

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* Every assigned command eventually completes or fails (with fairness)
EventualCompletion ==
    \A aid \in DOMAIN agents:
        agents[aid].state = "Assigned" ~>
        agents[aid].state \in {"Completed", "Failed", "Cancelled"}

\* Queued commands eventually get assigned (with fairness and available agents)
NoStarvation ==
    \A i \in 1..Len(commandQueue):
        (commandQueue[i].approved /\ DependenciesSatisfied(commandQueue[i])) ~>
        (\E aid \in DOMAIN agents: agents[aid].currentCommandId = commandQueue[i].id)

\* Released terminals become available
TerminalReclamation ==
    \A tid \in DOMAIN terminals:
        terminals[tid].state = "InUse" ~>
        terminals[tid].state \in {"Available", "Closed"}

(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)

\* THEOREM: Commands are never double-assigned
THEOREM NoDoubleAssignmentHolds ==
    Spec => []NoDoubleAssignment

\* THEOREM: Executions always have backing agents
THEOREM NoOrphanedExecutionsHolds ==
    Spec => []NoOrphanedExecutions

\* THEOREM: Terminal pool maintains exclusivity
THEOREM TerminalExclusivityHolds ==
    Spec => []TerminalExclusivity

\* THEOREM: Agent capabilities always match command requirements
THEOREM CapabilityMatchHolds ==
    Spec => []AgentCapabilityMatch

\* THEOREM: Executing agents always have terminals
THEOREM ExecutingHasTerminalHolds ==
    Spec => []ExecutingAgentHasTerminal

\* THEOREM: Only approved commands execute
THEOREM ApprovalRequiredHolds ==
    Spec => []OnlyApprovedExecute

\* THEOREM: Agent IDs are monotonically increasing
THEOREM AgentIdMonotonic ==
    Spec => [][nextAgentId' >= nextAgentId]_nextAgentId

\* THEOREM: Command IDs are monotonically increasing
THEOREM CommandIdMonotonic ==
    Spec => [][nextCommandId' >= nextCommandId]_nextCommandId

\* THEOREM: Completed commands set only grows
THEOREM CompletedCommandsMonotonic ==
    Spec => [][completedCommands \subseteq completedCommands']_completedCommands

=============================================================================
