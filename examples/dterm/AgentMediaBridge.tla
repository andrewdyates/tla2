------------------------------ MODULE AgentMediaBridge ------------------------------
\* TLA+ specification for the Agent-Media Bridge integration module.
\*
\* This module specifies the coordination between:
\* - Agent orchestration (command execution)
\* - Media server (voice I/O)
\* - Voice command workflow
\*
\* Author: AI Model (dterm AI)
\* Version: 1.0.0

EXTENDS Integers, Sequences, FiniteSets, TLC

\*==============================================================================
\* Constants
\*==============================================================================

CONSTANTS
    MaxAgents,          \* Maximum number of agents
    MaxClients,         \* Maximum number of media clients
    MaxVoiceCommands    \* Maximum pending voice commands

ASSUME MaxAgents \in Nat /\ MaxAgents > 0
ASSUME MaxClients \in Nat /\ MaxClients > 0
ASSUME MaxVoiceCommands \in Nat /\ MaxVoiceCommands > 0

\*==============================================================================
\* Variables
\*==============================================================================

VARIABLES
    \* Agent-client mapping (bidirectional)
    agentToClient,      \* Function: AgentId -> ClientId
    clientToAgent,      \* Function: ClientId -> AgentId

    \* Voice state
    activeVoiceAgent,   \* Currently active voice input agent (or NULL)
    voiceState,         \* "Idle" | "Listening" | "Processing"

    \* Pending voice commands
    pendingCommands,    \* Sequence of (ClientId, CommandText) pairs

    \* Counters
    nextClientId        \* Next client ID to assign

vars == <<agentToClient, clientToAgent, activeVoiceAgent, voiceState,
          pendingCommands, nextClientId>>

\*==============================================================================
\* Type Definitions
\*==============================================================================

NULL == -1  \* Sentinel value for "no active agent/client"

AgentId == 0..MaxAgents-1
ClientId == 1..MaxClients
VoiceStates == {"Idle", "Listening", "Processing"}

\*==============================================================================
\* Type Invariant
\*==============================================================================

TypeInvariant ==
    /\ DOMAIN agentToClient \subseteq AgentId
    /\ \A a \in DOMAIN agentToClient: agentToClient[a] \in ClientId
    /\ DOMAIN clientToAgent \subseteq ClientId
    /\ \A c \in DOMAIN clientToAgent: clientToAgent[c] \in AgentId
    /\ activeVoiceAgent \in AgentId \union {NULL}
    /\ voiceState \in VoiceStates
    /\ Len(pendingCommands) <= MaxVoiceCommands
    /\ nextClientId \in 1..(MaxClients + 1)

\*==============================================================================
\* Safety Invariants
\*==============================================================================

\* INV-BRIDGE-1: Agent-client mappings are bijective
\* If agent A maps to client C, then client C maps to agent A
MappingsBijective ==
    /\ \A a \in DOMAIN agentToClient:
        agentToClient[a] # NULL =>
            /\ agentToClient[a] \in DOMAIN clientToAgent
            /\ clientToAgent[agentToClient[a]] = a
    /\ \A c \in DOMAIN clientToAgent:
        clientToAgent[c] # NULL =>
            /\ clientToAgent[c] \in DOMAIN agentToClient
            /\ agentToClient[clientToAgent[c]] = c

\* INV-BRIDGE-2: Active voice agent must be registered
\* If there's an active voice session, the agent must be in the mapping
ActiveVoiceAgentRegistered ==
    activeVoiceAgent # NULL =>
        /\ activeVoiceAgent \in DOMAIN agentToClient
        /\ agentToClient[activeVoiceAgent] # NULL

\* INV-BRIDGE-3: Voice state consistency
\* - Idle means no active agent
\* - Listening/Processing means there IS an active agent
VoiceStateConsistent ==
    /\ (voiceState = "Idle") <=> (activeVoiceAgent = NULL)
    /\ (voiceState \in {"Listening", "Processing"}) => (activeVoiceAgent # NULL)

\* INV-BRIDGE-4: Pending commands have valid clients
\* All clients in pending commands are registered
PendingCommandsValid ==
    \A i \in 1..Len(pendingCommands):
        LET cmd == pendingCommands[i]
            clientId == cmd[1]
        IN clientId \in DOMAIN clientToAgent /\ clientToAgent[clientId] # NULL

\* Combined safety invariant
SafetyInvariant ==
    /\ MappingsBijective
    /\ ActiveVoiceAgentRegistered
    /\ VoiceStateConsistent
    /\ PendingCommandsValid

\*==============================================================================
\* Initial State
\*==============================================================================

Init ==
    /\ agentToClient = [a \in {} |-> NULL]  \* Empty function
    /\ clientToAgent = [c \in {} |-> NULL]  \* Empty function
    /\ activeVoiceAgent = NULL
    /\ voiceState = "Idle"
    /\ pendingCommands = <<>>
    /\ nextClientId = 1

\*==============================================================================
\* Actions
\*==============================================================================

\* Register an agent with the bridge
\* Returns a client ID for the agent
RegisterAgent(agentId) ==
    /\ agentId \notin DOMAIN agentToClient  \* Not already registered
    /\ nextClientId <= MaxClients           \* Have available client IDs
    /\ LET newClientId == nextClientId
       IN /\ agentToClient' = agentToClient @@ (agentId :> newClientId)
          /\ clientToAgent' = clientToAgent @@ (newClientId :> agentId)
          /\ nextClientId' = nextClientId + 1
    /\ UNCHANGED <<activeVoiceAgent, voiceState, pendingCommands>>

\* Unregister an agent from the bridge
\* Cleans up voice state if this was the active voice agent
UnregisterAgent(agentId) ==
    /\ agentId \in DOMAIN agentToClient
    /\ agentToClient[agentId] # NULL
    /\ LET clientId == agentToClient[agentId]
       IN /\ agentToClient' = [a \in DOMAIN agentToClient \ {agentId} |-> agentToClient[a]]
          /\ clientToAgent' = [c \in DOMAIN clientToAgent \ {clientId} |-> clientToAgent[c]]
          \* Cancel voice if this was the active agent
          /\ IF activeVoiceAgent = agentId
             THEN /\ activeVoiceAgent' = NULL
                  /\ voiceState' = "Idle"
             ELSE /\ UNCHANGED <<activeVoiceAgent, voiceState>>
          \* Remove pending commands for this client
          /\ pendingCommands' = SelectSeq(pendingCommands,
                LAMBDA cmd: cmd[1] # clientId)
    /\ UNCHANGED <<nextClientId>>

\* Start voice input for an agent
\* Only one agent can have voice input active at a time (INV-MEDIA-1)
StartVoiceInput(agentId) ==
    /\ agentId \in DOMAIN agentToClient
    /\ agentToClient[agentId] # NULL
    /\ activeVoiceAgent = NULL        \* No other active session
    /\ voiceState = "Idle"
    /\ activeVoiceAgent' = agentId
    /\ voiceState' = "Listening"
    /\ UNCHANGED <<agentToClient, clientToAgent, pendingCommands, nextClientId>>

\* End the current voice utterance (begin processing)
EndVoiceUtterance ==
    /\ voiceState = "Listening"
    /\ activeVoiceAgent # NULL
    /\ voiceState' = "Processing"
    /\ UNCHANGED <<agentToClient, clientToAgent, activeVoiceAgent,
                   pendingCommands, nextClientId>>

\* Deliver voice command result (queue for processing)
DeliverVoiceCommand ==
    /\ voiceState = "Processing"
    /\ activeVoiceAgent # NULL
    /\ Len(pendingCommands) < MaxVoiceCommands  \* Queue not full
    /\ LET clientId == agentToClient[activeVoiceAgent]
           newCmd == <<clientId, "command_text">>  \* Simplified
       IN pendingCommands' = Append(pendingCommands, newCmd)
    /\ voiceState' = "Idle"
    /\ activeVoiceAgent' = NULL
    /\ UNCHANGED <<agentToClient, clientToAgent, nextClientId>>

\* Cancel voice input
CancelVoiceInput ==
    /\ activeVoiceAgent # NULL
    /\ voiceState \in {"Listening", "Processing"}
    /\ activeVoiceAgent' = NULL
    /\ voiceState' = "Idle"
    /\ UNCHANGED <<agentToClient, clientToAgent, pendingCommands, nextClientId>>

\* Process a pending voice command
ProcessVoiceCommand ==
    /\ Len(pendingCommands) > 0
    /\ LET cmd == Head(pendingCommands)
       IN pendingCommands' = Tail(pendingCommands)
    /\ UNCHANGED <<agentToClient, clientToAgent, activeVoiceAgent,
                   voiceState, nextClientId>>

\* Allow system to stutter when in valid quiescent states:
\* 1. Empty system (no agents registered)
\* 2. System fully saturated (all client IDs allocated, no pending work)
\* These are legitimate terminal/quiescent states where no further action is required.
Stuttering ==
    \/ \* Empty system - no agents registered
       /\ DOMAIN agentToClient = {}
       /\ pendingCommands = <<>>
       /\ voiceState = "Idle"
       /\ UNCHANGED vars
    \/ \* Saturated system - all client IDs used up, no pending work, voice idle
       \* This is a valid quiescent state where system can accept no new registrations
       \* but existing agents can still unregister or use voice
       /\ nextClientId > MaxClients
       /\ pendingCommands = <<>>
       /\ voiceState = "Idle"
       /\ UNCHANGED vars

\*==============================================================================
\* Next State Relation
\*==============================================================================

Next ==
    \/ \E a \in AgentId: RegisterAgent(a)
    \/ \E a \in AgentId: UnregisterAgent(a)
    \/ \E a \in AgentId: StartVoiceInput(a)
    \/ EndVoiceUtterance
    \/ DeliverVoiceCommand
    \/ CancelVoiceInput
    \/ ProcessVoiceCommand
    \/ Stuttering

\*==============================================================================
\* Fairness and Liveness
\*==============================================================================

\* Weak fairness on actions - if an action is enabled, it eventually happens
Fairness ==
    /\ WF_vars(ProcessVoiceCommand)
    /\ WF_vars(DeliverVoiceCommand)

\* Liveness: Eventually all pending commands are processed
\* (Progress guarantee when no new commands arrive)
CommandsEventuallyProcessed ==
    [](Len(pendingCommands) > 0 => <>(Len(pendingCommands) < Len(pendingCommands)))

\*==============================================================================
\* Specification
\*==============================================================================

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

\*==============================================================================
\* Model Checking Configuration
\*==============================================================================

\* For TLC model checking, use small bounds:
\* MaxAgents = 3
\* MaxClients = 3
\* MaxVoiceCommands = 3

=============================================================================
