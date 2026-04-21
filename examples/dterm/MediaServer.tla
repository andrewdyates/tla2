---------------------------- MODULE MediaServer ----------------------------
(***************************************************************************)
(* Media Server Protocol State Machine                                     *)
(*                                                                         *)
(* Models the voice I/O protocol in dterm:                                 *)
(* - Direct TTS connection (bypass text rendering)                         *)
(* - Direct STT input handling                                             *)
(* - Audio stream management with latency constraints                      *)
(* - Platform-agnostic voice interface                                     *)
(*                                                                         *)
(* Architecture:                                                           *)
(*   User speaks → Local STT → Agent intent → Execution → TTS response    *)
(*                                                                         *)
(* Platform APIs modeled:                                                  *)
(* - macOS/iOS: Speech framework                                           *)
(* - Windows: Windows.Media.SpeechRecognition                             *)
(* - Linux: Vosk, Whisper.cpp                                             *)
(*                                                                         *)
(* Safety Properties:                                                       *)
(* - No concurrent STT sessions (one voice input at a time)               *)
(* - TTS queue depth bounded (prevent memory exhaustion)                   *)
(* - Audio streams properly released on disconnect                         *)
(* - No data loss during stream handoff                                    *)
(*                                                                         *)
(* Liveness Properties:                                                     *)
(* - STT results eventually delivered                                      *)
(* - TTS utterances eventually complete                                    *)
(* - Streams eventually close on disconnect                                *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxTTSQueueDepth,    \* Maximum queued TTS utterances
    MaxStreamDuration,   \* Maximum audio stream duration (ticks)
    MaxLatencyTicks,     \* Maximum acceptable latency (ticks)
    Clients,             \* Set of client identifiers (agents/terminals)
    AudioFormats,        \* Set of audio formats (e.g., {"PCM_16K", "OPUS"})
    NoClient,            \* Sentinel value for "no active client"
    Texts                \* Finite set of text strings for model checking

\* Constraint assumptions for model checking
ASSUME MaxTTSQueueDepth \in Nat /\ MaxTTSQueueDepth > 0
ASSUME MaxStreamDuration \in Nat /\ MaxStreamDuration > 0
ASSUME MaxLatencyTicks \in Nat /\ MaxLatencyTicks > 0
ASSUME Cardinality(Clients) > 0
ASSUME Cardinality(AudioFormats) > 0
ASSUME Cardinality(Texts) > 0

VARIABLES
    sttState,            \* STT session state
    ttsState,            \* TTS session state per client
    ttsQueues,           \* TTS utterance queues per client
    audioStreams,        \* Active audio streams
    clock,               \* Logical clock for latency tracking
    pendingResults,      \* STT results awaiting delivery
    activeClient         \* Currently active STT client (at most one)

vars == <<sttState, ttsState, ttsQueues, audioStreams, clock,
          pendingResults, activeClient>>

(***************************************************************************)
(* Helper Functions                                                        *)
(***************************************************************************)

\* Helper: Select elements from sequence matching predicate
\* Named FilterSeq to avoid conflict with Sequences!SelectSeq
FilterSeq(s, Test(_)) ==
    LET F[i \in 0..Len(s)] ==
        IF i = 0 THEN <<>>
        ELSE IF Test(s[i]) THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]

(***************************************************************************)
(* Type Definitions                                                        *)
(***************************************************************************)

\* STT (Speech-to-Text) session states
STTStates == {"Idle", "Listening", "Processing", "Error"}

\* TTS (Text-to-Speech) session states per client
TTSStates == {"Idle", "Speaking", "Paused", "Error"}

\* Audio stream states
StreamStates == {"Active", "Paused", "Closing", "Closed"}

\* Stream direction
StreamDirections == {"Input", "Output", "Bidirectional"}

\* An STT session record
STTSession == [
    state: STTStates,
    client: Clients \union {NoClient},    \* -1 = no client
    startTime: Nat,
    audioFormat: AudioFormats,
    partialText: Texts,             \* Partial recognition result
    confidence: 0..100              \* Recognition confidence %
]

\* A TTS utterance in the queue
TTSUtterance == [
    id: Nat,
    text: Texts,
    priority: 0..10,                \* 0 = lowest, 10 = highest (interrupts)
    queuedAt: Nat,
    audioFormat: AudioFormats
]

\* An audio stream record
AudioStream == [
    id: Nat,
    client: Clients,
    direction: StreamDirections,
    format: AudioFormats,
    state: StreamStates,
    startTime: Nat,
    bytesTransferred: Nat,
    latency: Nat                    \* Current latency in ticks
]

(***************************************************************************)
(* Type Invariant                                                          *)
(***************************************************************************)

TypeInvariant ==
    /\ sttState \in STTStates
    /\ activeClient \in Clients \union {NoClient}
    /\ clock \in Nat
    /\ DOMAIN ttsState \subseteq Clients
    /\ \A c \in DOMAIN ttsState: ttsState[c] \in TTSStates
    /\ DOMAIN ttsQueues \subseteq Clients
    /\ \A c \in DOMAIN ttsQueues:
        /\ ttsQueues[c] \in Seq(TTSUtterance)
        /\ Len(ttsQueues[c]) <= MaxTTSQueueDepth
    /\ pendingResults \in Seq([client: Clients, text: Texts, confidence: 0..100])
    /\ DOMAIN audioStreams \subseteq Nat
    /\ \A sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].id = sid
        /\ audioStreams[sid].client \in Clients
        /\ audioStreams[sid].direction \in StreamDirections
        /\ audioStreams[sid].format \in AudioFormats
        /\ audioStreams[sid].state \in StreamStates

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* INV-MEDIA-1: At most one STT session active at a time
SingleSTTSession ==
    sttState \in {"Listening", "Processing"} =>
    activeClient \in Clients

\* INV-MEDIA-2: TTS queue depth bounded per client
TTSQueueBounded ==
    \A c \in DOMAIN ttsQueues:
        Len(ttsQueues[c]) <= MaxTTSQueueDepth

\* INV-MEDIA-3: Active streams have valid clients
StreamClientsValid ==
    \A sid \in DOMAIN audioStreams:
        audioStreams[sid].state \in {"Active", "Paused"} =>
        audioStreams[sid].client \in Clients

\* INV-MEDIA-4: Latency within bounds (soft constraint - logged if violated)
LatencyBounded ==
    \A sid \in DOMAIN audioStreams:
        audioStreams[sid].state = "Active" =>
        audioStreams[sid].latency <= MaxLatencyTicks * 2  \* Allow 2x for spikes

\* INV-MEDIA-5: No orphaned processing state
NoOrphanedProcessing ==
    sttState = "Processing" => activeClient # NoClient

\* INV-MEDIA-6: Speaking client has TTS state
SpeakingClientHasState ==
    \A c \in Clients:
        c \in DOMAIN ttsState /\ ttsState[c] = "Speaking" =>
        \E sid \in DOMAIN audioStreams:
            /\ audioStreams[sid].client = c
            /\ audioStreams[sid].direction \in {"Output", "Bidirectional"}
            /\ audioStreams[sid].state = "Active"

\* INV-MEDIA-7: Idle STT has no active client
IdleSTTNoClient ==
    sttState = "Idle" => activeClient = NoClient

\* Combined safety invariant
SafetyInvariant ==
    /\ SingleSTTSession
    /\ TTSQueueBounded
    /\ StreamClientsValid
    /\ NoOrphanedProcessing
    /\ IdleSTTNoClient

(***************************************************************************)
(* Helper Functions                                                        *)
(***************************************************************************)

\* Get next stream ID
NextStreamId ==
    IF DOMAIN audioStreams = {} THEN 0
    ELSE (CHOOSE sid \in DOMAIN audioStreams:
          \A s2 \in DOMAIN audioStreams: sid >= s2) + 1

\* Count active streams for a client
ActiveStreamsForClient(client) ==
    Cardinality({sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client = client
        /\ audioStreams[sid].state \in {"Active", "Paused"}})

\* Get highest priority utterance in queue
HighestPriority(queue) ==
    IF queue = <<>> THEN <<>>
    ELSE LET maxPrio == CHOOSE p \in {queue[i].priority: i \in 1..Len(queue)}:
             \A i \in 1..Len(queue): queue[i].priority <= p
         IN CHOOSE i \in 1..Len(queue): queue[i].priority = maxPrio

\* Remove element at index from sequence
RemoveAt(seq, idx) ==
    SubSeq(seq, 1, idx - 1) \o SubSeq(seq, idx + 1, Len(seq))

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)

Init ==
    /\ sttState = "Idle"
    /\ activeClient = NoClient
    /\ ttsState = [c \in Clients |-> "Idle"]
    /\ ttsQueues = [c \in Clients |-> <<>>]
    /\ audioStreams = [sid \in {} |-> <<>>]
    /\ clock = 0
    /\ pendingResults = <<>>

(***************************************************************************)
(* STT (Speech-to-Text) Operations                                         *)
(***************************************************************************)

\* Start listening for voice input
StartSTT(client, format) ==
    /\ sttState = "Idle"
    /\ client \in Clients
    /\ format \in AudioFormats
    /\ sttState' = "Listening"
    /\ activeClient' = client
    \* Create input audio stream
    /\ LET newId == NextStreamId
           newStream == [
               id |-> newId,
               client |-> client,
               direction |-> "Input",
               format |-> format,
               state |-> "Active",
               startTime |-> clock,
               bytesTransferred |-> 0,
               latency |-> 0
           ]
       IN audioStreams' = audioStreams @@ (newId :> newStream)
    /\ UNCHANGED <<ttsState, ttsQueues, clock, pendingResults>>

\* STT receives audio data (incremental recognition)
STTReceiveAudio(partialText) ==
    /\ sttState = "Listening"
    /\ activeClient # NoClient
    \* Update stream bytes (model - actual bytes not tracked in detail)
    /\ \E sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client = activeClient
        /\ audioStreams[sid].direction = "Input"
        /\ audioStreams[sid].state = "Active"
        /\ audioStreams' = [audioStreams EXCEPT
            ![sid].bytesTransferred = @ + 1,
            ![sid].latency = IF clock - audioStreams[sid].startTime > MaxLatencyTicks
                            THEN clock - audioStreams[sid].startTime
                            ELSE @]
    /\ UNCHANGED <<sttState, activeClient, ttsState, ttsQueues, clock, pendingResults>>

\* End of utterance - begin processing
STTEndUtterance ==
    /\ sttState = "Listening"
    /\ activeClient # NoClient
    /\ sttState' = "Processing"
    \* Close input stream
    /\ \E sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client = activeClient
        /\ audioStreams[sid].direction = "Input"
        /\ audioStreams' = [audioStreams EXCEPT ![sid].state = "Closing"]
    /\ UNCHANGED <<activeClient, ttsState, ttsQueues, clock, pendingResults>>

\* STT processing complete - deliver result
STTDeliverResult(text, confidence) ==
    /\ sttState = "Processing"
    /\ activeClient # NoClient
    /\ confidence \in 0..100
    /\ LET result == [client |-> activeClient, text |-> text, confidence |-> confidence]
       IN pendingResults' = Append(pendingResults, result)
    /\ sttState' = "Idle"
    /\ activeClient' = NoClient
    \* Close input stream
    /\ \E sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client \in Clients  \* Was activeClient before reset
        /\ audioStreams[sid].direction = "Input"
        /\ audioStreams[sid].state = "Closing"
        /\ audioStreams' = [audioStreams EXCEPT ![sid].state = "Closed"]
    /\ UNCHANGED <<ttsState, ttsQueues, clock>>

\* Cancel STT session
CancelSTT ==
    /\ sttState \in {"Listening", "Processing"}
    /\ sttState' = "Idle"
    /\ activeClient' = NoClient
    \* Close any input streams
    /\ audioStreams' = [sid \in DOMAIN audioStreams |->
        IF audioStreams[sid].direction = "Input" /\
           audioStreams[sid].state \in {"Active", "Paused", "Closing"}
        THEN [audioStreams[sid] EXCEPT !.state = "Closed"]
        ELSE audioStreams[sid]]
    /\ UNCHANGED <<ttsState, ttsQueues, clock, pendingResults>>

\* STT error (recognition failed, timeout, etc.)
STTError ==
    /\ sttState \in {"Listening", "Processing"}
    /\ sttState' = "Idle"
    /\ activeClient' = NoClient
    \* Close streams
    /\ audioStreams' = [sid \in DOMAIN audioStreams |->
        IF audioStreams[sid].direction = "Input" /\
           audioStreams[sid].state \in {"Active", "Paused", "Closing"}
        THEN [audioStreams[sid] EXCEPT !.state = "Closed"]
        ELSE audioStreams[sid]]
    /\ UNCHANGED <<ttsState, ttsQueues, clock, pendingResults>>

(***************************************************************************)
(* TTS (Text-to-Speech) Operations                                         *)
(***************************************************************************)

\* Queue TTS utterance for a client
QueueTTS(client, text, priority, format) ==
    /\ client \in Clients
    /\ format \in AudioFormats
    /\ priority \in 0..10
    /\ Len(ttsQueues[client]) < MaxTTSQueueDepth
    /\ LET newUtterance == [
           id |-> clock,  \* Use clock as simple ID
           text |-> text,
           priority |-> priority,
           queuedAt |-> clock,
           audioFormat |-> format
       ]
       IN ttsQueues' = [ttsQueues EXCEPT ![client] = Append(@, newUtterance)]
    /\ UNCHANGED <<sttState, activeClient, ttsState, audioStreams, clock, pendingResults>>

\* Start speaking (dequeue and play)
StartTTS(client) ==
    /\ client \in Clients
    /\ ttsState[client] = "Idle"
    /\ Len(ttsQueues[client]) > 0
    /\ LET utterance == Head(ttsQueues[client])
           newId == NextStreamId
           newStream == [
               id |-> newId,
               client |-> client,
               direction |-> "Output",
               format |-> utterance.audioFormat,
               state |-> "Active",
               startTime |-> clock,
               bytesTransferred |-> 0,
               latency |-> clock - utterance.queuedAt  \* Initial latency
           ]
       IN
           /\ ttsState' = [ttsState EXCEPT ![client] = "Speaking"]
           /\ ttsQueues' = [ttsQueues EXCEPT ![client] = Tail(@)]
           /\ audioStreams' = audioStreams @@ (newId :> newStream)
    /\ UNCHANGED <<sttState, activeClient, clock, pendingResults>>

\* TTS utterance complete
CompleteTTS(client) ==
    /\ client \in Clients
    /\ ttsState[client] = "Speaking"
    /\ \E sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client = client
        /\ audioStreams[sid].direction = "Output"
        /\ audioStreams[sid].state = "Active"
        /\ audioStreams' = [audioStreams EXCEPT ![sid].state = "Closed"]
    /\ ttsState' = [ttsState EXCEPT ![client] = "Idle"]
    /\ UNCHANGED <<sttState, activeClient, ttsQueues, clock, pendingResults>>

\* Pause TTS playback
PauseTTS(client) ==
    /\ client \in Clients
    /\ ttsState[client] = "Speaking"
    /\ ttsState' = [ttsState EXCEPT ![client] = "Paused"]
    /\ \E sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client = client
        /\ audioStreams[sid].direction = "Output"
        /\ audioStreams[sid].state = "Active"
        /\ audioStreams' = [audioStreams EXCEPT ![sid].state = "Paused"]
    /\ UNCHANGED <<sttState, activeClient, ttsQueues, clock, pendingResults>>

\* Resume TTS playback
ResumeTTS(client) ==
    /\ client \in Clients
    /\ ttsState[client] = "Paused"
    /\ ttsState' = [ttsState EXCEPT ![client] = "Speaking"]
    /\ \E sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client = client
        /\ audioStreams[sid].direction = "Output"
        /\ audioStreams[sid].state = "Paused"
        /\ audioStreams' = [audioStreams EXCEPT ![sid].state = "Active"]
    /\ UNCHANGED <<sttState, activeClient, ttsQueues, clock, pendingResults>>

\* Cancel TTS (stop speaking, clear queue optionally)
CancelTTS(client, clearQueue) ==
    /\ client \in Clients
    /\ ttsState[client] \in {"Speaking", "Paused"}
    /\ ttsState' = [ttsState EXCEPT ![client] = "Idle"]
    /\ IF clearQueue THEN
           ttsQueues' = [ttsQueues EXCEPT ![client] = <<>>]
       ELSE UNCHANGED ttsQueues
    /\ \E sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client = client
        /\ audioStreams[sid].direction = "Output"
        /\ audioStreams[sid].state \in {"Active", "Paused"}
        /\ audioStreams' = [audioStreams EXCEPT ![sid].state = "Closed"]
    /\ UNCHANGED <<sttState, activeClient, clock, pendingResults>>

\* Interrupt TTS with high-priority utterance
InterruptTTS(client, text, format) ==
    /\ client \in Clients
    /\ ttsState[client] = "Speaking"
    /\ Len(ttsQueues[client]) < MaxTTSQueueDepth  \* Queue must have space
    \* Cancel current, queue new at front
    /\ \E sid \in DOMAIN audioStreams:
        /\ audioStreams[sid].client = client
        /\ audioStreams[sid].direction = "Output"
        /\ audioStreams' = [audioStreams EXCEPT ![sid].state = "Closed"]
    /\ LET interruptUtterance == [
           id |-> clock,
           text |-> text,
           priority |-> 10,  \* Highest priority
           queuedAt |-> clock,
           audioFormat |-> format
       ]
       IN ttsQueues' = [ttsQueues EXCEPT
           ![client] = <<interruptUtterance>> \o @]
    /\ ttsState' = [ttsState EXCEPT ![client] = "Idle"]  \* Will restart immediately
    /\ UNCHANGED <<sttState, activeClient, clock, pendingResults>>

(***************************************************************************)
(* Stream Management Operations                                            *)
(***************************************************************************)

\* Cleanup closed streams (garbage collection)
CleanupStreams ==
    /\ \E sid \in DOMAIN audioStreams:
        audioStreams[sid].state = "Closed"
    /\ audioStreams' = [sid \in {s \in DOMAIN audioStreams:
                                 audioStreams[s].state # "Closed"} |->
                        audioStreams[sid]]
    /\ UNCHANGED <<sttState, activeClient, ttsState, ttsQueues, clock, pendingResults>>

\* Stream timeout (duration exceeded)
StreamTimeout(streamId) ==
    /\ streamId \in DOMAIN audioStreams
    /\ audioStreams[streamId].state \in {"Active", "Paused"}
    /\ clock - audioStreams[streamId].startTime >= MaxStreamDuration
    /\ audioStreams' = [audioStreams EXCEPT ![streamId].state = "Closed"]
    \* Reset associated state
    /\ LET client == audioStreams[streamId].client
           dir == audioStreams[streamId].direction
       IN
           /\ IF dir = "Input" /\ activeClient = client THEN
                  /\ sttState' = "Idle"
                  /\ activeClient' = NoClient
              ELSE UNCHANGED <<sttState, activeClient>>
           /\ IF dir = "Output" /\ ttsState[client] \in {"Speaking", "Paused"} THEN
                  ttsState' = [ttsState EXCEPT ![client] = "Idle"]
              ELSE UNCHANGED ttsState
    /\ UNCHANGED <<ttsQueues, clock, pendingResults>>

(***************************************************************************)
(* Client Operations                                                       *)
(***************************************************************************)

\* Client disconnects - cleanup all resources
ClientDisconnect(client) ==
    /\ client \in Clients
    \* Close all streams for client
    /\ audioStreams' = [sid \in DOMAIN audioStreams |->
        IF audioStreams[sid].client = client /\
           audioStreams[sid].state \in {"Active", "Paused", "Closing"}
        THEN [audioStreams[sid] EXCEPT !.state = "Closed"]
        ELSE audioStreams[sid]]
    \* Reset STT if this client was active
    /\ IF activeClient = client THEN
           /\ sttState' = "Idle"
           /\ activeClient' = NoClient
       ELSE UNCHANGED <<sttState, activeClient>>
    \* Reset TTS state
    /\ ttsState' = [ttsState EXCEPT ![client] = "Idle"]
    /\ ttsQueues' = [ttsQueues EXCEPT ![client] = <<>>]
    \* Remove pending results for client
    /\ pendingResults' = FilterSeq(pendingResults,
        LAMBDA r: r.client # client)
    /\ UNCHANGED clock

\* Consume pending STT result
ConsumeResult(client) ==
    /\ Len(pendingResults) > 0
    /\ Head(pendingResults).client = client
    /\ pendingResults' = Tail(pendingResults)
    /\ UNCHANGED <<sttState, activeClient, ttsState, ttsQueues, audioStreams, clock>>

(***************************************************************************)
(* Clock Operations                                                        *)
(***************************************************************************)

\* Tick clock (for latency tracking and timeouts)
Tick ==
    /\ clock' = clock + 1
    /\ UNCHANGED <<sttState, activeClient, ttsState, ttsQueues, audioStreams, pendingResults>>

(***************************************************************************)
(* State Machine Specification                                             *)
(***************************************************************************)

Next ==
    \* STT operations
    \/ \E c \in Clients, f \in AudioFormats: StartSTT(c, f)
    \/ \E text \in Texts: STTReceiveAudio(text)
    \/ STTEndUtterance
    \/ \E text \in Texts, conf \in 0..100: STTDeliverResult(text, conf)
    \/ CancelSTT
    \/ STTError
    \* TTS operations
    \/ \E c \in Clients, text \in Texts, prio \in 0..10, f \in AudioFormats:
        QueueTTS(c, text, prio, f)
    \/ \E c \in Clients: StartTTS(c)
    \/ \E c \in Clients: CompleteTTS(c)
    \/ \E c \in Clients: PauseTTS(c)
    \/ \E c \in Clients: ResumeTTS(c)
    \/ \E c \in Clients, clear \in BOOLEAN: CancelTTS(c, clear)
    \/ \E c \in Clients, text \in Texts, f \in AudioFormats: InterruptTTS(c, text, f)
    \* Stream management
    \/ CleanupStreams
    \/ \E sid \in DOMAIN audioStreams: StreamTimeout(sid)
    \* Client operations
    \/ \E c \in Clients: ClientDisconnect(c)
    \/ \E c \in Clients: ConsumeResult(c)
    \* Clock
    \/ Tick

Spec == Init /\ [][Next]_vars

\* State constraint for bounded model checking
Constraint == clock < 5

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* STT results eventually delivered (with fairness)
STTResultsDelivered ==
    sttState = "Processing" ~>
    (sttState = "Idle" /\ (Len(pendingResults) > 0 \/ activeClient = NoClient))

\* TTS utterances eventually complete (with fairness)
TTSUtterancesComplete ==
    \A c \in Clients:
        ttsState[c] = "Speaking" ~>
        ttsState[c] \in {"Idle", "Paused"}

\* Streams eventually close on disconnect
StreamsEventuallyClosed ==
    \A sid \in DOMAIN audioStreams:
        audioStreams[sid].state \in {"Active", "Paused"} ~>
        audioStreams[sid].state = "Closed"

\* Queued TTS eventually plays (with fairness)
QueuedTTSPlays ==
    \A c \in Clients:
        (Len(ttsQueues[c]) > 0 /\ ttsState[c] = "Idle") ~>
        (ttsState[c] = "Speaking" \/ Len(ttsQueues[c]) = 0)

(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)

\* THEOREM: At most one STT session at a time
THEOREM SingleSTTHolds ==
    Spec => []SingleSTTSession

\* THEOREM: TTS queue never overflows
THEOREM TTSQueueBoundedHolds ==
    Spec => []TTSQueueBounded

\* THEOREM: Streams belong to valid clients
THEOREM StreamClientsValidHolds ==
    Spec => []StreamClientsValid

\* THEOREM: STT idle state consistent with client
THEOREM IdleSTTConsistentHolds ==
    Spec => []IdleSTTNoClient

\* THEOREM: Clock is monotonically increasing
THEOREM ClockMonotonic ==
    Spec => [][clock' >= clock]_clock

\* THEOREM: Once closed, stream stays closed
THEOREM ClosedStreamsFinal ==
    Spec => [](\A sid \in DOMAIN audioStreams:
        audioStreams[sid].state = "Closed" =>
        [][audioStreams[sid].state = "Closed" \/ sid \notin DOMAIN audioStreams']_audioStreams)

\* THEOREM: STT processing always has a client
THEOREM ProcessingHasClient ==
    Spec => []NoOrphanedProcessing

\* THEOREM: Pending results are consumed in order (FIFO)
\* Note: This is enforced by ConsumeResult only processing Head

(***************************************************************************)
(* Model Checking Configuration                                            *)
(*                                                                         *)
(* For tractable model checking, use small constants:                      *)
(* MaxTTSQueueDepth = 3                                                    *)
(* MaxStreamDuration = 5                                                   *)
(* MaxLatencyTicks = 2                                                     *)
(* Clients = {"agent1", "agent2"}                                          *)
(* AudioFormats = {"PCM_16K", "OPUS"}                                      *)
(* NoClient = "NO_CLIENT"                                                  *)
(* Texts = {"hello", "world", "test"}                                      *)
(***************************************************************************)

=============================================================================
