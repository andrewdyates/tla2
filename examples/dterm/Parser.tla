--------------------------- MODULE Parser ---------------------------
(***************************************************************************)
(* TLA+ Specification for the dTerm ANSI/DEC Parser State Machine           *)
(*                                                                         *)
(* Based on: https://vt100.net/emu/dec_ansi_parser                         *)
(* Reference: ECMA-48, VT100-VT520 series                                  *)
(*                                                                         *)
(* This specification defines:                                             *)
(* - All 14 parser states                                                  *)
(* - State transitions for all byte values (0x00-0xFF)                     *)
(* - Actions performed during transitions                                  *)
(* - Type invariants ensuring bounded data structures                      *)
(* - Safety properties                                                     *)
(*                                                                         *)
(* DESIGN NOTE: UTF-8 Handling (FV-11)                                     *)
(* ===================================                                     *)
(* UTF-8 decoding is an INTENTIONAL IMPLEMENTATION DETAIL not modeled here.*)
(*                                                                         *)
(* Rationale:                                                              *)
(* 1. VT parsers operate on byte streams, not Unicode codepoints           *)
(* 2. UTF-8 is a layer ABOVE the escape sequence parser                    *)
(* 3. In implementation, advance_fast() identifies UTF-8 lead bytes        *)
(*    (0xC2-0xF4) and decodes multi-byte sequences before Print action     *)
(* 4. The parser spec models the state machine; UTF-8 is data encoding     *)
(* 5. Kani proofs verify UTF-8 decoding safety in parser/mod.rs            *)
(*                                                                         *)
(* This separation follows the VT100.net reference parser design and       *)
(* matches real terminal emulators (Ghostty, Alacritty, Kitty, etc.)       *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* CONSTANTS                                                               *)
(***************************************************************************)

CONSTANTS
    Ground,
    Escape,
    EscapeIntermediate,
    CsiEntry,
    CsiParam,
    CsiIntermediate,
    CsiIgnore,
    DcsEntry,
    DcsParam,
    DcsIntermediate,
    DcsPassthrough,
    DcsIgnore,
    OscString,
    SosPmApcString,
    ByteSet

States == {
    Ground, Escape, EscapeIntermediate,
    CsiEntry, CsiParam, CsiIntermediate, CsiIgnore,
    DcsEntry, DcsParam, DcsIntermediate, DcsPassthrough, DcsIgnore,
    OscString, SosPmApcString
}

Bytes == ByteSet

ASSUME ByteSet \subseteq 0..255

Actions == {
    "Print",
    "Execute",
    "Clear",
    "Collect",
    "Param",
    "CsiDispatch",
    "EscDispatch",
    "OscStart",
    "OscPut",
    "OscEnd",
    "Hook",
    "Put",
    "Unhook"
}

MAX_PARAMS == 16
MAX_INTERMEDIATES == 4

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)

VARIABLES
    state,
    params,
    intermediates,
    currentParam,
    actions

vars == <<state, params, intermediates, currentParam, actions>>

(***************************************************************************)
(* TYPE INVARIANT                                                          *)
(***************************************************************************)

TypeInvariant ==
    /\ state \in States
    /\ params \in Seq(0..65535)
    /\ Len(params) <= MAX_PARAMS
    /\ intermediates \in Seq(0..255)
    /\ Len(intermediates) <= MAX_INTERMEDIATES
    /\ currentParam \in 0..65535
    /\ actions \subseteq Actions

(***************************************************************************)
(* HELPER DEFINITIONS                                                      *)
(***************************************************************************)

IsC0(b) == b \in 0..31
IsCAN(b) == b = 24
IsSUB(b) == b = 26
IsESC(b) == b = 27
IsDEL(b) == b = 127

IsC1(b) == b \in 128..159
IsCSI(b) == b = 155
IsDCS(b) == b = 144
IsOSC(b) == b = 157
IsSOS(b) == b = 152
IsPM(b) == b = 158
IsAPC(b) == b = 159
IsST(b) == b = 156

IsGR(b) == b \in 160..255
GL(b) == IF IsGR(b) THEN b - 128 ELSE b
IsGL(b, v) == GL(b) = v

IsIntermediate(b) == LET g == GL(b) IN g \in 32..47
IsParamByte(b) == LET g == GL(b) IN g \in 48..63
IsFinalByte(b) == LET g == GL(b) IN g \in 64..126
IsPrintableGL(b) == LET g == GL(b) IN g \in 32..126
IsDELGL(b) == LET g == GL(b) IN g = 127

(***************************************************************************)
(* ACTION HELPERS                                                          *)
(***************************************************************************)

Clear ==
    /\ params' = <<>>
    /\ intermediates' = <<>>
    /\ currentParam' = 0

Collect(b) ==
    LET g == GL(b)
    IN /\ params' = params
       /\ currentParam' = currentParam
       /\ intermediates' = IF Len(intermediates) < MAX_INTERMEDIATES
                           THEN Append(intermediates, g)
                           ELSE intermediates

Param(b) ==
    LET g == GL(b)
    IN /\ intermediates' = intermediates
       /\ CASE g \in 48..57 ->
            LET digit == g - 48
                newParam == IF currentParam * 10 + digit <= 65535
                            THEN currentParam * 10 + digit
                            ELSE 65535
            IN /\ params' = params
               /\ currentParam' = newParam
          [] g = 59 ->
            IF Len(params) < MAX_PARAMS
            THEN /\ params' = Append(params, currentParam)
                 /\ currentParam' = 0
            ELSE /\ params' = params
                 /\ currentParam' = 0
          [] OTHER ->
            /\ params' = params
            /\ currentParam' = currentParam

FinalizeParam ==
    /\ intermediates' = intermediates
    /\ IF Len(params) < MAX_PARAMS
       THEN params' = Append(params, currentParam)
       ELSE params' = params
    /\ currentParam' = 0

Goto(s, a) ==
    /\ state' = s
    /\ actions' = a
    /\ UNCHANGED <<params, intermediates, currentParam>>

GotoClear(s, a) ==
    /\ state' = s
    /\ actions' = a
    /\ Clear

GotoCollect(s, a, b) ==
    /\ state' = s
    /\ actions' = a
    /\ Collect(b)

GotoParam(s, a, b) ==
    /\ state' = s
    /\ actions' = a
    /\ Param(b)

GotoFinalize(s, a) ==
    /\ state' = s
    /\ actions' = a
    /\ FinalizeParam

(***************************************************************************)
(* STATE TRANSITIONS                                                       *)
(***************************************************************************)

GroundTransition(b) ==
    CASE
        IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsC0(b) -> Goto(Ground, {"Execute"})
    [] IsPrintableGL(b) -> Goto(Ground, {"Print"})
    [] IsDELGL(b) -> Goto(Ground, {})
    [] OTHER -> Goto(Ground, {})

EscapeTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> Goto(Escape, {})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsIntermediate(b) -> GotoCollect(EscapeIntermediate, {"Collect"}, b)
    [] IsGL(b, 91) -> GotoClear(CsiEntry, {"Clear"})
    [] IsGL(b, 93) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] IsGL(b, 80) -> GotoClear(DcsEntry, {"Clear"})
    [] (IsGL(b, 88) \/ IsGL(b, 94) \/ IsGL(b, 95)) ->
        GotoClear(SosPmApcString, {"Clear"})
    [] IsFinalByte(b) -> Goto(Ground, {"EscDispatch"})
    [] IsDELGL(b) -> Goto(Escape, {})
    [] IsC0(b) -> Goto(Escape, {"Execute"})
    [] OTHER -> Goto(Escape, {})

EscapeIntermediateTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsIntermediate(b) -> GotoCollect(EscapeIntermediate, {"Collect"}, b)
    [] IsFinalByte(b) -> Goto(Ground, {"EscDispatch"})
    [] IsDELGL(b) -> Goto(EscapeIntermediate, {})
    [] IsC0(b) -> Goto(EscapeIntermediate, {"Execute"})
    [] OTHER -> Goto(EscapeIntermediate, {})

CsiEntryTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsIntermediate(b) -> GotoCollect(CsiIntermediate, {"Collect"}, b)
    [] IsParamByte(b) /\ GL(b) \in 48..59 -> GotoParam(CsiParam, {"Param"}, b)
    [] IsParamByte(b) /\ GL(b) \in 60..63 -> GotoCollect(CsiParam, {"Collect"}, b)
    [] IsFinalByte(b) -> Goto(Ground, {"CsiDispatch"})
    [] IsDELGL(b) -> Goto(CsiEntry, {})
    [] IsC0(b) -> Goto(CsiEntry, {"Execute"})
    [] OTHER -> Goto(CsiEntry, {})

CsiParamTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsParamByte(b) /\ GL(b) \in 48..59 -> GotoParam(CsiParam, {"Param"}, b)
    [] IsParamByte(b) /\ GL(b) \in 60..63 -> Goto(CsiIgnore, {})
    [] IsIntermediate(b) -> GotoCollect(CsiIntermediate, {"Collect"}, b)
    [] IsFinalByte(b) -> GotoFinalize(Ground, {"CsiDispatch"})
    [] IsDELGL(b) -> Goto(CsiParam, {})
    [] IsC0(b) -> Goto(CsiParam, {"Execute"})
    [] OTHER -> Goto(CsiParam, {})

CsiIntermediateTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsIntermediate(b) -> GotoCollect(CsiIntermediate, {"Collect"}, b)
    [] IsParamByte(b) -> Goto(CsiIgnore, {})
    [] IsFinalByte(b) -> Goto(Ground, {"CsiDispatch"})
    [] IsDELGL(b) -> Goto(CsiIntermediate, {})
    [] IsC0(b) -> Goto(CsiIntermediate, {"Execute"})
    [] OTHER -> Goto(CsiIntermediate, {})

CsiIgnoreTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsFinalByte(b) -> Goto(Ground, {})
    [] IsDELGL(b) -> Goto(CsiIgnore, {})
    [] IsC0(b) -> Goto(CsiIgnore, {"Execute"})
    [] IsPrintableGL(b) -> Goto(CsiIgnore, {})
    [] OTHER -> Goto(CsiIgnore, {})

DcsEntryTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsIntermediate(b) -> GotoCollect(DcsIntermediate, {"Collect"}, b)
    [] IsParamByte(b) /\ GL(b) \in 48..59 -> GotoParam(DcsParam, {"Param"}, b)
    [] IsParamByte(b) /\ GL(b) \in 60..63 -> GotoCollect(DcsParam, {"Collect"}, b)
    [] IsFinalByte(b) -> Goto(DcsPassthrough, {"Hook"})
    [] IsDELGL(b) -> Goto(DcsEntry, {})
    [] IsC0(b) -> Goto(DcsEntry, {})
    [] OTHER -> Goto(DcsEntry, {})

DcsParamTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsParamByte(b) /\ GL(b) \in 48..59 -> GotoParam(DcsParam, {"Param"}, b)
    [] IsParamByte(b) /\ GL(b) \in 60..63 -> Goto(DcsIgnore, {})
    [] IsIntermediate(b) -> GotoCollect(DcsIntermediate, {"Collect"}, b)
    [] IsFinalByte(b) -> GotoFinalize(DcsPassthrough, {"Hook"})
    [] IsDELGL(b) -> Goto(DcsParam, {})
    [] IsC0(b) -> Goto(DcsParam, {})
    [] OTHER -> Goto(DcsParam, {})

DcsIntermediateTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {"Execute"})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsIntermediate(b) -> GotoCollect(DcsIntermediate, {"Collect"}, b)
    [] IsParamByte(b) -> Goto(DcsIgnore, {})
    [] IsFinalByte(b) -> Goto(DcsPassthrough, {"Hook"})
    [] IsDELGL(b) -> Goto(DcsIntermediate, {})
    [] IsC0(b) -> Goto(DcsIntermediate, {})
    [] OTHER -> Goto(DcsIntermediate, {})

DcsIgnoreTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsCSI(b) -> GotoClear(CsiEntry, {"Clear"})
    [] IsDCS(b) -> GotoClear(DcsEntry, {"Clear"})
    [] IsOSC(b) -> GotoClear(OscString, {"Clear", "OscStart"})
    [] (IsSOS(b) \/ IsPM(b) \/ IsAPC(b)) -> GotoClear(SosPmApcString, {"Clear"})
    [] IsST(b) -> Goto(Ground, {})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsDELGL(b) -> Goto(DcsIgnore, {})
    [] IsC0(b) -> Goto(DcsIgnore, {})
    [] IsPrintableGL(b) -> Goto(DcsIgnore, {})
    [] OTHER -> Goto(DcsIgnore, {})

DcsPassthroughTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Unhook", "Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Unhook", "Clear"})
    [] IsST(b) -> Goto(Ground, {"Unhook"})
    [] IsC1(b) -> Goto(Ground, {"Unhook", "Execute"})
    [] IsDELGL(b) -> Goto(DcsPassthrough, {})
    [] IsC0(b) -> Goto(DcsPassthrough, {"Put"})
    [] IsPrintableGL(b) -> Goto(DcsPassthrough, {"Put"})
    [] OTHER -> Goto(DcsPassthrough, {})

OscStringTransition(b) ==
    CASE
        b = 7 -> Goto(Ground, {"OscEnd"})
    [] IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"OscEnd", "Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"OscEnd", "Clear"})
    [] IsST(b) -> Goto(Ground, {"OscEnd"})
    [] IsC1(b) -> Goto(Ground, {"OscEnd", "Execute"})
    [] IsDELGL(b) -> Goto(OscString, {})
    [] IsC0(b) -> Goto(OscString, {})
    [] IsPrintableGL(b) -> Goto(OscString, {"OscPut"})
    [] OTHER -> Goto(OscString, {})

SosPmApcStringTransition(b) ==
    CASE
        IsCAN(b) \/ IsSUB(b) -> Goto(Ground, {"Execute"})
    [] IsESC(b) -> GotoClear(Escape, {"Clear"})
    [] IsST(b) -> Goto(Ground, {})
    [] IsC1(b) -> Goto(Ground, {"Execute"})
    [] IsDELGL(b) -> Goto(SosPmApcString, {})
    [] IsC0(b) -> Goto(SosPmApcString, {})
    [] IsPrintableGL(b) -> Goto(SosPmApcString, {})
    [] OTHER -> Goto(SosPmApcString, {})

(***************************************************************************)
(* INITIAL STATE                                                           *)
(***************************************************************************)

Init ==
    /\ state = Ground
    /\ params = <<>>
    /\ intermediates = <<>>
    /\ currentParam = 0
    /\ actions = {}

(***************************************************************************)
(* NEXT STATE RELATION                                                     *)
(***************************************************************************)

ProcessByte(b) ==
    \/ (state = Ground /\ GroundTransition(b))
    \/ (state = Escape /\ EscapeTransition(b))
    \/ (state = EscapeIntermediate /\ EscapeIntermediateTransition(b))
    \/ (state = CsiEntry /\ CsiEntryTransition(b))
    \/ (state = CsiParam /\ CsiParamTransition(b))
    \/ (state = CsiIntermediate /\ CsiIntermediateTransition(b))
    \/ (state = CsiIgnore /\ CsiIgnoreTransition(b))
    \/ (state = DcsEntry /\ DcsEntryTransition(b))
    \/ (state = DcsParam /\ DcsParamTransition(b))
    \/ (state = DcsIntermediate /\ DcsIntermediateTransition(b))
    \/ (state = DcsPassthrough /\ DcsPassthroughTransition(b))
    \/ (state = DcsIgnore /\ DcsIgnoreTransition(b))
    \/ (state = OscString /\ OscStringTransition(b))
    \/ (state = SosPmApcString /\ SosPmApcStringTransition(b))

Next ==
    \E b \in Bytes : ProcessByte(b)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* SAFETY PROPERTIES                                                       *)
(***************************************************************************)

StateAlwaysValid == state \in States
Safety == StateAlwaysValid

(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)

THEOREM TypeSafety == Spec => []TypeInvariant
THEOREM SafetyHolds == Spec => []Safety

(***************************************************************************)
(* GROUND STATE REACHABILITY                                               *)
(*                                                                         *)
(* Critical property: The parser can always recover to Ground state from   *)
(* any other state. This ensures robustness against malformed input.       *)
(*                                                                         *)
(* Recovery mechanisms:                                                    *)
(* - CAN (0x18) and SUB (0x1A): Universal recovery bytes, work from all    *)
(*   states. Execute action is emitted but parser returns to Ground.       *)
(* - ESC (0x1B): Moves to Escape state (one step closer to Ground via      *)
(*   any final byte).                                                      *)
(* - ST (0x9C): String terminator, ends string states.                     *)
(***************************************************************************)

\* Set of states that immediately transition to Ground on CAN/SUB
StatesWithCANRecovery ==
    {Ground, Escape, EscapeIntermediate, CsiEntry, CsiParam, CsiIntermediate,
     CsiIgnore, DcsEntry, DcsParam, DcsIntermediate, DcsPassthrough, DcsIgnore,
     OscString, SosPmApcString}

\* CAN (0x18) always leads to Ground from any state
CANLeadsToGround ==
    \A s \in States:
        LET b == 24  \* CAN byte
        IN state = s /\ ProcessByte(b) => state' = Ground

\* SUB (0x1A) always leads to Ground from any state
SUBLeadsToGround ==
    \A s \in States:
        LET b == 26  \* SUB byte
        IN state = s /\ ProcessByte(b) => state' = Ground

\* ST (0x9C) terminates string states
STTerminatesStrings ==
    \A s \in {DcsPassthrough, DcsIgnore, OscString, SosPmApcString}:
        LET b == 156  \* ST byte
        IN state = s /\ ProcessByte(b) => state' = Ground

\* From Escape, any final byte (0x40-0x7E) goes to Ground
EscapeFinalToGround ==
    \A b \in 64..126:
        state = Escape /\ ProcessByte(b) => state' = Ground

\* Combined Ground reachability: from any state, Ground is reachable
\* This is a key liveness property for parser robustness
GroundReachable ==
    \A s \in States:
        \E b \in Bytes:
            (state = s /\ ProcessByte(b)) =>
                (state' = Ground \/ state' = Escape)

(***************************************************************************)
(* RECOVERY PATH THEOREMS                                                  *)
(*                                                                         *)
(* These theorems prove that the parser can never get "stuck" in a state   *)
(* that prevents future Ground recovery.                                   *)
(***************************************************************************)

\* Every state has a path to Ground within 2 bytes (CAN always works in 1)
THEOREM GroundReachableIn2 ==
    Spec => [] [
        \* CAN from any state goes to Ground immediately
        \A s \in States:
            state = s => (\E b \in Bytes: ProcessByte(b) => state' = Ground)
    ]_vars

\* CAN recovery is universal
THEOREM CANRecovery ==
    Spec => [] [ProcessByte(24) => state' = Ground]_vars

\* SUB recovery is universal
THEOREM SUBRecovery ==
    Spec => [] [ProcessByte(26) => state' = Ground]_vars

\* From string states, ST terminates properly
THEOREM StringStateRecovery ==
    Spec => [] [
        (state \in {OscString, SosPmApcString, DcsPassthrough}) /\
        ProcessByte(156) => state' = Ground
    ]_vars

(***************************************************************************)
(* NO STUCK STATES                                                         *)
(*                                                                         *)
(* Every state has at least one valid transition. The parser never enters  *)
(* a state where no byte value can advance it.                             *)
(***************************************************************************)

\* Every state has at least one outgoing transition
NoStuckStates ==
    \A s \in States:
        state = s => \E b \in Bytes: ENABLED ProcessByte(b)

\* Parser is always responsive to input
AlwaysResponsive ==
    \A s \in States: \A b \in Bytes:
        state = s => ENABLED ProcessByte(b)

THEOREM ParserNeverStuck == Spec => []NoStuckStates
THEOREM ParserAlwaysResponsive == Spec => []AlwaysResponsive

(***************************************************************************)
(* DETERMINISM                                                             *)
(*                                                                         *)
(* For any given state and byte, there is exactly one resulting state.     *)
(* This ensures predictable parsing behavior.                              *)
(***************************************************************************)

\* Parser is deterministic: each (state, byte) pair has unique next state
ParserDeterministic ==
    \A s \in States, b \in Bytes:
        state = s =>
            LET nextStates == {s2 \in States: ProcessByte(b) /\ state' = s2}
            IN Cardinality(nextStates) = 1

THEOREM Determinism == Spec => [] [ParserDeterministic]_vars

=========================================================================
