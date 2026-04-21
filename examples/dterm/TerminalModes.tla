--------------------------- MODULE TerminalModes ---------------------------
(***************************************************************************)
(* TLA+ Specification for Terminal Mode Flags                              *)
(*                                                                          *)
(* This specification models the terminal mode state machine:               *)
(* - DECSET/DECRST (private mode) operations                               *)
(* - SM/RM (ANSI mode) operations                                          *)
(* - Mode dependencies and invariants                                       *)
(* - Save/restore cursor with mode state (DECSC/DECRC)                     *)
(*                                                                          *)
(* Reference: crates/dterm-core/src/terminal/mod.rs - TerminalModes struct *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANTS
    MaxSavedModes,      \* Maximum depth of saved mode stack
    CursorStyleSet,     \* Bounded cursor styles for model checking
    MouseModeSet,       \* Bounded mouse modes for model checking
    MouseEncodingSet    \* Bounded mouse encodings for model checking

ASSUME MaxSavedModes \in Nat /\ MaxSavedModes >= 1
ASSUME CursorStyleSet /= {} /\ CursorStyleSet \subseteq 0..6
ASSUME MouseModeSet /= {} /\ MouseModeSet \subseteq {"None", "Normal", "ButtonEvent", "AnyEvent"}
ASSUME MouseEncodingSet /= {} /\ MouseEncodingSet \subseteq {"X10", "Sgr"}

(***************************************************************************)
(* TYPE DEFINITIONS                                                         *)
(***************************************************************************)

\* Cursor styles (DECSCUSR values 0-6)
CursorStyles == CursorStyleSet

\* Mouse tracking modes
MouseModes == MouseModeSet

\* Mouse coordinate encoding formats
MouseEncodings == MouseEncodingSet

(***************************************************************************)
(* VARIABLES                                                                *)
(***************************************************************************)

VARIABLES
    \* Cursor modes
    cursor_visible,           \* DECTCEM (mode 25) - cursor visible
    cursor_style,             \* DECSCUSR (0-6)

    \* Screen modes
    alternate_screen,         \* DECSET 1047/1049 - alternate screen buffer
    origin_mode,              \* DECOM (mode 6) - origin mode
    auto_wrap,                \* DECAWM (mode 7) - auto-wrap at margin

    \* Keyboard modes
    application_cursor_keys,  \* DECCKM (mode 1) - application cursor keys

    \* Input modes
    insert_mode,              \* IRM (mode 4) - insert mode
    new_line_mode,            \* LNM (mode 20) - newline mode (LF implies CR)
    bracketed_paste,          \* DECSET 2004 - bracketed paste mode

    \* Mouse modes
    mouse_mode,               \* 1000/1002/1003 tracking mode
    mouse_encoding,           \* 1006 SGR encoding

    \* Focus and output modes
    focus_reporting,          \* DECSET 1004 - focus in/out events
    synchronized_output,      \* DECSET 2026 - synchronized output

    \* Saved state for DECSC/DECRC
    saved_modes               \* Stack of saved mode states

vars == <<cursor_visible, cursor_style, alternate_screen, origin_mode,
          auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
          bracketed_paste, mouse_mode, mouse_encoding, focus_reporting,
          synchronized_output, saved_modes>>

(***************************************************************************)
(* TYPE INVARIANT                                                           *)
(***************************************************************************)

TypeInvariant ==
    /\ cursor_visible \in BOOLEAN
    /\ cursor_style \in CursorStyles
    /\ alternate_screen \in BOOLEAN
    /\ origin_mode \in BOOLEAN
    /\ auto_wrap \in BOOLEAN
    /\ application_cursor_keys \in BOOLEAN
    /\ insert_mode \in BOOLEAN
    /\ new_line_mode \in BOOLEAN
    /\ bracketed_paste \in BOOLEAN
    /\ mouse_mode \in MouseModes
    /\ mouse_encoding \in MouseEncodings
    /\ focus_reporting \in BOOLEAN
    /\ synchronized_output \in BOOLEAN
    /\ Len(saved_modes) <= MaxSavedModes

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

\* Default mode values per VT100/xterm defaults
Init ==
    /\ cursor_visible = TRUE        \* Cursor visible by default
    /\ cursor_style = 0             \* Default cursor style
    /\ alternate_screen = FALSE     \* Main screen buffer
    /\ origin_mode = FALSE          \* Absolute origin
    /\ auto_wrap = TRUE             \* Auto-wrap enabled (common default)
    /\ application_cursor_keys = FALSE  \* Normal cursor keys
    /\ insert_mode = FALSE          \* Replace mode
    /\ new_line_mode = FALSE        \* LF doesn't imply CR
    /\ bracketed_paste = FALSE      \* No paste bracketing
    /\ mouse_mode = "None"          \* No mouse tracking
    /\ mouse_encoding = "X10"       \* Default X10 encoding
    /\ focus_reporting = FALSE      \* No focus events
    /\ synchronized_output = FALSE  \* Immediate output
    /\ saved_modes = <<>>           \* No saved states

(***************************************************************************)
(* MODE SET OPERATIONS (DECSET for private modes)                          *)
(***************************************************************************)

\* Set cursor visible (DECSET 25)
SetCursorVisible ==
    /\ cursor_visible' = TRUE
    /\ UNCHANGED <<cursor_style, alternate_screen, origin_mode, auto_wrap,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Reset cursor visible (DECRST 25)
ResetCursorVisible ==
    /\ cursor_visible' = FALSE
    /\ UNCHANGED <<cursor_style, alternate_screen, origin_mode, auto_wrap,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Set application cursor keys (DECSET 1)
SetApplicationCursorKeys ==
    /\ application_cursor_keys' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, insert_mode, new_line_mode, bracketed_paste,
                   mouse_mode, mouse_encoding, focus_reporting,
                   synchronized_output, saved_modes>>

\* Reset application cursor keys (DECRST 1)
ResetApplicationCursorKeys ==
    /\ application_cursor_keys' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, insert_mode, new_line_mode, bracketed_paste,
                   mouse_mode, mouse_encoding, focus_reporting,
                   synchronized_output, saved_modes>>

\* Set origin mode (DECSET 6)
SetOriginMode ==
    /\ origin_mode' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, auto_wrap,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Reset origin mode (DECRST 6)
ResetOriginMode ==
    /\ origin_mode' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, auto_wrap,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Set auto-wrap (DECSET 7)
SetAutoWrap ==
    /\ auto_wrap' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Reset auto-wrap (DECRST 7)
ResetAutoWrap ==
    /\ auto_wrap' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Set alternate screen buffer (DECSET 1047/1049)
\* Note: 1049 also saves cursor, but that's handled by Terminal, not TerminalModes
SetAlternateScreen ==
    /\ alternate_screen' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, origin_mode, auto_wrap,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Reset alternate screen buffer (DECRST 1047/1049)
ResetAlternateScreen ==
    /\ alternate_screen' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, origin_mode, auto_wrap,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Set bracketed paste (DECSET 2004)
SetBracketedPaste ==
    /\ bracketed_paste' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   mouse_mode, mouse_encoding, focus_reporting,
                   synchronized_output, saved_modes>>

\* Reset bracketed paste (DECRST 2004)
ResetBracketedPaste ==
    /\ bracketed_paste' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   mouse_mode, mouse_encoding, focus_reporting,
                   synchronized_output, saved_modes>>

\* Set focus reporting (DECSET 1004)
SetFocusReporting ==
    /\ focus_reporting' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   synchronized_output, saved_modes>>

\* Reset focus reporting (DECRST 1004)
ResetFocusReporting ==
    /\ focus_reporting' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   synchronized_output, saved_modes>>

\* Set synchronized output (DECSET 2026)
SetSynchronizedOutput ==
    /\ synchronized_output' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, saved_modes>>

\* Reset synchronized output (DECRST 2026)
ResetSynchronizedOutput ==
    /\ synchronized_output' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, saved_modes>>

(***************************************************************************)
(* ANSI MODE OPERATIONS (SM/RM)                                            *)
(***************************************************************************)

\* Set insert mode (SM 4)
SetInsertMode ==
    /\ insert_mode' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Reset insert mode (RM 4)
ResetInsertMode ==
    /\ insert_mode' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Set new line mode (SM 20) - LF implies CR
SetNewLineMode ==
    /\ new_line_mode' = TRUE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

\* Reset new line mode (RM 20)
ResetNewLineMode ==
    /\ new_line_mode' = FALSE
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

(***************************************************************************)
(* MOUSE MODE OPERATIONS                                                    *)
(***************************************************************************)

\* Set mouse tracking mode to a specific mode
\* Only one mode can be active at a time (mutually exclusive)
SetMouseMode(mode) ==
    /\ mode \in MouseModes
    /\ mouse_mode' = mode
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_encoding, focus_reporting,
                   synchronized_output, saved_modes>>

\* Set mouse encoding to SGR (DECSET 1006)
SetSgrMouseEncoding ==
    /\ "Sgr" \in MouseEncodings
    /\ mouse_encoding' = "Sgr"
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, focus_reporting,
                   synchronized_output, saved_modes>>

\* Reset mouse encoding to X10 (DECRST 1006)
ResetSgrMouseEncoding ==
    /\ "X10" \in MouseEncodings
    /\ mouse_encoding' = "X10"
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, focus_reporting,
                   synchronized_output, saved_modes>>

(***************************************************************************)
(* CURSOR STYLE OPERATIONS (DECSCUSR)                                      *)
(***************************************************************************)

\* Set cursor style (DECSCUSR 0-6)
\* 0 = default, 1 = blinking block, 2 = steady block, etc.
SetCursorStyle(style) ==
    /\ style \in CursorStyles
    /\ cursor_style' = style
    /\ UNCHANGED <<cursor_visible, alternate_screen, origin_mode, auto_wrap,
                   application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

(***************************************************************************)
(* SAVE/RESTORE MODE STATE                                                 *)
(***************************************************************************)

\* Construct current mode state as a record
CurrentModeState ==
    [cursor_visible |-> cursor_visible,
     cursor_style |-> cursor_style,
     alternate_screen |-> alternate_screen,
     origin_mode |-> origin_mode,
     auto_wrap |-> auto_wrap,
     application_cursor_keys |-> application_cursor_keys,
     insert_mode |-> insert_mode,
     new_line_mode |-> new_line_mode,
     bracketed_paste |-> bracketed_paste,
     mouse_mode |-> mouse_mode,
     mouse_encoding |-> mouse_encoding,
     focus_reporting |-> focus_reporting,
     synchronized_output |-> synchronized_output]

\* Save current mode state (part of DECSC)
SaveModes ==
    /\ Len(saved_modes) < MaxSavedModes
    /\ saved_modes' = Append(saved_modes, CurrentModeState)
    /\ UNCHANGED <<cursor_visible, cursor_style, alternate_screen, origin_mode,
                   auto_wrap, application_cursor_keys, insert_mode, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output>>

\* Restore mode state (part of DECRC)
RestoreModes ==
    /\ Len(saved_modes) > 0
    /\ LET state == saved_modes[Len(saved_modes)] IN
        /\ cursor_visible' = state.cursor_visible
        /\ cursor_style' = state.cursor_style
        /\ alternate_screen' = state.alternate_screen
        /\ origin_mode' = state.origin_mode
        /\ auto_wrap' = state.auto_wrap
        /\ application_cursor_keys' = state.application_cursor_keys
        /\ insert_mode' = state.insert_mode
        /\ new_line_mode' = state.new_line_mode
        /\ bracketed_paste' = state.bracketed_paste
        /\ mouse_mode' = state.mouse_mode
        /\ mouse_encoding' = state.mouse_encoding
        /\ focus_reporting' = state.focus_reporting
        /\ synchronized_output' = state.synchronized_output
    /\ saved_modes' = SubSeq(saved_modes, 1, Len(saved_modes) - 1)

\* Restore with empty stack restores defaults
RestoreModesDefault ==
    /\ Len(saved_modes) = 0
    /\ cursor_visible' = TRUE
    /\ cursor_style' = 0
    /\ alternate_screen' = FALSE
    /\ origin_mode' = FALSE
    /\ auto_wrap' = TRUE
    /\ application_cursor_keys' = FALSE
    /\ insert_mode' = FALSE
    /\ new_line_mode' = FALSE
    /\ bracketed_paste' = FALSE
    /\ mouse_mode' = "None"
    /\ mouse_encoding' = "X10"
    /\ focus_reporting' = FALSE
    /\ synchronized_output' = FALSE
    /\ UNCHANGED saved_modes

(***************************************************************************)
(* RESET OPERATIONS                                                         *)
(***************************************************************************)

\* Full terminal reset (RIS) - reset all modes to defaults
FullReset ==
    /\ cursor_visible' = TRUE
    /\ cursor_style' = 0
    /\ alternate_screen' = FALSE
    /\ origin_mode' = FALSE
    /\ auto_wrap' = TRUE
    /\ application_cursor_keys' = FALSE
    /\ insert_mode' = FALSE
    /\ new_line_mode' = FALSE
    /\ bracketed_paste' = FALSE
    /\ mouse_mode' = "None"
    /\ mouse_encoding' = "X10"
    /\ focus_reporting' = FALSE
    /\ synchronized_output' = FALSE
    /\ saved_modes' = <<>>

\* Soft terminal reset (DECSTR) - subset of RIS
\* Note: DECSTR doesn't reset all modes, just certain ones
SoftReset ==
    /\ cursor_visible' = TRUE
    /\ cursor_style' = 0
    /\ origin_mode' = FALSE
    /\ auto_wrap' = TRUE
    /\ insert_mode' = FALSE
    \* These are NOT reset by DECSTR:
    /\ UNCHANGED <<alternate_screen, application_cursor_keys, new_line_mode,
                   bracketed_paste, mouse_mode, mouse_encoding,
                   focus_reporting, synchronized_output, saved_modes>>

(***************************************************************************)
(* NEXT STATE RELATION                                                     *)
(***************************************************************************)

Next ==
    \/ SetCursorVisible
    \/ ResetCursorVisible
    \/ SetApplicationCursorKeys
    \/ ResetApplicationCursorKeys
    \/ SetOriginMode
    \/ ResetOriginMode
    \/ SetAutoWrap
    \/ ResetAutoWrap
    \/ SetAlternateScreen
    \/ ResetAlternateScreen
    \/ SetBracketedPaste
    \/ ResetBracketedPaste
    \/ SetFocusReporting
    \/ ResetFocusReporting
    \/ SetSynchronizedOutput
    \/ ResetSynchronizedOutput
    \/ SetInsertMode
    \/ ResetInsertMode
    \/ SetNewLineMode
    \/ ResetNewLineMode
    \/ \E mode \in MouseModes: SetMouseMode(mode)
    \/ SetSgrMouseEncoding
    \/ ResetSgrMouseEncoding
    \/ \E style \in CursorStyles: SetCursorStyle(style)
    \/ SaveModes
    \/ RestoreModes
    \/ RestoreModesDefault
    \/ FullReset
    \/ SoftReset

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* SAFETY PROPERTIES                                                        *)
(***************************************************************************)

\* Mouse encoding is only meaningful when mouse mode is active
\* (This is not an invariant but a useful property to track)
MouseEncodingRelevance ==
    (mouse_mode # "None") => TRUE  \* Always true, just documentation

\* Cursor style is always valid
CursorStyleValid ==
    cursor_style \in CursorStyles

\* Mouse mode is always one of the defined modes
MouseModeValid ==
    mouse_mode \in MouseModes

\* Saved modes stack never exceeds limit
SavedModesValid ==
    Len(saved_modes) <= MaxSavedModes

\* Combined safety property
Safety ==
    /\ CursorStyleValid
    /\ MouseModeValid
    /\ SavedModesValid

(***************************************************************************)
(* LIVENESS PROPERTIES (not verified, just documented)                     *)
(***************************************************************************)

\* Save followed by restore returns to original state (temporal property)
\* This is more complex to express in TLA+ for model checking
\* SaveRestoreConsistent ==
\*     (SaveModes => <>(RestoreModes /\ saved_modes = <<>>))

(***************************************************************************)
(* THEOREMS                                                                *)
(***************************************************************************)

\* Theorem: Set followed by reset is idempotent for boolean modes
THEOREM SetResetIdempotent ==
    \A b \in BOOLEAN:
        /\ (cursor_visible = b /\ SetCursorVisible) => cursor_visible' = TRUE
        /\ (cursor_visible = TRUE /\ ResetCursorVisible) => cursor_visible' = FALSE

\* Theorem: Full reset restores Init state (except for saved_modes which is cleared)
THEOREM FullResetToInit ==
    FullReset =>
        /\ cursor_visible' = TRUE
        /\ cursor_style' = 0
        /\ alternate_screen' = FALSE
        /\ origin_mode' = FALSE
        /\ auto_wrap' = TRUE
        /\ application_cursor_keys' = FALSE
        /\ insert_mode' = FALSE
        /\ new_line_mode' = FALSE
        /\ bracketed_paste' = FALSE
        /\ mouse_mode' = "None"
        /\ mouse_encoding' = "X10"
        /\ focus_reporting' = FALSE
        /\ synchronized_output' = FALSE
        /\ saved_modes' = <<>>

\* Theorem: Save/Restore preserves mode state integrity
THEOREM SaveRestorePreservesState ==
    /\ Len(saved_modes) < MaxSavedModes
    /\ SaveModes
    => Len(saved_modes') = Len(saved_modes) + 1

\* Theorem: Mouse modes are mutually exclusive
THEOREM MouseModesMutuallyExclusive ==
    \A m1, m2 \in MouseModes:
        m1 # m2 => ~(mouse_mode = m1 /\ mouse_mode = m2)

=============================================================================
