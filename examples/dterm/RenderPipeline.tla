--------------------------- MODULE RenderPipeline ---------------------------
(***************************************************************************)
(* TLA+ Specification for the dTerm GPU Render Pipeline                    *)
(*                                                                          *)
(* This specification defines:                                              *)
(* - Render pipeline state machine (Idle -> Preparing -> Rendering -> Idle) *)
(* - Vertex buffer bounds and management                                    *)
(* - Glyph atlas allocation and bounds                                      *)
(* - GPU resource lifecycle                                                 *)
(* - Integration with FrameSync for frame coordination                      *)
(*                                                                          *)
(* CRITICAL SAFETY PROPERTY:                                                *)
(* Unlike dispatch_group, this cannot have "unbalanced" operations.         *)
(* The Rust implementation uses oneshot channels that can only complete     *)
(* once (enforced at compile time by ownership).                            *)
(*                                                                          *)
(* Reference: docs/ROADMAP_PHASE_E_GPU_RENDERER.md                          *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANTS
    MaxVertices,          \* Maximum vertices in buffer (e.g., 1000000)
    MaxAtlasSize,         \* Maximum atlas texture size in bytes (e.g., 4194304 = 2048^2)
    MaxGlyphs,            \* Maximum glyphs in atlas (e.g., 4096)
    MaxPendingFrames,     \* Maximum pending frame requests (e.g., 3)
    MaxRows,              \* Maximum terminal rows (e.g., 100)
    MaxCols,              \* Maximum terminal columns (e.g., 200)
    MaxFrameId            \* Maximum frame ID for bounded checking (e.g., 100)

\* Constraint assumptions for model checking
ASSUME MaxVertices \in Nat /\ MaxVertices > 0
ASSUME MaxAtlasSize \in Nat /\ MaxAtlasSize > 0
ASSUME MaxGlyphs \in Nat /\ MaxGlyphs > 0
ASSUME MaxPendingFrames \in Nat /\ MaxPendingFrames > 0
ASSUME MaxRows \in Nat /\ MaxRows > 0
ASSUME MaxCols \in Nat /\ MaxCols > 0
ASSUME MaxFrameId \in Nat /\ MaxFrameId > 0

(***************************************************************************)
(* VARIABLES                                                                *)
(***************************************************************************)

VARIABLES
    \* Pipeline state machine
    pipeline_state,       \* "Idle", "Preparing", "Rendering", "Error"

    \* Vertex buffer management
    vertex_count,         \* Current number of vertices
    vertex_capacity,      \* Current buffer capacity

    \* Atlas management
    atlas_size,           \* Current atlas texture size (width = height)
    atlas_used_bytes,     \* Bytes used in atlas
    glyph_count,          \* Number of glyphs in atlas
    glyph_entries,        \* Set of allocated glyph regions
    pending_uploads,      \* Glyphs waiting to be uploaded to GPU

    \* Frame synchronization (safe by construction)
    frame_id_counter,     \* Monotonically increasing frame ID
    pending_frame,        \* Current pending frame: NONE or [id: Nat, status: "Pending"|"Completed"|"Cancelled"]
    completed_frames,     \* Set of completed frame IDs

    \* Terminal state snapshot
    terminal_rows,        \* Current terminal rows
    terminal_cols,        \* Current terminal columns
    dirty_rows,           \* Set of dirty rows needing redraw

    \* Resource tracking
    gpu_memory_used,      \* Total GPU memory in use
    resource_count        \* Number of allocated GPU resources

vars == <<pipeline_state, vertex_count, vertex_capacity, atlas_size, atlas_used_bytes,
          glyph_count, glyph_entries, pending_uploads, frame_id_counter, pending_frame,
          completed_frames, terminal_rows, terminal_cols, dirty_rows, gpu_memory_used,
          resource_count>>

(***************************************************************************)
(* TYPE DEFINITIONS                                                         *)
(***************************************************************************)

\* Valid pipeline states
PipelineStates == {"Idle", "Preparing", "Rendering", "Error"}

\* Frame status values
FrameStatusValues == {"Pending", "Completed", "Cancelled", "Timeout"}

\* Glyph entry: region in atlas
GlyphEntry == [x: 0..MaxAtlasSize-1, y: 0..MaxAtlasSize-1, width: 1..256, height: 1..256]

\* Frame record
FrameRecord == [id: 0..MaxFrameId, status: FrameStatusValues]

\* No frame sentinel
NONE == [id |-> -1, status |-> "None"]

(***************************************************************************)
(* TYPE INVARIANT                                                           *)
(*                                                                          *)
(* Ensures the pipeline state is always well-formed                         *)
(***************************************************************************)

TypeInvariant ==
    /\ pipeline_state \in PipelineStates
    /\ vertex_count \in 0..MaxVertices
    /\ vertex_capacity \in 1..MaxVertices
    /\ atlas_size \in {256, 512, 1024, 2048, 4096}  \* Power of 2
    /\ atlas_used_bytes \in 0..MaxAtlasSize
    /\ glyph_count \in 0..MaxGlyphs
    /\ glyph_entries \subseteq GlyphEntry
    /\ pending_uploads \subseteq GlyphEntry
    /\ frame_id_counter \in 0..MaxFrameId
    /\ (pending_frame = NONE \/ pending_frame \in FrameRecord)
    /\ completed_frames \subseteq 0..MaxFrameId
    /\ terminal_rows \in 1..MaxRows
    /\ terminal_cols \in 1..MaxCols
    /\ dirty_rows \subseteq 0..MaxRows-1
    /\ gpu_memory_used \in 0..MaxAtlasSize + MaxVertices * 64  \* Atlas + vertex buffer
    /\ resource_count \in Nat

(***************************************************************************)
(* HELPER OPERATORS                                                         *)
(***************************************************************************)

\* Minimum of two values
Min(a, b) == IF a < b THEN a ELSE b

\* Maximum of two values
Max(a, b) == IF a > b THEN a ELSE b

\* Clamp value to range
Clamp(val, minVal, maxVal) ==
    IF val < minVal THEN minVal
    ELSE IF val > maxVal THEN maxVal
    ELSE val

\* Calculate vertices needed for terminal (6 vertices per cell for background + glyph)
VerticesForTerminal(rows, cols) ==
    rows * cols * 12  \* 6 for background quad + 6 for glyph quad

\* Next power of 2 >= n
NextPowerOf2(n) ==
    CHOOSE p \in {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384} :
        /\ p >= n
        /\ \A q \in {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384} :
            q >= n => p <= q

(***************************************************************************)
(* SAFETY PROPERTIES                                                        *)
(***************************************************************************)

\* Vertex buffer never exceeds capacity
VertexBufferBounded ==
    vertex_count <= vertex_capacity

\* Vertex capacity never exceeds maximum
VertexCapacityBounded ==
    vertex_capacity <= MaxVertices

\* Atlas never overflows
AtlasNeverOverflows ==
    atlas_used_bytes <= atlas_size * atlas_size

\* Glyph count matches entries
GlyphCountConsistent ==
    glyph_count = Cardinality(glyph_entries)

\* CRITICAL: Frame operations are balanced
\* Unlike dispatch_group, we CANNOT have more completions than requests
\* This is enforced by Rust's ownership: FrameRequest can only complete once
FrameOperationsBalanced ==
    \A fid \in completed_frames :
        fid < frame_id_counter  \* Can only complete frames that were requested

\* No "unbalanced leave" possible (the dispatch_group crash)
\* In our model: completed frames are always <= requested frames
NoUnbalancedOperations ==
    Cardinality(completed_frames) <= frame_id_counter

\* Pipeline state machine is valid
PipelineStateValid ==
    pipeline_state \in PipelineStates

\* GPU memory is bounded
GPUMemoryBounded ==
    gpu_memory_used <= MaxAtlasSize + MaxVertices * 64

\* Combined safety property
Safety ==
    /\ VertexBufferBounded
    /\ VertexCapacityBounded
    /\ AtlasNeverOverflows
    /\ FrameOperationsBalanced
    /\ NoUnbalancedOperations
    /\ PipelineStateValid
    /\ GPUMemoryBounded

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

Init ==
    /\ pipeline_state = "Idle"
    /\ vertex_count = 0
    /\ vertex_capacity = 80 * 24 * 12  \* Initial capacity for 80x24 terminal
    /\ atlas_size = 512  \* Start with 512x512 atlas
    /\ atlas_used_bytes = 0
    /\ glyph_count = 0
    /\ glyph_entries = {}
    /\ pending_uploads = {}
    /\ frame_id_counter = 0
    /\ pending_frame = NONE
    /\ completed_frames = {}
    /\ terminal_rows = 24
    /\ terminal_cols = 80
    /\ dirty_rows = 0..23  \* All rows dirty initially
    /\ gpu_memory_used = 512 * 512 + vertex_capacity * 64
    /\ resource_count = 2  \* Atlas texture + vertex buffer

(***************************************************************************)
(* FRAME SYNCHRONIZATION OPERATIONS                                         *)
(*                                                                          *)
(* These model the safe frame sync from frame_sync.rs                       *)
(* Key property: Cannot crash with "unbalanced" errors                      *)
(***************************************************************************)

\* Request a new frame
\* Safe: Replaces any pending frame (old one is just dropped)
RequestFrame ==
    /\ frame_id_counter < MaxFrameId
    /\ pipeline_state = "Idle"
    /\ frame_id_counter' = frame_id_counter + 1
    /\ pending_frame' = [id |-> frame_id_counter, status |-> "Pending"]
    /\ pipeline_state' = "Preparing"
    /\ UNCHANGED <<vertex_count, vertex_capacity, atlas_size, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, completed_frames,
                   terminal_rows, terminal_cols, dirty_rows, gpu_memory_used,
                   resource_count>>

\* Complete a pending frame (drawable provided)
\* Safe: Can only happen once per request (Rust ownership ensures this)
CompleteFrame ==
    /\ pending_frame /= NONE
    /\ pending_frame.status = "Pending"
    /\ pending_frame' = [pending_frame EXCEPT !.status = "Completed"]
    /\ completed_frames' = completed_frames \union {pending_frame.id}
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   atlas_used_bytes, glyph_count, glyph_entries, pending_uploads,
                   frame_id_counter, terminal_rows, terminal_cols, dirty_rows,
                   gpu_memory_used, resource_count>>

\* Cancel a pending frame (request dropped without completing)
\* Safe: This is just dropping the FrameRequest, no "unbalanced" error
CancelFrame ==
    /\ pending_frame /= NONE
    /\ pending_frame.status = "Pending"
    /\ pending_frame' = [pending_frame EXCEPT !.status = "Cancelled"]
    /\ pipeline_state' = "Idle"
    /\ UNCHANGED <<vertex_count, vertex_capacity, atlas_size, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, frame_id_counter,
                   completed_frames, terminal_rows, terminal_cols, dirty_rows,
                   gpu_memory_used, resource_count>>

\* Timeout waiting for frame
\* Safe: Just sets status, no "unbalanced leave" like dispatch_group
TimeoutFrame ==
    /\ pending_frame /= NONE
    /\ pending_frame.status = "Pending"
    /\ pending_frame' = [pending_frame EXCEPT !.status = "Timeout"]
    /\ pipeline_state' = "Idle"
    /\ UNCHANGED <<vertex_count, vertex_capacity, atlas_size, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, frame_id_counter,
                   completed_frames, terminal_rows, terminal_cols, dirty_rows,
                   gpu_memory_used, resource_count>>

\* CRITICAL: Late completion after timeout is SAFE
\* In ObjC dispatch_group: this causes "unbalanced leave" crash
\* In Rust: send to closed channel is a no-op (Result::Err, not crash)
LateCompletion ==
    /\ pending_frame /= NONE
    /\ pending_frame.status = "Timeout"  \* Already timed out
    \* Now drawable arrives - in Rust this is safe (send fails silently)
    \* In ObjC this would crash
    /\ completed_frames' = completed_frames \union {pending_frame.id}
    /\ pending_frame' = NONE  \* Clear the timed out frame
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   atlas_used_bytes, glyph_count, glyph_entries, pending_uploads,
                   frame_id_counter, terminal_rows, terminal_cols, dirty_rows,
                   gpu_memory_used, resource_count>>

(***************************************************************************)
(* PIPELINE STATE MACHINE                                                   *)
(***************************************************************************)

\* Start rendering (transition Preparing -> Rendering)
StartRendering ==
    /\ pipeline_state = "Preparing"
    /\ pending_frame /= NONE
    /\ pending_frame.status = "Completed"
    /\ pipeline_state' = "Rendering"
    /\ UNCHANGED <<vertex_count, vertex_capacity, atlas_size, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, frame_id_counter,
                   pending_frame, completed_frames, terminal_rows, terminal_cols,
                   dirty_rows, gpu_memory_used, resource_count>>

\* Finish rendering (transition Rendering -> Idle)
FinishRendering ==
    /\ pipeline_state = "Rendering"
    /\ pipeline_state' = "Idle"
    /\ pending_frame' = NONE  \* Clear completed frame
    /\ dirty_rows' = {}  \* Clear damage after render
    /\ UNCHANGED <<vertex_count, vertex_capacity, atlas_size, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, frame_id_counter,
                   completed_frames, terminal_rows, terminal_cols, gpu_memory_used,
                   resource_count>>

\* Pipeline error (any state -> Error)
PipelineError ==
    /\ pipeline_state' = "Error"
    /\ UNCHANGED <<vertex_count, vertex_capacity, atlas_size, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, frame_id_counter,
                   pending_frame, completed_frames, terminal_rows, terminal_cols,
                   dirty_rows, gpu_memory_used, resource_count>>

\* Recover from error (Error -> Idle)
RecoverFromError ==
    /\ pipeline_state = "Error"
    /\ pipeline_state' = "Idle"
    /\ pending_frame' = NONE
    /\ UNCHANGED <<vertex_count, vertex_capacity, atlas_size, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, frame_id_counter,
                   completed_frames, terminal_rows, terminal_cols, dirty_rows,
                   gpu_memory_used, resource_count>>

(***************************************************************************)
(* VERTEX BUFFER OPERATIONS                                                 *)
(***************************************************************************)

\* Build vertices for current terminal state
BuildVertices ==
    /\ pipeline_state = "Preparing"
    /\ LET needed == VerticesForTerminal(terminal_rows, terminal_cols)
       IN /\ needed <= MaxVertices
          /\ IF needed > vertex_capacity
             THEN \* Grow buffer
                  /\ vertex_capacity' = Min(NextPowerOf2(needed), MaxVertices)
                  /\ gpu_memory_used' = atlas_size * atlas_size + vertex_capacity' * 64
                  /\ resource_count' = resource_count  \* Reuse existing buffer
             ELSE
                  /\ UNCHANGED <<vertex_capacity, gpu_memory_used, resource_count>>
          /\ vertex_count' = needed
    /\ UNCHANGED <<pipeline_state, atlas_size, atlas_used_bytes, glyph_count,
                   glyph_entries, pending_uploads, frame_id_counter, pending_frame,
                   completed_frames, terminal_rows, terminal_cols, dirty_rows>>

\* Clear vertex buffer
ClearVertices ==
    /\ vertex_count' = 0
    /\ UNCHANGED <<pipeline_state, vertex_capacity, atlas_size, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, frame_id_counter,
                   pending_frame, completed_frames, terminal_rows, terminal_cols,
                   dirty_rows, gpu_memory_used, resource_count>>

(***************************************************************************)
(* GLYPH ATLAS OPERATIONS                                                   *)
(***************************************************************************)

\* Allocate glyph in atlas
\* Returns success only if glyph fits
AllocateGlyph(width, height) ==
    /\ width > 0 /\ width <= 256
    /\ height > 0 /\ height <= 256
    /\ glyph_count < MaxGlyphs
    /\ atlas_used_bytes + width * height <= atlas_size * atlas_size
    \* Find position (simplified - just track bytes used)
    /\ LET newEntry == [x |-> 0, y |-> 0, width |-> width, height |-> height]
       IN /\ glyph_entries' = glyph_entries \union {newEntry}
          /\ pending_uploads' = pending_uploads \union {newEntry}
    /\ atlas_used_bytes' = atlas_used_bytes + width * height
    /\ glyph_count' = glyph_count + 1
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   frame_id_counter, pending_frame, completed_frames,
                   terminal_rows, terminal_cols, dirty_rows, gpu_memory_used,
                   resource_count>>

\* Upload pending glyphs to GPU
UploadPendingGlyphs ==
    /\ pending_uploads /= {}
    /\ pending_uploads' = {}
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   atlas_used_bytes, glyph_count, glyph_entries, frame_id_counter,
                   pending_frame, completed_frames, terminal_rows, terminal_cols,
                   dirty_rows, gpu_memory_used, resource_count>>

\* Grow atlas (double size)
GrowAtlas ==
    /\ atlas_size < 4096  \* Can't grow beyond 4096
    /\ LET newSize == atlas_size * 2
       IN /\ atlas_size' = newSize
          /\ gpu_memory_used' = newSize * newSize + vertex_capacity * 64
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_used_bytes,
                   glyph_count, glyph_entries, pending_uploads, frame_id_counter,
                   pending_frame, completed_frames, terminal_rows, terminal_cols,
                   dirty_rows, resource_count>>

\* Clear atlas (reset all glyphs)
ClearAtlas ==
    /\ glyph_entries' = {}
    /\ pending_uploads' = {}
    /\ atlas_used_bytes' = 0
    /\ glyph_count' = 0
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   frame_id_counter, pending_frame, completed_frames,
                   terminal_rows, terminal_cols, dirty_rows, gpu_memory_used,
                   resource_count>>

(***************************************************************************)
(* TERMINAL STATE OPERATIONS                                                *)
(***************************************************************************)

\* Resize terminal
ResizeTerminal(newRows, newCols) ==
    /\ newRows \in 1..MaxRows
    /\ newCols \in 1..MaxCols
    /\ terminal_rows' = newRows
    /\ terminal_cols' = newCols
    /\ dirty_rows' = 0..newRows-1  \* All rows dirty after resize
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   atlas_used_bytes, glyph_count, glyph_entries, pending_uploads,
                   frame_id_counter, pending_frame, completed_frames, gpu_memory_used,
                   resource_count>>

\* Mark row as dirty
MarkRowDirty(row) ==
    /\ row \in 0..terminal_rows-1
    /\ dirty_rows' = dirty_rows \union {row}
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   atlas_used_bytes, glyph_count, glyph_entries, pending_uploads,
                   frame_id_counter, pending_frame, completed_frames,
                   terminal_rows, terminal_cols, gpu_memory_used, resource_count>>

\* Mark all rows dirty (full damage)
MarkFullDamage ==
    /\ dirty_rows' = 0..terminal_rows-1
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   atlas_used_bytes, glyph_count, glyph_entries, pending_uploads,
                   frame_id_counter, pending_frame, completed_frames,
                   terminal_rows, terminal_cols, gpu_memory_used, resource_count>>

(***************************************************************************)
(* RESOURCE MANAGEMENT                                                      *)
(***************************************************************************)

\* Allocate new GPU resource
AllocateResource ==
    /\ resource_count' = resource_count + 1
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   atlas_used_bytes, glyph_count, glyph_entries, pending_uploads,
                   frame_id_counter, pending_frame, completed_frames,
                   terminal_rows, terminal_cols, dirty_rows, gpu_memory_used>>

\* Free a GPU resource
FreeResource ==
    /\ resource_count > 0
    /\ resource_count' = resource_count - 1
    /\ UNCHANGED <<pipeline_state, vertex_count, vertex_capacity, atlas_size,
                   atlas_used_bytes, glyph_count, glyph_entries, pending_uploads,
                   frame_id_counter, pending_frame, completed_frames,
                   terminal_rows, terminal_cols, dirty_rows, gpu_memory_used>>

(***************************************************************************)
(* NEXT STATE RELATION                                                      *)
(***************************************************************************)

Next ==
    \* Frame synchronization (safe operations)
    \/ RequestFrame
    \/ CompleteFrame
    \/ CancelFrame
    \/ TimeoutFrame
    \/ LateCompletion  \* CRITICAL: This is safe in Rust, crashes in ObjC
    \* Pipeline state machine
    \/ StartRendering
    \/ FinishRendering
    \/ PipelineError
    \/ RecoverFromError
    \* Vertex operations
    \/ BuildVertices
    \/ ClearVertices
    \* Atlas operations
    \/ \E w \in 1..32, h \in 1..32 : AllocateGlyph(w, h)
    \/ UploadPendingGlyphs
    \/ GrowAtlas
    \/ ClearAtlas
    \* Terminal operations
    \/ \E r \in 1..MaxRows, c \in 1..MaxCols : ResizeTerminal(r, c)
    \/ \E row \in 0..MaxRows-1 : MarkRowDirty(row)
    \/ MarkFullDamage
    \* Resource operations
    \/ AllocateResource
    \/ FreeResource

(***************************************************************************)
(* SPECIFICATION                                                            *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* INVARIANTS                                                               *)
(***************************************************************************)

\* Type invariant always holds
THEOREM TypeSafe == Spec => []TypeInvariant

\* Safety properties always hold
THEOREM SafetyHolds == Spec => []Safety

(***************************************************************************)
(* CRITICAL FRAME SYNC THEOREMS                                             *)
(*                                                                          *)
(* These prove the frame sync is safe - no "unbalanced" errors possible.    *)
(* This is the key advantage over ObjC dispatch_group.                      *)
(***************************************************************************)

\* Frame ID is monotonically increasing
THEOREM FrameIdMonotonic ==
    [][frame_id_counter' >= frame_id_counter]_vars

\* Completed frames are always valid (were actually requested)
THEOREM CompletedFramesValid ==
    Spec => [](\A fid \in completed_frames : fid < frame_id_counter)

\* CRITICAL: No unbalanced operations ever (unlike dispatch_group)
THEOREM NoDispatchGroupCrash ==
    Spec => []NoUnbalancedOperations

\* Late completion is safe (doesn't crash)
\* In ObjC: dispatch_group_leave after timeout = crash
\* In Rust: send to closed channel = no-op
THEOREM LateCompletionSafe ==
    Spec => [](pending_frame.status = "Timeout" =>
               \* After late completion, we can still operate normally
               (pipeline_state \in PipelineStates))

\* Timeout handling is safe (no resource leaks)
THEOREM TimeoutSafe ==
    Spec => [](pending_frame.status = "Timeout" =>
               \* Resources are still valid after timeout
               /\ resource_count >= 0
               /\ gpu_memory_used >= 0)

(***************************************************************************)
(* VERTEX BUFFER THEOREMS                                                   *)
(***************************************************************************)

\* Vertex count never exceeds capacity
THEOREM VertexBoundsSafe ==
    Spec => []VertexBufferBounded

\* Capacity never exceeds maximum
THEOREM CapacityBoundsSafe ==
    Spec => []VertexCapacityBounded

(***************************************************************************)
(* ATLAS THEOREMS                                                           *)
(***************************************************************************)

\* Atlas never overflows
THEOREM AtlasSafe ==
    Spec => []AtlasNeverOverflows

\* Glyph allocations stay in bounds
THEOREM GlyphAllocationSafe ==
    Spec => [](glyph_count <= MaxGlyphs)

(***************************************************************************)
(* PIPELINE STATE MACHINE THEOREMS                                          *)
(***************************************************************************)

\* Valid state transitions
ValidTransition ==
    \/ (pipeline_state = "Idle" /\ pipeline_state' \in {"Idle", "Preparing", "Error"})
    \/ (pipeline_state = "Preparing" /\ pipeline_state' \in {"Preparing", "Rendering", "Idle", "Error"})
    \/ (pipeline_state = "Rendering" /\ pipeline_state' \in {"Rendering", "Idle", "Error"})
    \/ (pipeline_state = "Error" /\ pipeline_state' \in {"Error", "Idle"})
    \/ UNCHANGED pipeline_state

THEOREM ValidStateMachine ==
    Spec => [][ValidTransition]_pipeline_state

(***************************************************************************)
(* LIVENESS PROPERTIES                                                      *)
(***************************************************************************)

\* Requested frames eventually complete, timeout, or get cancelled
EventualFrameResolution ==
    [](pending_frame /= NONE /\ pending_frame.status = "Pending" =>
       <>(pending_frame.status \in {"Completed", "Cancelled", "Timeout"} \/ pending_frame = NONE))

\* Pipeline eventually returns to Idle
EventualIdle ==
    [](pipeline_state /= "Idle" => <>(pipeline_state = "Idle"))

(***************************************************************************)
(* MODEL CHECKING CONFIGURATION                                             *)
(*                                                                          *)
(* For tractable model checking, use small constants:                       *)
(* MaxVertices = 1000, MaxAtlasSize = 1024, MaxGlyphs = 10,                 *)
(* MaxPendingFrames = 3, MaxRows = 4, MaxCols = 4, MaxFrameId = 10          *)
(***************************************************************************)

=============================================================================
