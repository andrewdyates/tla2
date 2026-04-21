# dterm TLA+ Specifications

Real-world TLA+ specs from the dterm terminal emulator project.

**Project:** https://github.com/andrewdyates/dterm
**Total specs:** 17
**Total lines:** ~15,000 lines of TLA+

---

## Spec Overview

| Spec | Lines | States | Purpose |
|------|-------|--------|---------|
| Parser.tla | 700 | 443K | VT100/ANSI escape sequence parser state machine |
| Terminal.tla | 600 | 235K | Main terminal state machine |
| Grid.tla | 1200 | 307M | Terminal grid with cursor, scrolling, damage tracking |
| TerminalModes.tla | 700 | 27M | Terminal mode flags (DECCKM, DECAWM, etc.) |
| Scrollback.tla | 700 | 1.8K | Tiered scrollback storage (hot/warm/cold) |
| Selection.tla | 500 | 1.4M | Text selection state machine |
| Animation.tla | 300 | 7.6K | Kitty animation protocol |
| VT52.tla | 400 | 12K | VT52 compatibility mode |
| DoubleWidth.tla | 350 | 551K | Double-width/height character handling |
| Coalesce.tla | 400 | 311K | Input coalescing for performance |
| PagePool.tla | 500 | 562K | Memory page pooling |
| StreamingSearch.tla | 650 | OOM | Incremental search across scrollback |
| AgentApproval.tla | 350 | - | AI agent approval workflow |
| AgentOrchestration.tla | 650 | 10M+ | Multi-agent orchestration |
| MediaServer.tla | 800 | - | Voice I/O (STT/TTS) protocol |
| RenderPipeline.tla | 850 | - | GPU render pipeline |
| UIStateMachine.tla | 450 | - | UI event coordination |

---

## Verification Status

| Status | Count |
|--------|-------|
| Passing | 12 |
| Needs work | 2 (MediaServer, StreamingSearch) |
| Running | 3 (large state space) |

---

## Bugs Found

TLA+ model checking found these real bugs:

1. **Animation.tla** - `SetLoopCount` could be called during playback, causing `current_loop > max_loops`
2. **MediaServer.tla** - Duplicate TTS utterance IDs (clock not incremented in QueueTTS)
3. **VT52.tla** - Type inconsistency comparing strings with tuples

---

## Pain Points Demonstrated

These specs demonstrate several TLA+ pain points:

1. **State explosion** - Grid.tla has 307M states with tiny constants
2. **OOM** - StreamingSearch.tla runs out of memory
3. **Type errors at runtime** - VT52.tla type mismatch only found by TLC
4. **UNCHANGED boilerplate** - Every action needs manual unchanged list
5. **Separate .cfg files** - Configuration separate from spec

These pain points informed the design of TLA2's native features (built-in config, static type checking, implicit UNCHANGED).

---

## Running

```bash
# Install Java
brew install openjdk@21

# Download TLC
curl -L -o tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Run a spec
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -deadlock Parser.tla
```

---

## File Descriptions

### Core Terminal

- `Parser.tla` - VT100/ANSI escape sequence parser (DEC state machine)
- `Terminal.tla` - Main terminal state machine
- `Grid.tla` - 2D grid with cells, cursor, scrolling
- `TerminalModes.tla` - Terminal mode flags
- `Scrollback.tla` - Tiered storage (hot → warm → cold)
- `Selection.tla` - Text selection (simple, block, semantic, line)

### Protocols

- `VT52.tla` - VT52 compatibility mode
- `DoubleWidth.tla` - DECDWL/DECDHL double-width chars
- `Animation.tla` - Kitty animation protocol
- `Coalesce.tla` - Input event coalescing

### Infrastructure

- `PagePool.tla` - Memory page allocation
- `StreamingSearch.tla` - Incremental search
- `RenderPipeline.tla` - GPU rendering

### Agent System

- `AgentApproval.tla` - Approval workflow for AI actions
- `AgentOrchestration.tla` - Multi-agent coordination
- `MediaServer.tla` - Voice I/O (speech-to-text, text-to-speech)
- `UIStateMachine.tla` - UI event coordination
