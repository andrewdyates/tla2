--------------------------- MODULE MCPDR ---------------------------
\* Model checking wrapper for PDR with a tiny 2-proposition instance.
\*
\* System modeled: a 2-bit monotone counter (bits can be set but not cleared).
\*   States are subsets of {1, 2}:
\*     {} = both FALSE, {1} = p1 TRUE, {2} = p2 TRUE, {1,2} = both TRUE
\*
\*   Init: starts in state {} (all false)
\*   Trans: can set any bit or stay (monotone: bits never clear)
\*     {} -> {}       (stay)
\*     {} -> {1}      (set p1)
\*     {} -> {2}      (set p2)
\*     {1} -> {1}     (stay)
\*     {1} -> {1,2}   (set p2)
\*     {2} -> {2}     (stay)
\*     {2} -> {1,2}   (set p1)
\*     {1,2} -> {1,2} (stay)
\*
\*   Safety: state {1,2} is UNSAFE (both propositions true).
\*           Safe states = {{}, {1}, {2}}
\*
\*   MaxDepth = 4: bounds exploration to 4 frames (sufficient for this instance).
\*
\* Expected result: UNSAFE
\*   PDR should find counterexample: {} -> {1} -> {1,2} (or via {2}).
\*   The status variable will eventually reach "unsafe", showing that
\*   PDR correctly discovers the safety violation.
\*
\*   The model checker explores all possible PDR execution orders.
\*   No invariant should be violated: even though the system is unsafe,
\*   the PDR algorithm's frames maintain their structural properties
\*   throughout execution until it discovers the counterexample.

EXTENDS PDR

MCNumProps == 2

MCInit == {{}}

MCTrans == {
    <<{}, {}>>,
    <<{}, {1}>>,
    <<{}, {2}>>,
    <<{1}, {1}>>,
    <<{1}, {1, 2}>>,
    <<{2}, {2}>>,
    <<{2}, {1, 2}>>,
    <<{1, 2}, {1, 2}>>
}

MCSafety == {{}, {1}, {2}}

MCMaxDepth == 4
=============================================================================
