---- MODULE LetCacheBug277 ----
\* Minimal reproduction for #277 - ZERO_ARG_OP_CACHE stale results
\*
\* This test specifically triggers the recursive enumeration path
\* where LET definitions are stored in local_ops (lazy evaluation)
\* rather than immediately evaluated onto local_stack.
\*
\* The bug: When a LET-bound operator depends on a quantified variable,
\* the dependency may not be recorded correctly, causing stale cache hits.
\*
\* Pattern: \E p \in Processes : Op(p) where Op has LET x == f(p)
\*
\* TLC: Finds 923 distinct states (with Procs = {"p1", "p2"})
\* TLA2: Finds 923 distinct states (PASS - local deps tracked correctly)
\*
\* NOTE: This test passes because local deps ARE tracked. The actual #277 bug
\* requires INSTANCE context - see Disruptor_SPMC spec (9 vs 8496 states).

EXTENDS Integers, Sequences

CONSTANTS Procs

VARIABLES cursors, buffer

Init ==
    /\ cursors = [p \in Procs |-> 0]
    /\ buffer = <<>>

\* Operator with LET that depends on parameter
\* This is the pattern from Disruptor's BeginRead(reader)
Advance(proc) ==
    LET
        next == cursors[proc] + 1    \* 'next' depends on 'proc'
        idx == next % 4              \* 'idx' depends on 'next'
    IN
        /\ cursors[proc] < 3         \* Guard doesn't use LET vars
        /\ next <= 3                 \* Guard DOES use LET var 'next'
        /\ cursors' = [cursors EXCEPT ![proc] = next]
        /\ buffer' = Append(buffer, <<proc, idx>>)

\* Simple action for state space variety
Noop ==
    /\ Len(buffer) < 6
    /\ UNCHANGED cursors
    /\ buffer' = Append(buffer, <<"noop">>)

Next ==
    \/ \E p \in Procs : Advance(p)
    \/ Noop

Spec == Init /\ [][Next]_<<cursors, buffer>>

StateConstraint ==
    /\ \A p \in Procs : cursors[p] <= 3
    /\ Len(buffer) <= 6

\* Invariant
TypeOK ==
    /\ cursors \in [Procs -> 0..3]
    /\ buffer \in Seq(Seq(STRING) \union {<<p, n>> : p \in Procs, n \in 0..3})

====
