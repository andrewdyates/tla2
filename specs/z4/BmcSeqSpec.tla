--------------------------- MODULE BmcSeqSpec ---------------------------
\* Sequence-valued state variables for BMC compound type testing.
\*
\* Models a log buffer: a sequence that starts empty and grows by
\* appending incrementing values. Tests: Append, Head, Tail, Len.
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Copyright 2026 Dropbox. | Apache 2.0

EXTENDS Integers, Sequences

VARIABLES
    log,    \* Sequence of integers
    next_id \* Next value to append

Init ==
    /\ log = << >>
    /\ next_id = 1

\* Append the next_id to the log
AppendStep ==
    /\ Len(log) < 5
    /\ log' = Append(log, next_id)
    /\ next_id' = next_id + 1

\* Remove the head element
ConsumeStep ==
    /\ Len(log) > 0
    /\ log' = Tail(log)
    /\ UNCHANGED next_id

Next == AppendStep \/ ConsumeStep

\* Invariant: next_id is always positive
NextIdPositive == next_id >= 1

\* Invariant: log length bounded by 5
LogBounded == Len(log) <= 5

\* Invariant: if non-empty, head is positive
HeadPositive == Len(log) > 0 => Head(log) >= 1

=============================================================================
