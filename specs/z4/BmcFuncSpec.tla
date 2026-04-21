--------------------------- MODULE BmcFuncSpec ---------------------------
\* Function-valued state variables for BMC compound type testing.
\*
\* Models a counter array: a function from {1, 2} to integers that
\* increments each element on each step.
\* Tests: function construction, DOMAIN, application, EXCEPT.
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Copyright 2026 Andrew Yates. | Apache 2.0

EXTENDS Integers

VARIABLES counters  \* Function: {1, 2} -> Int

Init == counters = [i \in {1, 2} |-> 0]

\* Increment both counters
Next == counters' = [i \in {1, 2} |-> counters[i] + 1]

\* Invariant: both counters are non-negative
AllNonNeg == \A i \in DOMAIN counters : counters[i] >= 0

\* Invariant: both counters are equal (symmetric init + symmetric step)
AllEqual == counters[1] = counters[2]

\* Invariant that should fail at step 3: all counters < 3
AllSmall == \A i \in {1, 2} : counters[i] < 3

=============================================================================
