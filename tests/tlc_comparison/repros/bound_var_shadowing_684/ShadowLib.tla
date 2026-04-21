---- MODULE ShadowLib ----
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\*
\* Regression repro for #684-style bugs: a module can use bound identifiers
\* like a1/a2/v1/v2 even if an extending module declares constants with the
\* same names. TLC accepts this (see Voting/MCVoting); TLA2 must match.

CONSTANTS Acceptor, Value
VARIABLE votes

VotedFor(a, b, v) == <<b, v>> \in votes[a]

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in {0}, v1, v2 \in Value :
        VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)
====

