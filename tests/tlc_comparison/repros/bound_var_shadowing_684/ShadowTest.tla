---- MODULE ShadowTest ----
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Cross-module shadowing repro: see ShadowLib.tla

EXTENDS ShadowLib, TLC

CONSTANTS a1, a2, v1, v2

MCAcceptor == {a1, a2}
MCValue == {v1, v2}

Init == votes = [a \in Acceptor |-> {}]
Next == \E a \in Acceptor, v \in Value :
          votes' = [votes EXCEPT ![a] = @ \cup {<<0, v>>}]

Inv == OneValuePerBallot
====

