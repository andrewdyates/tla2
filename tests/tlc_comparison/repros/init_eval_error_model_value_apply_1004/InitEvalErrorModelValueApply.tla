\* Copyright 2026 Andrew Yates.
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Licensed under the Apache License, Version 2.0

---- MODULE InitEvalErrorModelValueApply ----
\* Repro for #1004: applying a model value as a function during Init enumeration.

EXTENDS TLC, Naturals, Sequences, FiniteSets

VARIABLE x
CONSTANT A

Req == [mask |-> A]

Init == /\ x = 1
        /\ Print("Should report error for applying model value to arg", TRUE)
        /\ Req.mask[1] = 1
        /\ Print("Should never get this far", TRUE)

Next == UNCHANGED x

Inv == x = 1

====
