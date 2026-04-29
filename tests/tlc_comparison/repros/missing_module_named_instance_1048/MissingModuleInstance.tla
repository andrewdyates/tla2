---- MODULE MissingModuleInstance ----
(* Copyright 2026 Dropbox. *)
(* Author: Andrew Yates <andrewyates.name@gmail.com> *)
(* Regression test for #1048: missing module via named INSTANCE *)
(* Both TLC and TLA2 should fail at parse/semantic stage *)

VARIABLE x

\* Named instance - TLC accepts this syntax (unlike `INSTANCE M` in expr position)
I == INSTANCE Missing

Init == x = 0
Next == x' = x
====
