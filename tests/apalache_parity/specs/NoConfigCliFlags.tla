---- MODULE NoConfigCliFlags ----
\* Apalache-style config-free checking: --no-config --init --next --inv.
\* Expected: passes with CLI flags only, no .cfg file needed.
VARIABLE counter
MyInit == counter = 0
MyNext == counter' = IF counter < 2 THEN counter + 1 ELSE counter
TypeOK == counter \in {0, 1, 2}
====
