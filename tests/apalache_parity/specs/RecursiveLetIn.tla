---- MODULE RecursiveLetIn ----
\* RECURSIVE inside LET/IN blocks (Part of #3828).
\* Tests RECURSIVE declarations scoped within LET.
\* Expected: model check passes with all invariants holding.
EXTENDS Naturals

VARIABLE n

Init == n = 0
Next == IF n < 1 THEN n' = n + 1 ELSE UNCHANGED n

\* RECURSIVE inside LET
FactLet(x) ==
    LET RECURSIVE fact(_)
        fact(m) == IF m <= 1 THEN 1 ELSE m * fact(m - 1)
    IN fact(x)

\* Nested LET with RECURSIVE
SumTo(x) ==
    LET RECURSIVE sum(_)
        sum(m) == IF m = 0 THEN 0 ELSE m + sum(m - 1)
    IN LET result == sum(x)
    IN result

\* RECURSIVE with multi-param inside LET
Power(base, exp) ==
    LET RECURSIVE pow(_, _)
        pow(b, e) == IF e = 0 THEN 1 ELSE b * pow(b, e - 1)
    IN pow(base, exp)

FactOK == FactLet(5) = 120
SumOK == SumTo(10) = 55
PowerOK == Power(2, 8) = 256
Power0OK == Power(5, 0) = 1
====
