---- MODULE VariantStateMachine ----
\* Variants used as a state machine with pattern matching (Part of #3828).
\* Tests Variant, VariantTag, VariantGetUnsafe, VariantGetOrElse in transitions.
\* Expected: model check passes with all invariants holding.
EXTENDS Variants, Naturals

VARIABLE msg

\* Model a simple message-passing protocol using variants
MkRequest(id) == Variant("Request", id)
MkResponse(val) == Variant("Response", val)
MkError(code) == Variant("Error", code)

Init == msg = MkRequest(1)

Next ==
    \/ /\ VariantTag(msg) = "Request"
       /\ msg' = MkResponse(VariantGetUnsafe("Request", msg) * 10)
    \/ /\ VariantTag(msg) = "Response"
       /\ LET val == VariantGetUnsafe("Response", msg)
          IN IF val > 50
             THEN msg' = MkError(500)
             ELSE msg' = MkRequest(val + 1)
    \/ /\ VariantTag(msg) = "Error"
       /\ msg' = MkRequest(0)

\* Invariants
ValidTag == VariantTag(msg) \in {"Request", "Response", "Error"}
RequestVal == VariantTag(msg) = "Request" =>
    VariantGetUnsafe("Request", msg) \in 0..100
ResponseVal == VariantTag(msg) = "Response" =>
    VariantGetUnsafe("Response", msg) \in 0..1000
ErrorVal == VariantTag(msg) = "Error" =>
    VariantGetUnsafe("Error", msg) = 500
FallbackOK == VariantGetOrElse("Missing", msg, -1) = -1
====
