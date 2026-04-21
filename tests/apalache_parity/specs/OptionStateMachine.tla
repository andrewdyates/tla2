---- MODULE OptionStateMachine ----
\* Option module operators used in a state machine pattern (Part of #3828).
\* Tests Some, NoneVal, IsSome, IsNone, OptionGetOrElse, OptionToSet, OptionToSeq
\* in transitions and invariants.
\* Expected: model check passes with all invariants holding.
EXTENDS Integers, Sequences, Variants, FiniteSets

\* Option definitions
UNIT_VAL == "U_OF_UNIT"
Some(val) == Variant("Some", val)
NoneVal == Variant("None", UNIT_VAL)
IsSome(opt) == VariantTag(opt) = "Some"
IsNone(opt) == VariantTag(opt) = "None"
OptionGetOrElse(opt, default) == VariantGetOrElse("Some", opt, default)
OptionToSeq(opt) ==
    IF IsSome(opt) THEN <<VariantGetUnsafe("Some", opt)>> ELSE <<>>
OptionToSet(opt) ==
    IF IsSome(opt) THEN {VariantGetUnsafe("Some", opt)} ELSE {}

VARIABLE result

Init == result = NoneVal

Next ==
    \/ /\ IsNone(result)
       /\ result' = Some(1)
    \/ /\ IsSome(result)
       /\ LET val == OptionGetOrElse(result, 0)
          IN IF val < 5
             THEN result' = Some(val + 1)
             ELSE result' = NoneVal

\* Invariants
ValidOption == IsSome(result) \/ IsNone(result)
NoneExclusive == IsNone(result) => ~IsSome(result)
SomeExclusive == IsSome(result) => ~IsNone(result)
GetOrElseOK == IsNone(result) => OptionGetOrElse(result, -1) = -1
ToSetOK == IsNone(result) => OptionToSet(result) = {}
ToSeqOK == IsNone(result) => OptionToSeq(result) = <<>>
SomeToSetOK == IsSome(result) =>
    Cardinality(OptionToSet(result)) = 1
SomeToSeqOK == IsSome(result) =>
    Len(OptionToSeq(result)) = 1
ValueBound == IsSome(result) =>
    OptionGetOrElse(result, 0) \in 1..5
====
