---- MODULE OptionOps ----
\* Option module operator tests (Part of #3760).
\* Tests Some, None, IsSome, IsNone, OptionGetOrElse, OptionToSet, OptionToSeq.
\* Expected: model check passes with all invariants holding.
EXTENDS Integers, Sequences, Variants

\* Inline Option definitions (avoid EXTENDS Option which needs Apalache module)
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

VARIABLE x
Init == x = 0
Next == IF x < 1 THEN x' = x + 1 ELSE UNCHANGED x

\* Test invariants
SomeOK == IsSome(Some(42))
NotNoneOK == ~IsNone(Some(42))
TagOK == VariantTag(Some(42)) = "Some"
ValueOK == VariantGetUnsafe("Some", Some(42)) = 42
NoneWorks == IsNone(NoneVal)
SetOK == OptionToSet(Some(42)) = {42}
NoneSetOK == OptionToSet(NoneVal) = {}
SeqOK == OptionToSeq(Some(42)) = <<42>>
NoneSeqOK == OptionToSeq(NoneVal) = <<>>
====
