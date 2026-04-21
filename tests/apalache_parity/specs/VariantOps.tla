---- MODULE VariantOps ----
\* Apalache Variants module: tagged unions.
\* Expected: model check passes, variant operations correct.
EXTENDS Variants, Naturals
VARIABLE v
Init == v = Variant("Some", 42)
Next == UNCHANGED v
TagOK == VariantTag(v) = "Some"
ValueOK == VariantGetUnsafe("Some", v) = 42
FallbackOK == VariantGetOrElse("None", v, -1) = -1
====
