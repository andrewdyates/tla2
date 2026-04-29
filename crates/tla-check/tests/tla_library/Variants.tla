---------------------------- MODULE Variants ------------------------------------
(*
 * Tagged union (variant) operators for Apalache.
 *
 * A variant is represented as a record [tag |-> "Tag", value |-> val].
 * These operators provide a type-safe way to work with sum types.
 *
 * Reference: https://apalache-mc.org/docs/lang/apalache-operators.html#variants
 *
 * The bodies below are TLC-compatible fallbacks. TLA2 provides native Rust
 * builtin implementations for performance.
 *)

(**
 * Create a tagged union value.
 * @type: (Str, a) => [tag: Str, value: a];
 *)
Variant(__tag, __value) == [tag |-> __tag, value |-> __value]

(**
 * Extract the tag string from a variant.
 * @type: [tag: Str, value: a] => Str;
 *)
VariantTag(__v) == __v.tag

(**
 * Extract the value from a variant. Fails if tag does not match.
 * @type: (Str, [tag: Str, value: a]) => a;
 *)
VariantGetUnsafe(__tag, __v) ==
    IF __v.tag = __tag
    THEN __v.value
    ELSE CHOOSE __x \in {} : TRUE

(**
 * Extract the value from a variant if tag matches, otherwise return default.
 * @type: (Str, [tag: Str, value: a], a) => a;
 *)
VariantGetOrElse(__tag, __v, __default) ==
    IF __v.tag = __tag
    THEN __v.value
    ELSE __default

(**
 * Filter a set of variants by tag.
 * @type: (Str, Set([tag: Str, value: a])) => Set([tag: Str, value: a]);
 *)
VariantFilter(__tag, __S) == { __v \in __S : __v.tag = __tag }

(**
 * The unit value, used as the value component of nullary variant constructors (e.g., None).
 * @type: Str;
 *)
UNIT == "U_OF_UNIT"

================================================================================
