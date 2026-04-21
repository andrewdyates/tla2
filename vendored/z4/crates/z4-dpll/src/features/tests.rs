// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_infer_pure_uf() {
    let features = StaticFeatures::default();
    assert_eq!(features.infer_logic(), "QF_UF");
}

#[test]
fn test_infer_bv() {
    let features = StaticFeatures {
        has_bv: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_BV");
}

#[test]
fn test_infer_aufbv() {
    let features = StaticFeatures {
        has_bv: true,
        has_arrays: true,
        has_uf: true,
        num_theories: 2,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_AUFBV");
}

#[test]
fn test_infer_lia_with_quantifiers() {
    let features = StaticFeatures {
        has_int: true,
        has_quantifiers: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "LIA");
}

#[test]
fn test_infer_qf_uflia() {
    let features = StaticFeatures {
        has_int: true,
        has_uf: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_UFLIA");
}

#[test]
fn test_infer_qf_nia() {
    // Non-linear Int without UF should route to QF_NIA
    let features = StaticFeatures {
        has_int: true,
        has_nonlinear_int: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_NIA");
}

#[test]
fn test_infer_qf_nra() {
    // Non-linear Real without UF should route to QF_NRA
    let features = StaticFeatures {
        has_real: true,
        has_nonlinear_real: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_NRA");
}

#[test]
fn test_infer_nonlinear_int_with_uf() {
    // Non-linear Int with UF preserves UF information (#5984)
    let features = StaticFeatures {
        has_int: true,
        has_nonlinear_int: true,
        has_uf: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_UFNIA");
}

#[test]
fn test_infer_quantified_nia() {
    // Quantified non-linear Int should route to NIA
    let features = StaticFeatures {
        has_int: true,
        has_nonlinear_int: true,
        has_quantifiers: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "NIA");
}

#[test]
fn test_infer_quantified_nra() {
    // Quantified non-linear Real should route to NRA
    let features = StaticFeatures {
        has_real: true,
        has_nonlinear_real: true,
        has_quantifiers: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "NRA");
}

#[test]
fn test_linear_int_stays_lia() {
    // Linear Int (no nonlinear flag) should stay QF_LIA
    let features = StaticFeatures {
        has_int: true,
        has_nonlinear_int: false,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_LIA");
}

/// Pure strings (no arithmetic) infers QF_S.
#[test]
fn test_infer_pure_strings_routes_to_qf_s() {
    let features = StaticFeatures {
        has_strings: true,
        num_theories: 1,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_S");
}

/// Strings with Int arithmetic infers QF_SLIA.
#[test]
fn test_infer_strings_with_int_routes_to_qf_slia() {
    let features = StaticFeatures {
        has_strings: true,
        has_int: true,
        num_theories: 2,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_SLIA");
}

/// Strings with non-linear Int arithmetic infers QF_SNIA.
#[test]
fn test_infer_strings_with_nonlinear_int_routes_to_qf_snia() {
    let features = StaticFeatures {
        has_strings: true,
        has_int: true,
        has_nonlinear_int: true,
        num_theories: 2,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_SNIA");
}

/// Strings + Arrays + Int routes to AUFLIA, not SLIA (#6724).
/// Array axioms (ROW1/ROW2) are critical for soundness; string constraints
/// degrade to uninterpreted (incomplete but sound).
#[test]
fn test_infer_strings_arrays_int_routes_to_auflia_not_slia() {
    let features = StaticFeatures {
        has_strings: true,
        has_arrays: true,
        has_int: true,
        num_theories: 3,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_AUFLIA");
}

/// Strings + Arrays + Real routes to AUFLRA (#6724).
#[test]
fn test_infer_strings_arrays_real_routes_to_auflra() {
    let features = StaticFeatures {
        has_strings: true,
        has_arrays: true,
        has_real: true,
        num_theories: 3,
        ..Default::default()
    };
    assert_eq!(features.infer_logic(), "QF_AUFLRA");
}

/// is_builtin_symbol recognizes standard string operator names.
#[test]
fn test_is_builtin_symbol_recognizes_string_ops() {
    use z4_core::term::Symbol;
    let string_ops = [
        "str.++",
        "str.len",
        "str.contains",
        "str.prefixof",
        "str.suffixof",
        "str.at",
        "str.substr",
        "str.indexof",
        "str.replace",
        "str.replace_all",
        "str.replace_re",
        "str.replace_re_all",
        "str.to_int",
        "str.to.int",
        "int.to.str",
        "str.from_int",
        "str.to_code",
        "str.from_code",
        "str.to_lower",
        "str.to_upper",
        "str.is_digit",
        "str.<",
        "str.<=",
    ];
    for op in &string_ops {
        assert!(
            is_builtin_symbol(&Symbol::named(*op)),
            "{op} should be recognized as a built-in symbol"
        );
    }
}

#[test]
fn test_is_builtin_symbol_recognizes_regex_ops() {
    use z4_core::term::Symbol;
    let regex_ops = [
        "str.to_re",
        "str.to.re",
        "str.in_re",
        "str.in.re",
        "re.++",
        "re.union",
        "re.inter",
        "re.*",
        "re.+",
        "re.opt",
        "re.range",
        "re.comp",
        "re.diff",
        "re.none",
        "re.all",
        "re.allchar",
    ];
    for op in &regex_ops {
        assert!(
            is_builtin_symbol(&Symbol::named(*op)),
            "{op} should be recognized as a built-in symbol"
        );
    }
}

#[test]
fn test_collect_str_to_code_not_uf() {
    use z4_core::term::Symbol;

    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let code = terms.mk_app(Symbol::named("str.to_code"), vec![a], Sort::Int);
    let codepoint = terms.mk_int(97_i64.into());
    let eq = terms.mk_app(Symbol::named("="), vec![code, codepoint], Sort::Bool);

    let features = StaticFeatures::collect(&terms, &[eq]);
    assert!(features.has_strings, "str.to_code should set has_strings");
    assert!(features.has_int, "str.to_code result sort is Int");
    assert!(!features.has_uf, "str.to_code must not be classified as UF");
}

#[test]
fn test_collect_detects_regex_terms() {
    use z4_core::term::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let to_re = terms.mk_app(Symbol::named("str.to_re"), vec![a], Sort::RegLan);
    let star = terms.mk_app(Symbol::named("re.*"), vec![to_re], Sort::RegLan);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, star], Sort::Bool);

    let features = StaticFeatures::collect(&terms, &[in_re]);
    assert!(features.has_regex, "regex operators should set has_regex");
    assert!(
        features.has_strings,
        "regex terms should imply strings theory"
    );
    assert_eq!(features.infer_logic(), "QF_S");
}

/// Cross-theory conversion symbols (bv2nat, int2bv, to_real, etc.)
/// must be recognized as builtins, not classified as UF (#5503).
#[test]
fn test_is_builtin_symbol_recognizes_cross_theory_conversions() {
    use z4_core::term::Symbol;
    let conversion_ops = [
        "bv2nat",
        "int2bv",
        "to_real",
        "to_int",
        "is_int",
        "bvcomp",
        "const-array",
    ];
    for op in &conversion_ops {
        assert!(
            is_builtin_symbol(&Symbol::named(*op)),
            "{op} should be recognized as a built-in symbol"
        );
    }
}

/// bv2nat term should set has_bv AND has_int, not has_uf (#5503).
#[test]
fn test_collect_bv2nat_not_uf() {
    use z4_core::term::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let bv2nat = terms.mk_app(Symbol::named("bv2nat"), vec![x], Sort::Int);
    let five = terms.mk_int(5_i64.into());
    let gt = terms.mk_app(Symbol::named(">"), vec![bv2nat, five], Sort::Bool);

    let features = StaticFeatures::collect(&terms, &[gt]);
    assert!(features.has_bv, "bv2nat arg should set has_bv");
    assert!(
        features.has_int,
        "bv2nat result sort Int should set has_int"
    );
    assert!(!features.has_uf, "bv2nat must not be classified as UF");
}

/// BV+Int formula (via bv2nat) must route to _BV_LIA, not QF_BV (#5503).
#[test]
fn test_infer_logic_bv_int_routes_to_bv_lia() {
    use z4_core::term::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let bv2nat = terms.mk_app(Symbol::named("bv2nat"), vec![x], Sort::Int);
    let five = terms.mk_int(5_i64.into());
    let gt = terms.mk_app(Symbol::named(">"), vec![bv2nat, five], Sort::Bool);

    let features = StaticFeatures::collect(&terms, &[gt]);
    assert_eq!(
        features.infer_logic(),
        "_BV_LIA",
        "BV+Int formula must route to _BV_LIA, not QF_BV"
    );
}

/// BV+FP formula must route to QF_BVFP, not QF_BV.
///
/// Without this fix, auto-detection for BV+FP silently drops FP
/// constraints and routes to QF_BV (false-SAT risk).
#[test]
fn test_infer_logic_bv_fp_routes_to_bvfp() {
    let features = StaticFeatures {
        has_bv: true,
        has_fpa: true,
        num_theories: 2,
        ..Default::default()
    };
    assert_eq!(
        features.infer_logic(),
        "QF_BVFP",
        "BV+FP formula must route to QF_BVFP, not QF_BV"
    );
}

/// FP + Int formula must route to QF_FP (not silently drop FP).
#[test]
fn test_infer_logic_fp_int_routes_to_fp() {
    let features = StaticFeatures {
        has_fpa: true,
        has_int: true,
        num_theories: 2,
        ..Default::default()
    };
    assert_eq!(
        features.infer_logic(),
        "QF_FP",
        "FP+Int formula must route to QF_FP, not QF_LIA"
    );
}

/// FP + Real formula must route to QF_FP.
#[test]
fn test_infer_logic_fp_real_routes_to_fp() {
    let features = StaticFeatures {
        has_fpa: true,
        has_real: true,
        num_theories: 2,
        ..Default::default()
    };
    assert_eq!(
        features.infer_logic(),
        "QF_FP",
        "FP+Real formula must route to QF_FP"
    );
}

/// #6077 Bug 3: UF + Int + Real must route to QF_AUFLIRA, not QF_UFLRA.
///
/// Before the fix, the UF branch checked has_real first and returned
/// QF_UFLRA, silently dropping integer constraints. The fix checks
/// has_both (Int && Real) first.
#[test]
fn test_infer_logic_uf_int_real_routes_to_auflira_6077() {
    let features = StaticFeatures {
        has_uf: true,
        has_int: true,
        has_real: true,
        num_theories: 3,
        ..Default::default()
    };
    assert_eq!(
        features.infer_logic(),
        "QF_AUFLIRA",
        "UF+Int+Real must route to QF_AUFLIRA, not QF_UFLRA (Bug 3, #6077)"
    );
}

/// #6077 Bug 3 variant: UF + nonlinear mixed Int/Real routes to QF_UFNIRA.
#[test]
fn test_infer_logic_uf_nonlinear_mixed_routes_to_ufnira_6077() {
    let features = StaticFeatures {
        has_uf: true,
        has_int: true,
        has_real: true,
        has_nonlinear_int: true,
        num_theories: 3,
        ..Default::default()
    };
    assert_eq!(
        features.infer_logic(),
        "QF_UFNIRA",
        "UF+nonlinear Int+Real must route to QF_UFNIRA (Bug 3 variant, #6077)"
    );
}

/// #6077 Bug 4: Mixed Int/Real nonlinear routes to QF_NIRA, not QF_NIA.
///
/// Before the fix, mixed nonlinear returned QF_NIA (pure integer solver),
/// silently dropping Real constraints. The fix returns QF_NIRA so the
/// dispatcher can detect Real terms and return Unknown.
#[test]
fn test_infer_logic_mixed_nonlinear_routes_to_nira_6077() {
    let features = StaticFeatures {
        has_int: true,
        has_real: true,
        has_nonlinear_int: true,
        num_theories: 2,
        ..Default::default()
    };
    assert_eq!(
        features.infer_logic(),
        "QF_NIRA",
        "Mixed Int/Real nonlinear must route to QF_NIRA, not QF_NIA (Bug 4, #6077)"
    );
}

/// Nullary uninterpreted function applications (declare-fun f () Int)
/// must set has_uf (#6498). Without this, logic narrowing strips UF
/// support (e.g., AUFLIA → LIA) and model validation returns Unknown
/// for UF terms that the LIA evaluator cannot check.
#[test]
fn test_collect_nullary_uf_sets_has_uf_6498() {
    use z4_core::term::Symbol;

    let mut terms = TermStore::new();
    // Simulate: (declare-fun f () Int) (assert (not (= f 42)))
    let f_app = terms.mk_app(Symbol::named("logic_secret"), vec![], Sort::Int);
    let forty_two = terms.mk_int(42_i64.into());
    let eq = terms.mk_app(Symbol::named("="), vec![f_app, forty_two], Sort::Bool);
    let neq = terms.mk_not(eq);

    let features = StaticFeatures::collect(&terms, &[neq]);
    assert!(
        features.has_uf,
        "nullary UF application must set has_uf to prevent incorrect logic narrowing"
    );
}

/// extend_with_declarations marks UF for declared non-builtin functions (#7442).
#[test]
fn test_extend_with_declarations_sets_has_uf_7442() {
    let mut features = StaticFeatures {
        has_int: true,
        num_theories: 1,
        ..Default::default()
    };
    assert!(!features.has_uf);
    // Simulate: (declare-fun seq_array (Int) (Array Int Int))
    features.extend_with_declarations(
        [(
            "seq_array",
            vec![Sort::Int].as_slice(),
            &Sort::array(Sort::Int, Sort::Int),
        )]
        .into_iter(),
    );
    assert!(features.has_uf, "declared UF function must set has_uf");
    assert!(
        features.has_arrays,
        "Array-sorted return must set has_arrays"
    );
}

/// extend_with_declarations does NOT mark builtin symbols as UF (#7442).
#[test]
fn test_extend_with_declarations_skips_builtins_7442() {
    let mut features = StaticFeatures::default();
    // "select" is a builtin — should not set has_uf
    features.extend_with_declarations(
        [(
            "select",
            vec![Sort::array(Sort::Int, Sort::Int), Sort::Int].as_slice(),
            &Sort::Int,
        )]
        .into_iter(),
    );
    assert!(!features.has_uf, "builtin symbol must not set has_uf");
}

/// Sequence builtin symbols (seq.empty, seq.len, etc.) are recognized (#7442).
#[test]
fn test_is_builtin_symbol_recognizes_seq_ops_7442() {
    use z4_core::term::Symbol;
    let seq_ops = [
        "seq.len",
        "seq.unit",
        "seq.empty",
        "seq.++",
        "seq.nth",
        "seq.contains",
        "seq.extract",
        "seq.prefixof",
        "seq.suffixof",
        "seq.indexof",
        "seq.last_indexof",
        "seq.replace",
    ];
    for op in &seq_ops {
        assert!(
            is_builtin_symbol(&Symbol::named(*op)),
            "{op} should be recognized as a built-in symbol"
        );
    }
}
