// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(test)]
use tla_core::ast::{Expr, Module, Substitution, Unit};
#[cfg(test)]
use tla_core::Spanned;

/// Compute implicit substitutions for an INSTANCE declaration.
///
/// When a module is INSTANCE'd without explicit WITH substitutions,
/// variables and constants with matching names in both modules are
/// implicitly substituted (identity substitution: p <- p).
///
/// The `instancer_extended_modules` contains modules the instancer EXTENDS.
/// Symbols from these are also considered for implicit substitution (fixes #148).
/// Note: currently only exercised by unit tests. The adaptive checker was the
/// sole production consumer; after its constructor was simplified to use
/// `setup_imports::collect_ops_vars_and_assumes`, no production code path
/// calls this function.  Retained under `#[cfg(test)]` to preserve test
/// coverage of the implicit-substitution logic.
#[cfg(test)]
pub(crate) fn compute_implicit_substitutions(
    instanced_module: &Module,
    instancer_module: &Module,
    instancer_extended_modules: &[&Module],
    explicit_subs: &[Substitution],
) -> Vec<Substitution> {
    let explicit_names: std::collections::HashSet<&str> =
        explicit_subs.iter().map(|s| s.from.node.as_str()).collect();

    // Collect symbols from the instancer module AND its extended modules
    let mut instancer_symbols: std::collections::HashSet<&str> = std::collections::HashSet::new();

    fn collect_symbols<'a>(module: &'a Module, symbols: &mut std::collections::HashSet<&'a str>) {
        for unit in &module.units {
            match &unit.node {
                Unit::Variable(names) => {
                    for name in names {
                        symbols.insert(name.node.as_str());
                    }
                }
                Unit::Constant(decls) => {
                    for decl in decls {
                        symbols.insert(decl.name.node.as_str());
                    }
                }
                Unit::Operator(def) => {
                    symbols.insert(def.name.node.as_str());
                }
                _ => {}
            }
        }
    }

    // First collect from extended modules
    for ext_mod in instancer_extended_modules {
        collect_symbols(ext_mod, &mut instancer_symbols);
    }
    // Then from instancer module itself (may shadow)
    collect_symbols(instancer_module, &mut instancer_symbols);

    // Build implicit substitutions for matching variables/constants
    let mut implicit_subs = Vec::new();
    for unit in &instanced_module.units {
        match &unit.node {
            Unit::Variable(names) => {
                for name in names {
                    let name_str = name.node.as_str();
                    if !explicit_names.contains(name_str) && instancer_symbols.contains(name_str) {
                        implicit_subs.push(Substitution {
                            from: name.clone(),
                            to: Spanned {
                                node: Expr::Ident(
                                    name.node.clone(),
                                    tla_core::name_intern::NameId::INVALID,
                                ),
                                span: name.span,
                            },
                        });
                    }
                }
            }
            Unit::Constant(decls) => {
                for decl in decls {
                    let name_str = decl.name.node.as_str();
                    if !explicit_names.contains(name_str) && instancer_symbols.contains(name_str) {
                        implicit_subs.push(Substitution {
                            from: decl.name.clone(),
                            to: Spanned {
                                node: Expr::Ident(
                                    decl.name.node.clone(),
                                    tla_core::name_intern::NameId::INVALID,
                                ),
                                span: decl.name.span,
                            },
                        });
                    }
                }
            }
            _ => {}
        }
    }
    implicit_subs
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::ast::{ConstantDecl, OperatorDef};
    use tla_core::Span;

    fn s(name: &str) -> Spanned<String> {
        Spanned::dummy(name.to_string())
    }

    fn make_module(name: &str, vars: &[&str], consts: &[&str]) -> Module {
        let mut units = Vec::new();
        if !vars.is_empty() {
            units.push(Spanned::dummy(Unit::Variable(
                vars.iter().map(|v| s(v)).collect(),
            )));
        }
        if !consts.is_empty() {
            units.push(Spanned::dummy(Unit::Constant(
                consts
                    .iter()
                    .map(|c| ConstantDecl {
                        name: s(c),
                        arity: None,
                    })
                    .collect(),
            )));
        }
        Module {
            name: s(name),
            extends: vec![],
            units,
            action_subscript_spans: Default::default(),
            span: Span::dummy(),
        }
    }

    fn make_module_with_ops(name: &str, vars: &[&str], ops: &[&str]) -> Module {
        let mut m = make_module(name, vars, &[]);
        for op_name in ops {
            m.units.push(Spanned::dummy(Unit::Operator(OperatorDef {
                name: s(op_name),
                params: vec![],
                body: Spanned::dummy(Expr::Bool(true)),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })));
        }
        m
    }

    #[test]
    fn test_matching_variables_get_implicit_substitution() {
        let instanced = make_module("Inner", &["x", "y"], &[]);
        let instancer = make_module("Outer", &["x", "y"], &[]);

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[], &[]);

        assert_eq!(subs.len(), 2);
        assert_eq!(subs[0].from.node, "x");
        assert_eq!(subs[1].from.node, "y");
        assert!(matches!(&subs[0].to.node, Expr::Ident(n, _) if n == "x"));
        assert!(matches!(&subs[1].to.node, Expr::Ident(n, _) if n == "y"));
    }

    #[test]
    fn test_matching_constants_get_implicit_substitution() {
        let instanced = make_module("Inner", &[], &["N", "M"]);
        let instancer = make_module("Outer", &[], &["N", "M"]);

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[], &[]);

        assert_eq!(subs.len(), 2);
        assert_eq!(subs[0].from.node, "N");
        assert_eq!(subs[1].from.node, "M");
    }

    #[test]
    fn test_non_matching_names_get_no_substitution() {
        let instanced = make_module("Inner", &["x"], &["N"]);
        let instancer = make_module("Outer", &["y"], &["M"]);

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[], &[]);

        assert_eq!(subs.len(), 0);
    }

    #[test]
    fn test_explicit_substitution_suppresses_implicit() {
        let instanced = make_module("Inner", &["x", "y"], &[]);
        let instancer = make_module("Outer", &["x", "y"], &[]);
        let explicit = vec![Substitution {
            from: s("x"),
            to: Spanned::dummy(Expr::Ident(
                "other".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        }];

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[], &explicit);

        assert_eq!(subs.len(), 1);
        assert_eq!(subs[0].from.node, "y");
    }

    #[test]
    fn test_extended_module_provides_symbols() {
        let instanced = make_module("Inner", &["x"], &["N"]);
        let instancer = make_module("Outer", &[], &[]); // no matching symbols
        let extended = make_module("Base", &["x"], &["N"]);

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[&extended], &[]);

        assert_eq!(subs.len(), 2);
        assert_eq!(subs[0].from.node, "x");
        assert_eq!(subs[1].from.node, "N");
    }

    #[test]
    fn test_operator_symbol_matches_constant_in_instanced() {
        // Instancer has an operator named "N"; instanced has a constant "N".
        // The symbol "N" is in instancer_symbols via the Operator variant,
        // so it should produce an implicit substitution.
        let instanced = make_module("Inner", &[], &["N"]);
        let instancer = make_module_with_ops("Outer", &[], &["N"]);

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[], &[]);

        assert_eq!(subs.len(), 1);
        assert_eq!(subs[0].from.node, "N");
    }

    #[test]
    fn test_empty_modules_produce_no_substitutions() {
        let instanced = make_module("Inner", &[], &[]);
        let instancer = make_module("Outer", &[], &[]);

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[], &[]);

        assert_eq!(subs.len(), 0);
    }

    #[test]
    fn test_mixed_variables_and_constants() {
        let instanced = make_module("Inner", &["x", "y"], &["N", "M"]);
        let instancer = make_module("Outer", &["x"], &["M"]);

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[], &[]);

        // Only x (var) and M (const) match
        assert_eq!(subs.len(), 2);
        assert_eq!(subs[0].from.node, "x");
        assert_eq!(subs[1].from.node, "M");
    }

    #[test]
    fn test_multiple_extended_modules() {
        let instanced = make_module("Inner", &["a", "b", "c"], &[]);
        let instancer = make_module("Outer", &[], &[]);
        let ext1 = make_module("Base1", &["a"], &[]);
        let ext2 = make_module("Base2", &["b"], &[]);

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[&ext1, &ext2], &[]);

        assert_eq!(subs.len(), 2);
        assert_eq!(subs[0].from.node, "a");
        assert_eq!(subs[1].from.node, "b");
        // "c" has no match anywhere
    }

    #[test]
    fn test_all_explicit_suppresses_all_implicit() {
        let instanced = make_module("Inner", &["x"], &["N"]);
        let instancer = make_module("Outer", &["x"], &["N"]);
        let explicit = vec![
            Substitution {
                from: s("x"),
                to: Spanned::dummy(Expr::Ident(
                    "a".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                )),
            },
            Substitution {
                from: s("N"),
                to: Spanned::dummy(Expr::Ident(
                    "b".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                )),
            },
        ];

        let subs = compute_implicit_substitutions(&instanced, &instancer, &[], &explicit);

        assert_eq!(subs.len(), 0);
    }
}
