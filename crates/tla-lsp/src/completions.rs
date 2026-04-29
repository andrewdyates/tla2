// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_core::{
    ast::Module, get_module_operators, ResolveResult, SymbolKind as TlaSymbolKind, STDLIB_MODULES,
};
use tower_lsp::lsp_types::*;

/// Get completion items for TLA+ keywords
pub(crate) fn get_keyword_completions() -> Vec<CompletionItem> {
    const KEYWORDS: &[(&str, &str)] = &[
        ("MODULE", "Module declaration"),
        ("EXTENDS", "Import module definitions"),
        ("VARIABLE", "Declare state variable(s)"),
        ("VARIABLES", "Declare state variable(s)"),
        ("CONSTANT", "Declare constant(s)"),
        ("CONSTANTS", "Declare constant(s)"),
        ("ASSUME", "Add assumption"),
        ("THEOREM", "Declare theorem"),
        ("LEMMA", "Declare lemma"),
        ("PROPOSITION", "Declare proposition"),
        ("COROLLARY", "Declare corollary"),
        ("AXIOM", "Declare axiom"),
        ("LOCAL", "Make definition module-local"),
        ("INSTANCE", "Instantiate module"),
        ("LET", "Local definitions"),
        ("IN", "Body of LET expression"),
        ("IF", "Conditional expression"),
        ("THEN", "Then branch"),
        ("ELSE", "Else branch"),
        ("CASE", "Case expression"),
        ("OTHER", "Default case branch"),
        ("CHOOSE", "Choice operator"),
        ("EXCEPT", "Function update"),
        ("ENABLED", "Enabled predicate"),
        ("UNCHANGED", "Unchanged predicate"),
        ("SUBSET", "Powerset operator"),
        ("UNION", "Generalized union"),
        ("DOMAIN", "Function domain"),
        ("BOOLEAN", "Set {TRUE, FALSE}"),
        ("STRING", "Set of strings"),
        ("TRUE", "Boolean true"),
        ("FALSE", "Boolean false"),
        ("LAMBDA", "Lambda expression"),
        ("WF_", "Weak fairness"),
        ("SF_", "Strong fairness"),
        // Proof keywords
        ("PROOF", "Begin proof"),
        ("BY", "Proof justification"),
        ("OBVIOUS", "Obvious proof step"),
        ("OMITTED", "Omitted proof"),
        ("QED", "End of proof"),
        ("PROVE", "Proof goal"),
        ("SUFFICES", "Suffices to prove"),
        ("HAVE", "Assert in proof"),
        ("TAKE", "Universal instantiation"),
        ("WITNESS", "Existential instantiation"),
        ("PICK", "Choose witness"),
        ("DEFINE", "Local definition in proof"),
        ("HIDE", "Hide fact in proof"),
        ("USE", "Use fact in proof"),
        ("DEFS", "Use definitions"),
        ("DEF", "Use definition"),
        ("ONLY", "Use only specified facts"),
        ("NEW", "Introduce new constant"),
    ];

    KEYWORDS
        .iter()
        .map(|(name, doc)| CompletionItem {
            label: name.to_string(),
            kind: Some(CompletionItemKind::KEYWORD),
            detail: Some(doc.to_string()),
            ..Default::default()
        })
        .collect()
}

/// Get completion items for standard library modules
pub(crate) fn get_stdlib_module_completions() -> Vec<CompletionItem> {
    STDLIB_MODULES
        .iter()
        .map(|name| CompletionItem {
            label: name.to_string(),
            kind: Some(CompletionItemKind::MODULE),
            detail: Some("Standard library module".to_string()),
            ..Default::default()
        })
        .collect()
}

/// Get completion items for operators from extended modules
pub(crate) fn get_stdlib_operator_completions(module: &Module) -> Vec<CompletionItem> {
    let mut completions = Vec::new();
    let mut seen = std::collections::HashSet::new();

    // Process extended modules and their transitive dependencies
    fn process_module(
        module_name: &str,
        completions: &mut Vec<CompletionItem>,
        seen: &mut std::collections::HashSet<String>,
    ) {
        if seen.contains(module_name) {
            return;
        }
        seen.insert(module_name.to_string());

        // Handle transitive extends
        match module_name {
            "Integers" => process_module("Naturals", completions, seen),
            "Reals" => process_module("Integers", completions, seen),
            _ => {}
        }

        // Add operators from this module
        for (name, arity) in get_module_operators(module_name) {
            let detail = if *arity == 0 {
                format!("{} (constant)", module_name)
            } else if *arity < 0 {
                format!("{} (variadic)", module_name)
            } else {
                format!("{} (arity {})", module_name, arity)
            };

            completions.push(CompletionItem {
                label: name.to_string(),
                kind: Some(CompletionItemKind::FUNCTION),
                detail: Some(detail),
                ..Default::default()
            });
        }

        // Add built-in constants for certain modules
        match module_name {
            "Naturals" => {
                completions.push(CompletionItem {
                    label: "Nat".to_string(),
                    kind: Some(CompletionItemKind::CONSTANT),
                    detail: Some("Set of natural numbers".to_string()),
                    ..Default::default()
                });
            }
            "Integers" => {
                completions.push(CompletionItem {
                    label: "Int".to_string(),
                    kind: Some(CompletionItemKind::CONSTANT),
                    detail: Some("Set of integers".to_string()),
                    ..Default::default()
                });
            }
            "Reals" => {
                completions.push(CompletionItem {
                    label: "Real".to_string(),
                    kind: Some(CompletionItemKind::CONSTANT),
                    detail: Some("Set of real numbers".to_string()),
                    ..Default::default()
                });
                completions.push(CompletionItem {
                    label: "Infinity".to_string(),
                    kind: Some(CompletionItemKind::CONSTANT),
                    detail: Some("Infinity constant".to_string()),
                    ..Default::default()
                });
            }
            _ => {}
        }
    }

    for ext in &module.extends {
        process_module(&ext.node, &mut completions, &mut seen);
    }

    completions
}

/// Get completion items for local symbols
pub(crate) fn get_local_symbol_completions(resolve: &ResolveResult) -> Vec<CompletionItem> {
    resolve
        .symbols
        .iter()
        .filter(|sym| {
            // Only include module-level definitions, not bound variables
            matches!(
                sym.kind,
                TlaSymbolKind::Variable
                    | TlaSymbolKind::Constant
                    | TlaSymbolKind::Operator
                    | TlaSymbolKind::Module
            )
        })
        .map(|sym| {
            let kind = match sym.kind {
                TlaSymbolKind::Variable => CompletionItemKind::VARIABLE,
                TlaSymbolKind::Constant => CompletionItemKind::CONSTANT,
                TlaSymbolKind::Operator => {
                    if sym.arity > 0 {
                        CompletionItemKind::FUNCTION
                    } else {
                        CompletionItemKind::CONSTANT
                    }
                }
                TlaSymbolKind::Module => CompletionItemKind::MODULE,
                _ => CompletionItemKind::TEXT,
            };

            let detail = if sym.arity > 0 {
                Some(format!("arity {}", sym.arity))
            } else {
                None
            };

            CompletionItem {
                label: sym.name.clone(),
                kind: Some(kind),
                detail,
                ..Default::default()
            }
        })
        .collect()
}
