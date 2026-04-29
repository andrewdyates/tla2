// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for SPECIFICATION formula extraction.

use super::*;
use tla_core::{parse_to_syntax_tree, SyntaxElement, SyntaxKind, SyntaxNode};

mod extraction;
mod fairness;
mod subscript_forms;

fn find_op_body(tree: &SyntaxNode, name: &str) -> Option<SyntaxNode> {
    fn search(node: &SyntaxNode, name: &str) -> Option<SyntaxNode> {
        if node.kind() == SyntaxKind::OperatorDef {
            let mut found_name = false;
            for child in node.children_with_tokens() {
                if let SyntaxElement::Token(t) = child {
                    if t.kind() == SyntaxKind::Ident && t.text() == name {
                        found_name = true;
                        break;
                    }
                }
            }
            if found_name {
                // Conjunction-list bodies can surface as multiple top-level expressions;
                // return the full operator node so recursive traversals still see all conjuncts.
                let mut body_nodes = Vec::new();
                let mut past_def_eq = false;
                for child in node.children_with_tokens() {
                    match child {
                        SyntaxElement::Token(t) if t.kind() == SyntaxKind::DefEqOp => {
                            past_def_eq = true;
                        }
                        SyntaxElement::Node(n) if past_def_eq => body_nodes.push(n),
                        _ => {}
                    }
                }

                match body_nodes.as_slice() {
                    [single] => return Some(single.clone()),
                    [] | [_, ..] => return Some(node.clone()),
                }
            }
        }
        for child in node.children() {
            if let Some(found) = search(&child, name) {
                return Some(found);
            }
        }
        None
    }

    search(tree, name)
}
