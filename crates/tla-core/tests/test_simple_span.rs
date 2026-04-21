// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_core::{lower, parse_to_syntax_tree, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simple_operator_span() {
    let source = r"---- MODULE Test ----
SendMessage(m) == messages' = messages \union {m}
(*
Comment block
*)
PaxosPrepare == TRUE
====";

    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);
    assert!(
        result.errors.is_empty(),
        "unexpected lowering errors: {:?}",
        result.errors
    );
    let module = result.module.expect("Module");
    let mut saw_send_message = false;
    let mut saw_paxos_prepare = false;

    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            let start = def.body.span.start as usize;
            let end = def.body.span.end as usize;
            assert!(
                start < end,
                "operator `{}` has invalid empty span {start}..{end}",
                def.name.node
            );
            assert!(
                end <= source.len(),
                "operator `{}` span {start}..{end} exceeds source length {}",
                def.name.node,
                source.len()
            );
            let body_text = source[start..end].trim();

            match def.name.node.clone().as_str() {
                "SendMessage" => {
                    saw_send_message = true;
                    assert_eq!(body_text, "messages' = messages \\union {m}");
                }
                "PaxosPrepare" => {
                    saw_paxos_prepare = true;
                    assert_eq!(body_text, "TRUE");
                }
                other => {
                    panic!("unexpected operator in fixture module: {other}");
                }
            }
        }
    }

    assert!(saw_send_message, "expected SendMessage operator in module");
    assert!(
        saw_paxos_prepare,
        "expected PaxosPrepare operator in module"
    );
}
