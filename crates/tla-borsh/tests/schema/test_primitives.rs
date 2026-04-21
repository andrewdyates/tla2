// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use crate::common_macro::schema_imports::*;

#[test]
fn isize_schema() {
    let schema = schema_container_of::<isize>();

    assert_eq!(
        schema,
        BorshSchemaContainer::new(
            "i64".to_string(),
            schema_map! {
                "i64" => Definition::Primitive(8)

            }
        )
    )
}

#[test]
fn usize_schema() {
    let schema = schema_container_of::<usize>();

    assert_eq!(
        schema,
        BorshSchemaContainer::new(
            "u64".to_string(),
            schema_map! {
                "u64" => Definition::Primitive(8)

            }
        )
    )
}
