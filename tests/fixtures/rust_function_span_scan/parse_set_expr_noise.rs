// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

impl Parser {
    fn parse_set_expr(&mut self) -> Result<(), String> {
        // Braces in comments should not affect function depth: { } {{{ }}}
        let _regular = "{ not a block }";
        let _raw = r#"raw string with { and }"#;
        let _raw_hash = r##"nested hash raw { } text"##;
        /*
            block comment with braces {
                nested comment /* { } */ still comment
            }
        */
        if true {
            let _inner = 1;
        }
        Ok(())
    }

    fn helper(&self) -> usize {
        0
    }
}
