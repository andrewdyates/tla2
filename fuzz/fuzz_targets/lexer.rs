#![no_main]

use libfuzzer_sys::fuzz_target;
use tla_core::syntax::lexer::lex_all;

fuzz_target!(|data: &[u8]| {
    // Lexer should not panic on any input
    if let Ok(s) = std::str::from_utf8(data) {
        // Consume all tokens
        for _ in lex_all(s) {}
    }
});
