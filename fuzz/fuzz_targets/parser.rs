#![no_main]

use libfuzzer_sys::fuzz_target;
use tla_core::syntax::parser::parse;

fuzz_target!(|data: &[u8]| {
    // Parser should not panic on any input
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = parse(s);
    }
});
