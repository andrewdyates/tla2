// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

/// Emit Rust code for `SubSeq(s, m, n)` with check-before-cast bounds handling.
pub(super) fn emit_subseq_expr(seq_expr: &str, m_expr: &str, n_expr: &str) -> String {
    format!(
        r#"{{
    let __subseq_seq = &{};
    let __subseq_m = {};
    let __subseq_n = {};
    if __subseq_m > __subseq_n {{
        Vec::new()
    }} else {{
        assert!(__subseq_m >= 1, "SubSeq lower index must be >= 1");
        assert!(__subseq_n >= 1, "SubSeq upper index must be >= 1");
        let __subseq_len = __subseq_seq.len() as i64;
        assert!(
            __subseq_m <= __subseq_len && __subseq_n <= __subseq_len,
            "SubSeq indices out of bounds: m={{}}, n={{}}, len={{}}",
            __subseq_m,
            __subseq_n,
            __subseq_len
        );
        __subseq_seq[(__subseq_m - 1) as usize..__subseq_n as usize].to_vec()
    }}
}}"#,
        seq_expr, m_expr, n_expr
    )
}
