// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Minimal unified diff generator for the `tla2 fmt --diff` mode.
//!
//! Implements a line-based LCS (Longest Common Subsequence) diff algorithm
//! and formats the result as a standard unified diff with configurable context.

/// Number of context lines surrounding each change hunk.
const CONTEXT_LINES: usize = 3;

/// Produce a unified diff between `original` and `modified`, labeled with `path`.
///
/// Returns an empty string if the texts are identical.
pub(super) fn unified_diff(original: &str, modified: &str, path: &str) -> String {
    let old_lines: Vec<&str> = original.lines().collect();
    let new_lines: Vec<&str> = modified.lines().collect();

    let edits = compute_edits(&old_lines, &new_lines);
    let hunks = group_into_hunks(&edits, CONTEXT_LINES);

    if hunks.is_empty() {
        return String::new();
    }

    let mut out = String::new();
    out.push_str(&format!("--- a/{path}\n"));
    out.push_str(&format!("+++ b/{path}\n"));

    for hunk in &hunks {
        out.push_str(&format!(
            "@@ -{},{} +{},{} @@\n",
            hunk.old_start + 1,
            hunk.old_count,
            hunk.new_start + 1,
            hunk.new_count,
        ));
        for line in &hunk.lines {
            out.push_str(line);
            out.push('\n');
        }
    }

    out
}

/// A single edit operation in the diff sequence.
#[derive(Debug, Clone)]
enum EditOp<'a> {
    /// Line present in both old and new.
    Equal(&'a str, usize, usize),
    /// Line removed from old.
    Delete(&'a str, usize),
    /// Line added in new.
    Insert(&'a str, usize),
}

/// A unified diff hunk with pre-formatted output lines.
struct Hunk {
    old_start: usize,
    old_count: usize,
    new_start: usize,
    new_count: usize,
    lines: Vec<String>,
}

/// Compute the edit sequence between two line slices using LCS.
fn compute_edits<'a>(old: &[&'a str], new: &[&'a str]) -> Vec<EditOp<'a>> {
    let m = old.len();
    let n = new.len();

    // Build LCS length table
    let mut table = vec![vec![0u32; n + 1]; m + 1];
    for i in 1..=m {
        for j in 1..=n {
            if old[i - 1] == new[j - 1] {
                table[i][j] = table[i - 1][j - 1] + 1;
            } else {
                table[i][j] = table[i - 1][j].max(table[i][j - 1]);
            }
        }
    }

    // Backtrack to produce edit sequence
    let mut edits = Vec::new();
    let mut i = m;
    let mut j = n;

    while i > 0 || j > 0 {
        if i > 0 && j > 0 && old[i - 1] == new[j - 1] {
            edits.push(EditOp::Equal(old[i - 1], i - 1, j - 1));
            i -= 1;
            j -= 1;
        } else if j > 0 && (i == 0 || table[i][j - 1] >= table[i - 1][j]) {
            edits.push(EditOp::Insert(new[j - 1], j - 1));
            j -= 1;
        } else {
            edits.push(EditOp::Delete(old[i - 1], i - 1));
            i -= 1;
        }
    }

    edits.reverse();
    edits
}

/// Group a flat edit sequence into unified diff hunks with surrounding context.
fn group_into_hunks(edits: &[EditOp<'_>], context: usize) -> Vec<Hunk> {
    // Find indices of changed (non-Equal) edits
    let change_indices: Vec<usize> = edits
        .iter()
        .enumerate()
        .filter(|(_, e)| !matches!(e, EditOp::Equal(..)))
        .map(|(i, _)| i)
        .collect();

    if change_indices.is_empty() {
        return Vec::new();
    }

    // Group changes that are close enough to share context
    let mut groups: Vec<(usize, usize)> = Vec::new();
    let mut g_start = change_indices[0];
    let mut g_end = change_indices[0];

    for &idx in &change_indices[1..] {
        // Merge if the gap between changes is <= 2*context
        if idx <= g_end + 2 * context + 1 {
            g_end = idx;
        } else {
            groups.push((g_start, g_end));
            g_start = idx;
            g_end = idx;
        }
    }
    groups.push((g_start, g_end));

    // Convert each group into a hunk
    let mut hunks = Vec::new();
    for (g_start, g_end) in groups {
        let hunk_start = g_start.saturating_sub(context);
        let hunk_end = (g_end + context).min(edits.len() - 1);

        let mut lines = Vec::new();
        let mut old_start = None;
        let mut new_start = None;
        let mut old_count = 0usize;
        let mut new_count = 0usize;

        for edit in &edits[hunk_start..=hunk_end] {
            match edit {
                EditOp::Equal(text, oi, ni) => {
                    if old_start.is_none() {
                        old_start = Some(*oi);
                    }
                    if new_start.is_none() {
                        new_start = Some(*ni);
                    }
                    old_count += 1;
                    new_count += 1;
                    lines.push(format!(" {text}"));
                }
                EditOp::Delete(text, oi) => {
                    if old_start.is_none() {
                        old_start = Some(*oi);
                    }
                    old_count += 1;
                    lines.push(format!("-{text}"));
                }
                EditOp::Insert(text, ni) => {
                    if new_start.is_none() {
                        new_start = Some(*ni);
                    }
                    new_count += 1;
                    lines.push(format!("+{text}"));
                }
            }
        }

        hunks.push(Hunk {
            old_start: old_start.unwrap_or(0),
            old_count,
            new_start: new_start.unwrap_or(0),
            new_count,
            lines,
        });
    }

    hunks
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identical_produces_empty_diff() {
        let text = "line1\nline2\nline3\n";
        let result = unified_diff(text, text, "test.tla");
        assert!(
            result.is_empty(),
            "identical text should produce empty diff"
        );
    }

    #[test]
    fn test_single_line_change() {
        let old = "aaa\nbbb\nccc\n";
        let new = "aaa\nBBB\nccc\n";
        let result = unified_diff(old, new, "test.tla");
        assert!(
            result.contains("--- a/test.tla"),
            "should have old file header"
        );
        assert!(
            result.contains("+++ b/test.tla"),
            "should have new file header"
        );
        assert!(result.contains("@@"), "should have hunk header");
        assert!(result.contains("-bbb"), "should show deleted line");
        assert!(result.contains("+BBB"), "should show inserted line");
    }

    #[test]
    fn test_insertion_only() {
        let old = "aaa\nccc\n";
        let new = "aaa\nbbb\nccc\n";
        let result = unified_diff(old, new, "test.tla");
        assert!(result.contains("+bbb"), "should show inserted line");
        // Check that no data lines start with '-' (excluding headers)
        let data_lines: Vec<&str> = result
            .lines()
            .filter(|l| !l.starts_with("---") && !l.starts_with("+++") && !l.starts_with("@@"))
            .collect();
        for line in &data_lines {
            assert!(
                !line.starts_with('-'),
                "no data line should be a deletion: {line}"
            );
        }
    }

    #[test]
    fn test_deletion_only() {
        let old = "aaa\nbbb\nccc\n";
        let new = "aaa\nccc\n";
        let result = unified_diff(old, new, "test.tla");
        assert!(result.contains("-bbb"), "should show deleted line");
    }

    #[test]
    fn test_multiple_changes_in_short_file() {
        let old = "1\n2\n3\n4\n5\n";
        let new = "1\nX\n3\nY\n5\n";
        let result = unified_diff(old, new, "test.tla");
        // Both changes are close together; verify both appear in the diff
        assert!(result.contains("-2"), "should show deletion of line 2");
        assert!(result.contains("+X"), "should show insertion of X");
        assert!(result.contains("-4"), "should show deletion of line 4");
        assert!(result.contains("+Y"), "should show insertion of Y");
    }

    #[test]
    fn test_distant_changes_produce_multiple_hunks() {
        // Build content with changes far enough apart to be in separate hunks.
        // With context=3, changes need >6 lines of unchanged text between them.
        let mut old_lines = Vec::new();
        let mut new_lines = Vec::new();
        for i in 0..30 {
            old_lines.push(format!("line{i}"));
            new_lines.push(format!("line{i}"));
        }
        old_lines[2] = "OLD2".to_string();
        new_lines[2] = "NEW2".to_string();
        old_lines[27] = "OLD27".to_string();
        new_lines[27] = "NEW27".to_string();

        let old = old_lines.join("\n") + "\n";
        let new = new_lines.join("\n") + "\n";
        let result = unified_diff(&old, &new, "test.tla");
        assert!(result.contains("-OLD2"), "should contain first deletion");
        assert!(result.contains("+NEW2"), "should contain first insertion");
        assert!(result.contains("-OLD27"), "should contain second deletion");
        assert!(result.contains("+NEW27"), "should contain second insertion");
        // With ~24 unchanged lines between changes and context=3,
        // these should be in separate hunks (at least 2 @@ markers)
        let hunk_count = result.matches("@@").count();
        assert!(
            hunk_count >= 2,
            "distant changes should produce at least 2 hunks, got {hunk_count}"
        );
    }
}
