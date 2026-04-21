// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[allow(clippy::struct_field_names)]
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct DisabledActionStatsSnapshot {
    pub(crate) disabled_choose_failed: usize,
    pub(crate) disabled_not_in_domain: usize,
    pub(crate) disabled_index_out_of_bounds: usize,
    pub(crate) disabled_no_such_field: usize,
    pub(crate) disabled_division_by_zero: usize,
    pub(crate) disabled_type_error: usize,
}

impl DisabledActionStatsSnapshot {
    #[inline]
    pub(crate) fn total_disabled(self) -> usize {
        self.disabled_choose_failed
            + self.disabled_not_in_domain
            + self.disabled_index_out_of_bounds
            + self.disabled_no_such_field
            + self.disabled_division_by_zero
            + self.disabled_type_error
    }
}

debug_flag_strict!(pub(crate) enabled_for_process, "TLA2_DISABLED_ACTION_STATS");

#[must_use]
pub(crate) fn render(snapshot: DisabledActionStatsSnapshot) -> Option<String> {
    let total_disabled = snapshot.total_disabled();
    if total_disabled == 0 {
        return None;
    }

    let mut out = String::new();
    out.push_str("=== Disabled Action Stats ===\n");
    if snapshot.disabled_choose_failed > 0 {
        append_stat_line(
            &mut out,
            "  ChooseFailed:     ",
            snapshot.disabled_choose_failed,
        );
    }
    if snapshot.disabled_not_in_domain > 0 {
        append_stat_line(
            &mut out,
            "  NotInDomain:      ",
            snapshot.disabled_not_in_domain,
        );
    }
    if snapshot.disabled_index_out_of_bounds > 0 {
        append_stat_line(
            &mut out,
            "  IndexOutOfBounds: ",
            snapshot.disabled_index_out_of_bounds,
        );
    }
    if snapshot.disabled_no_such_field > 0 {
        append_stat_line(
            &mut out,
            "  NoSuchField:      ",
            snapshot.disabled_no_such_field,
        );
    }
    if snapshot.disabled_division_by_zero > 0 {
        append_stat_line(
            &mut out,
            "  DivisionByZero:   ",
            snapshot.disabled_division_by_zero,
        );
    }
    if snapshot.disabled_type_error > 0 {
        append_stat_line(
            &mut out,
            "  TypeError:        ",
            snapshot.disabled_type_error,
        );
    }
    append_stat_line(&mut out, "  TOTAL:            ", total_disabled);
    out.push_str("=============================\n");
    Some(out)
}

fn append_stat_line(out: &mut String, label: &str, value: usize) {
    use std::fmt::Write;
    out.push_str(label);
    write!(out, "{value}").expect("invariant: String fmt::Write is infallible");
    out.push('\n');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_render_none_when_empty() {
        assert_eq!(render(DisabledActionStatsSnapshot::default()), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_render_only_nonzero_fields() {
        let snapshot = DisabledActionStatsSnapshot {
            disabled_choose_failed: 2,
            disabled_division_by_zero: 1,
            ..DisabledActionStatsSnapshot::default()
        };

        let rendered = render(snapshot).expect("non-empty stats must render");
        let expected = "\
=== Disabled Action Stats ===
  ChooseFailed:     2
  DivisionByZero:   1
  TOTAL:            3
=============================
";
        assert_eq!(rendered, expected);
        assert!(
            !rendered.contains("NotInDomain:"),
            "zero fields must be omitted"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_total_disabled() {
        let snapshot = DisabledActionStatsSnapshot {
            disabled_choose_failed: 2,
            disabled_not_in_domain: 3,
            disabled_index_out_of_bounds: 0,
            disabled_no_such_field: 1,
            disabled_division_by_zero: 4,
            disabled_type_error: 0,
        };
        assert_eq!(snapshot.total_disabled(), 10);
    }
}
