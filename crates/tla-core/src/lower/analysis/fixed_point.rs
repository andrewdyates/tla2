// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

#[derive(Debug, Default)]
pub(super) struct DependencyScan {
    pub(super) local_refs: HashSet<String>,
}

pub(super) fn propagate_truth(
    values: &mut HashMap<String, bool>,
    scans: &HashMap<String, DependencyScan>,
) {
    let mut changed = true;
    while changed {
        changed = false;
        for (name, scan) in scans {
            if values.get(name).copied().unwrap_or(false) {
                continue;
            }

            let should_mark_true = scan
                .local_refs
                .iter()
                .any(|ref_name| values.get(ref_name).copied().unwrap_or(false));

            if should_mark_true {
                values.insert(name.clone(), true);
                changed = true;
            }
        }
    }
}
