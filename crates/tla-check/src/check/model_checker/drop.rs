// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::debug::debug_lazy_values_in_state;
use super::ModelChecker;

impl Drop for ModelChecker<'_> {
    fn drop(&mut self) {
        // FP collision summaries — active in both debug and release builds.
        // Part of #2841.
        if let Some(ref seen) = self.debug.seen_tlc_fp_dedup {
            let unique = seen.len();
            let collisions = self.debug.seen_tlc_fp_dedup_collisions;
            eprintln!(
                "FP DEDUP SUMMARY unique_tlc_fps={} collisions={} internal_states_seen={}",
                unique,
                collisions,
                self.states_count()
            );
        }
        if let Some(ref seen) = self.debug.internal_fp_collision {
            let unique_internal = seen.len();
            let collisions = self.debug.internal_fp_collisions;
            eprintln!(
                "FP COLLISION SUMMARY unique_internal_fps={} collisions={} internal_states_seen={}",
                unique_internal,
                collisions,
                self.states_count()
            );
        }

        // Lazy value summary — debug builds only.
        #[cfg(debug_assertions)]
        debug_eprintln!(
            debug_lazy_values_in_state(),
            "DEBUG LAZY VALUES IN STATE SUMMARY states_with_lazy={} lazy_values={} internal_states_seen={}",
            self.debug.lazy_values_in_state_states,
            self.debug.lazy_values_in_state_values,
            self.states_count()
        );
    }
}
