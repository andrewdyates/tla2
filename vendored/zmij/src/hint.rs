// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub fn select_unpredictable<T>(condition: bool, true_val: T, false_val: T) -> T {
    if condition {
        true_val
    } else {
        false_val
    }
}
