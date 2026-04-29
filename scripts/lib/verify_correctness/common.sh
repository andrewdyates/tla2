# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

run_with_heartbeat_tee() {
    local heartbeat_sec="$1"
    local heartbeat_msg="$2"
    local log_path="$3"
    shift 3

    local start_s=""
    start_s="$(date +%s)"

    (
        set -o pipefail
        "$@" 2>&1 | tee "$log_path"
    ) &

    local pid="$!"
    while kill -0 "$pid" >/dev/null 2>&1; do
        sleep "$heartbeat_sec"
        if kill -0 "$pid" >/dev/null 2>&1; then
            local now_s=""
            now_s="$(date +%s)"
            echo "[ INFO ] $heartbeat_msg (+$((now_s - start_s))s)" >&2
        fi
    done

    wait "$pid"
}
