# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

sha256_hex() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum | awk '{print $1}'
        return
    fi
    if command -v shasum >/dev/null 2>&1; then
        shasum -a 256 | awk '{print $1}'
        return
    fi
    echo "sha256_hex: need sha256sum or shasum" >&2
    return 1
}

trace_signature() {
    # Canonicalizes and hashes extracted trace lines of the form:
    #   <state_number>\t<assignment_line>
    #
    # - Numeric-sort by state number so multi-digit traces are stable.
    # - Then sort by assignment line to ignore variable-print order diffs.
    #
    # Input: trace lines on stdin.
    LC_ALL=C sort -t$'\t' -k1,1n -k2,2 | sha256_hex
}

extract_tla2_final_state_block() {
    awk '
        BEGIN { in_state=0; seen_state=0; curr=""; last="" }
        /^State [0-9]+[ :]/ {
            if (seen_state) { last=curr }
            curr=""
            in_state=1
            seen_state=1
            next
        }
        in_state && /^  / {
            line=$0
            sub(/^  /, "", line)
            sub(/^[[:space:]]+/, "", line)
            sub(/[[:space:]]+$/, "", line)
            if (line == "") { next }
            curr=curr line "\n"
            next
        }
        END {
            if (seen_state) { last=curr }
            printf "%s", last
        }
    '
}

extract_tlc_final_state_block() {
    awk '
        BEGIN { in_state=0; seen_state=0; curr=""; last="" }
        /^State [0-9]+:/ {
            if (seen_state) { last=curr }
            curr=""
            in_state=1
            seen_state=1
            next
        }
        in_state && ($0 ~ /^\/\\/ || $0 ~ /^[[:space:]]+/) {
            line=$0
            sub(/^\/\\[[:space:]]*/, "", line)
            sub(/^[[:space:]]+/, "", line)
            sub(/[[:space:]]+$/, "", line)
            if (line == "") { next }
            curr=curr line "\n"
            next
        }
        END {
            if (seen_state) { last=curr }
            printf "%s", last
        }
    '
}

extract_tla2_trace_lines() {
    awk '
        BEGIN { state="" }
        {
            # NOTE: POSIX awk only supports match(s, r) (no 3rd-arg capture array).
            # Use RSTART/RLENGTH and string ops for portability (BSD awk on macOS).
            if (match($0, /^State [0-9]+[ :]/)) {
                s=substr($0, RSTART, RLENGTH)
                sub(/^State /, "", s)
                sub(/[ :].*$/, "", s)
                state=s
                next
            }
            if (state != "" && $0 ~ /^  /) {
                line=$0
                sub(/^  /, "", line)
                sub(/^[[:space:]]+/, "", line)
                sub(/[[:space:]]+$/, "", line)
                if (line == "") { next }
                printf "%s\t%s\n", state, line
            }
        }
    '
}

extract_tlc_trace_lines() {
    awk '
        BEGIN { state="" }
        {
            # NOTE: POSIX awk only supports match(s, r) (no 3rd-arg capture array).
            # Use RSTART/RLENGTH and string ops for portability (BSD awk on macOS).
            if (match($0, /^State [0-9]+:/)) {
                s=substr($0, RSTART, RLENGTH)
                sub(/^State /, "", s)
                sub(/:.*$/, "", s)
                state=s
                next
            }
            if (state != "" && ($0 ~ /^\/\\/ || $0 ~ /^[[:space:]]+/)) {
                line=$0
                sub(/^\/\\[[:space:]]*/, "", line)
                sub(/^[[:space:]]+/, "", line)
                sub(/[[:space:]]+$/, "", line)
                if (line == "") { next }
                printf "%s\t%s\n", state, line
            }
        }
    '
}
