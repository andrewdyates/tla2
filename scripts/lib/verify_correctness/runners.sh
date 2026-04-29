# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

config_has_property() {
    local cfg="${1:-}"
    [ -n "$cfg" ] && [ -f "$cfg" ] && grep -Eq '^[[:space:]]*PROPERTY([[:space:]]|$)' "$cfg"
}

# W10: Run a negative test with trace comparison between TLA2 and TLC
# Verifies both tools find the same violation with matching trace signatures
run_negative() {
    local name="$1"
    local spec="$2"
    local config="${3:-}"
    local expected_error="${4:-invariant}"  # invariant, deadlock, or liveness
    local extra_args="${5:-}"

    if [ ! -f "$spec" ]; then
        echo "[ SKIP ] $name (negative) - spec not found"
        SKIP=$((SKIP + 1))
        return
    fi

    # Run TLA2
    local tla2_args="--workers 1"
    if [ -n "$config" ] && [ -f "$config" ]; then
        tla2_args="$tla2_args --config $config"
    fi
    local tla2_output=""
    tla2_output="$($TLA2 check "$spec" $tla2_args $extra_args 2>&1)" || true

    # Run TLC
    local tlc_jar="$HOME/tlaplus/tla2tools.jar"
    if [ ! -f "$tlc_jar" ]; then
        echo "[ SKIP ] $name (negative) - TLC jar not found"
        SKIP=$((SKIP + 1))
        return
    fi

    # Build classpath with CommunityModules if available
    local community_modules="${COMMUNITY_MODULES:-$HOME/tlaplus/CommunityModules.jar}"
    local tlc_cp="$tlc_jar"
    if [ -f "$community_modules" ]; then
        tlc_cp="$tlc_jar:$community_modules"
    fi

    local spec_dir=""
    spec_dir="$(cd "$(dirname "$spec")" && pwd)"
    local states_dir="$spec_dir/states"

    local -a tlc_args=( -workers 1 )
    if [ -n "$config" ] && [ -f "$config" ]; then
        tlc_args+=( -config "$config" )
    fi
    if [ "$expected_error" = "deadlock" ]; then
        tlc_args+=( -deadlock )
    fi

    local tlc_metadir=""
    if [ "${TLA2_KEEP_STATES:-0}" != "1" ]; then
        local tlc_metadir_root="${TLA2_TLC_METADIR_ROOT:-$REPO_ROOT/target/tlc_metadir}"
        mkdir -p "$tlc_metadir_root"
        tlc_metadir="$(mktemp -d "$tlc_metadir_root/tlc_XXXXXX")"
        tlc_args+=( -metadir "$tlc_metadir" )
    fi

    local tlc_output=""
    tlc_output="$(cd "$spec_dir" && java -cp "$tlc_cp" tlc2.TLC "${tlc_args[@]}" "$(basename "$spec")" 2>&1)" || true

    if [ -n "$tlc_metadir" ]; then
        rm -rf "$tlc_metadir"
    fi
    if [ "${TLA2_KEEP_STATES:-0}" != "1" ] && [ "${TLA2_PRESERVE_STATES_DIR:-0}" != "1" ] && [ -d "$states_dir" ]; then
        # Safety: never delete `/states` if someone points a spec at `/`.
        if [ -z "${spec_dir:-}" ] || [ "$spec_dir" = "/" ] || [ "$states_dir" = "/states" ] || [ "$(basename -- "$states_dir")" != "states" ]; then
            echo "[ WARN ] refusing to delete suspicious states dir: spec_dir=$spec_dir states_dir=$states_dir" >&2
        else
            rm -rf "$states_dir"
        fi
    fi

    # Extract TLA2 trace info (use extended regex for multi-digit state numbers)
    local tla2_trace_len=""
    tla2_trace_len="$(echo "$tla2_output" | grep -cE "^State [0-9]+[ :]" || true)"
    local tla2_trace_lines=""
    tla2_trace_lines="$(printf '%s\n' "$tla2_output" | extract_tla2_trace_lines)"
    local tla2_final_state_block=""
    tla2_final_state_block="$(printf '%s\n' "$tla2_output" | extract_tla2_final_state_block)"
    local tla2_final_state_sig=""
    if [ -n "$tla2_final_state_block" ]; then
        tla2_final_state_sig="$(printf '%s' "$tla2_final_state_block" | sha256_hex)"
    fi
    local tla2_trace_sig=""
    if [ "$tla2_trace_len" != "0" ] && [ -n "$tla2_trace_lines" ]; then
        tla2_trace_sig="$(printf '%s\n' "$tla2_trace_lines" | trace_signature)"
    fi

    # Extract TLA2 error type
    local tla2_error=""
    if echo "$tla2_output" | grep -q "Error: Invariant"; then
        tla2_error="invariant"
    elif echo "$tla2_output" | grep -q "Error: Deadlock"; then
        tla2_error="deadlock"
    elif echo "$tla2_output" | grep -q "Error:.*liveness\|Error:.*temporal"; then
        tla2_error="liveness"
    fi

    # Extract TLC trace info (use extended regex for multi-digit state numbers)
    local tlc_trace_len=""
    tlc_trace_len="$(echo "$tlc_output" | grep -cE "^State [0-9]+:" || true)"
    local tlc_trace_lines=""
    tlc_trace_lines="$(printf '%s\n' "$tlc_output" | extract_tlc_trace_lines)"
    local tlc_final_state_block=""
    tlc_final_state_block="$(printf '%s\n' "$tlc_output" | extract_tlc_final_state_block)"
    local tlc_final_state_sig=""
    if [ -n "$tlc_final_state_block" ]; then
        tlc_final_state_sig="$(printf '%s' "$tlc_final_state_block" | sha256_hex)"
    fi
    local tlc_trace_sig=""
    if [ "$tlc_trace_len" != "0" ] && [ -n "$tlc_trace_lines" ]; then
        tlc_trace_sig="$(printf '%s\n' "$tlc_trace_lines" | trace_signature)"
    fi

    # Extract TLC error type
    local tlc_error=""
    if echo "$tlc_output" | grep -q "Invariant.*violated"; then
        tlc_error="invariant"
    elif echo "$tlc_output" | grep -q "Deadlock reached"; then
        tlc_error="deadlock"
    elif echo "$tlc_output" | grep -q "liveness\|temporal"; then
        tlc_error="liveness"
    fi

    # Compare results
    local passed=true
    local failures=""

    # Check both found errors
    if [ -z "$tla2_error" ]; then
        passed=false
        failures="$failures TLA2 found no error;"
    fi
    if [ -z "$tlc_error" ]; then
        passed=false
        failures="$failures TLC found no error;"
    fi

    # Check error types match
    if [ -n "$tla2_error" ] && [ -n "$tlc_error" ] && [ "$tla2_error" != "$tlc_error" ]; then
        passed=false
        failures="$failures error type mismatch (TLA2:$tla2_error vs TLC:$tlc_error);"
    fi

    # Check error type matches expectation
    if [ -n "$expected_error" ] && [ -n "$tla2_error" ] && [ "$tla2_error" != "$expected_error" ]; then
        passed=false
        failures="$failures unexpected TLA2 error type (expected:$expected_error got:$tla2_error);"
    fi
    if [ -n "$expected_error" ] && [ -n "$tlc_error" ] && [ "$tlc_error" != "$expected_error" ]; then
        passed=false
        failures="$failures unexpected TLC error type (expected:$expected_error got:$tlc_error);"
    fi

    # Check trace lengths match
    if [ "$tla2_trace_len" != "$tlc_trace_len" ]; then
        passed=false
        failures="$failures trace length mismatch (TLA2:$tla2_trace_len vs TLC:$tlc_trace_len);"
    fi

    # Check full trace signature matches (normalized per-state lines).
    if [ "$tla2_trace_len" != "0" ] && [ "$tlc_trace_len" != "0" ]; then
        if [ -z "$tla2_trace_sig" ] || [ -z "$tlc_trace_sig" ]; then
            passed=false
            failures="$failures could not extract trace signature;"
        elif [ "$tla2_trace_sig" != "$tlc_trace_sig" ]; then
            passed=false
            failures="$failures trace mismatch;"
        fi
    fi

    # Check trace signature matches (normalized final state).
    if [ "$tla2_trace_len" != "0" ] && [ "$tlc_trace_len" != "0" ]; then
        if [ -z "$tla2_final_state_sig" ] || [ -z "$tlc_final_state_sig" ]; then
            passed=false
            failures="$failures could not extract final state signature;"
        elif [ "$tla2_final_state_sig" != "$tlc_final_state_sig" ]; then
            passed=false
            failures="$failures final state mismatch;"
        fi
    fi

    if [ "$passed" = "true" ]; then
        echo "[ PASS ] $name (negative): $tla2_error, trace=$tla2_trace_len states"
        PASS=$((PASS + 1))
    else
        echo "[ FAIL ] $name (negative):$failures"
        if [ -n "$tla2_trace_lines" ] && [ -n "$tlc_trace_lines" ] && [ "$tla2_trace_sig" != "$tlc_trace_sig" ]; then
            echo "TLA2 trace signature lines (normalized):" >&2
            printf '%s\n' "$tla2_trace_lines" | LC_ALL=C sort -t$'\t' -k1,1n -k2,2 | head -50 >&2
            echo "---" >&2
            echo "TLC trace signature lines (normalized):" >&2
            printf '%s\n' "$tlc_trace_lines" | LC_ALL=C sort -t$'\t' -k1,1n -k2,2 | head -50 >&2
        fi
        if [ -n "$tla2_final_state_block" ] && [ -n "$tlc_final_state_block" ] && [ "$tla2_final_state_sig" != "$tlc_final_state_sig" ]; then
            echo "TLA2 final state (normalized):" >&2
            printf '%s\n' "$tla2_final_state_block" | head -50 >&2
            echo "---" >&2
            echo "TLC final state (normalized):" >&2
            printf '%s\n' "$tlc_final_state_block" | head -50 >&2
        fi
        echo "TLA2 output:" >&2
        printf '%s\n' "$tla2_output" | head -50 >&2
        echo "---"
        echo "TLC output:" >&2
        printf '%s\n' "$tlc_output" | head -50 >&2
        FAIL=$((FAIL + 1))
    fi
}

run_check() {
    local name="$1"
    local spec="$2"
    local expected="$3"
    local config="${4:-}"
    local skip_liveness="${5:-0}"
    local extra_args="${6:-}"
    local expected_error="${7:-}"  # W1: Optional expected error type (invariant/deadlock/liveness)

    if [ ! -f "$spec" ]; then
        echo "[ SKIP ] $name - spec not found"
        SKIP=$((SKIP + 1))
        return
    fi

    # W5: If TLC config has PROPERTY, liveness must be enabled.
    local effective_skip_liveness="$skip_liveness"
    if config_has_property "$config"; then
        effective_skip_liveness="0"
    fi

    # Run TLA2 (optionally skip liveness for specs that don't need it)
    if [ "$effective_skip_liveness" = "1" ]; then
        export TLA2_SKIP_LIVENESS=1
    else
        unset TLA2_SKIP_LIVENESS
    fi

    local output=""
    if [ -n "$config" ] && [ -f "$config" ]; then
        if [ "$skip_liveness" = "1" ] && [ "$effective_skip_liveness" = "0" ]; then
            echo "[ INFO ] $name: enabling liveness (PROPERTY in config)"
        fi
        output="$($TLA2 check "$spec" --config "$config" --workers 1 $extra_args 2>&1)" || true
    else
        output="$($TLA2 check "$spec" --workers 1 $extra_args 2>&1)" || true
    fi

    # Extract state count
    local states=""
    states="$(echo "$output" | grep -oE "States found: [0-9,]+" | tr -d ',' | grep -oE "[0-9]+" || echo "0")"

    # W1: Detect errors in output
    local error_found=""
    if echo "$output" | grep -q "Error: Invariant"; then
        error_found="invariant"
    elif echo "$output" | grep -q "Error: Deadlock"; then
        error_found="deadlock"
    elif echo "$output" | grep -q "Error:.*liveness\|Error:.*temporal\|Error:.*stuttering"; then
        error_found="liveness"
    elif echo "$output" | grep -q "Error:"; then
        error_found="other"
    fi

    # W1: Verify error detection matches expectation
    local error_ok=true
    local error_msg=""

    if [ -n "$expected_error" ]; then
        # Error expected - verify it was found
        if [ -z "$error_found" ]; then
            error_ok=false
            error_msg="Expected $expected_error error, but TLA2 found no error"
        elif [ "$error_found" != "$expected_error" ]; then
            # Allow some type flexibility (invariant=safety, liveness=temporal)
            case "$expected_error-$error_found" in
                invariant-safety|safety-invariant|liveness-temporal|temporal-liveness)
                    error_ok=true  # Acceptable mismatch
                    ;;
                *)
                    error_ok=false
                    error_msg="Expected $expected_error error, but TLA2 found $error_found"
                    ;;
            esac
        fi
    else
        # No error expected - verify none was found
        if [ -n "$error_found" ]; then
            error_ok=false
            error_msg="TLA2 found unexpected $error_found error"
        fi
    fi

    # Final pass/fail decision
    if [ "$states" = "$expected" ] && [ "$error_ok" = "true" ]; then
        echo "[ PASS ] $name: $states states (expected $expected)"
        PASS=$((PASS + 1))
    else
        if [ "$states" != "$expected" ]; then
            echo "[ FAIL ] $name: $states states (expected $expected)"
        else
            echo "[ FAIL ] $name: $error_msg"
        fi
        echo "Output: $output"
        FAIL=$((FAIL + 1))
    fi
}

# run_eval: Run an evaluator-only test (1 state, no transitions)
# These test expression evaluation via ASSUME/invariants, NOT model checking.
# Output uses [EVAL ] prefix to distinguish from model checking tests.
run_eval() {
    local name="$1"
    local spec="$2"
    local expected="$3"
    local config="${4:-}"
    local extra_args="${5:-}"

    if [ ! -f "$spec" ]; then
        echo "[ SKIP ] $name - spec not found"
        SKIP=$((SKIP + 1))
        return
    fi

    # Evaluator tests always skip liveness (no transitions)
    export TLA2_SKIP_LIVENESS=1

    local output=""
    if [ -n "$config" ] && [ -f "$config" ]; then
        output="$($TLA2 check "$spec" --config "$config" --workers 1 $extra_args 2>&1)" || true
    else
        output="$($TLA2 check "$spec" --workers 1 $extra_args 2>&1)" || true
    fi

    # Extract state count
    local states=""
    states="$(echo "$output" | grep -oE "States found: [0-9,]+" | tr -d ',' | grep -oE "[0-9]+" || echo "0")"

    # Check for unexpected errors
    if echo "$output" | grep -q "Error:"; then
        echo "[ FAIL ] $name (eval): unexpected error in evaluator test"
        echo "Output: $output"
        FAIL=$((FAIL + 1))
        return
    fi

    if [ "$states" = "$expected" ]; then
        echo "[ EVAL ] $name: $states states (evaluator-only)"
        EVAL=$((EVAL + 1))
    else
        echo "[ FAIL ] $name (eval): $states states (expected $expected)"
        echo "Output: $output"
        FAIL=$((FAIL + 1))
    fi
}
