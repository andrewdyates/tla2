#!/usr/bin/env bash
# clean_stale_targets.sh - Clean stale cargo target directories under target/
#
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

set -euo pipefail

usage() {
    local exit_code="${1:-0}"
    local output_fd=1
    if [[ "$exit_code" -ne 0 ]]; then
        output_fd=2
    fi

    cat >&"$output_fd" <<'EOF'
Usage: clean_stale_targets.sh [OPTIONS]

List direct target/ subdirectories, mark stale directories by access time, and
optionally delete them.

Options:
  --max-age-days N   Mark directories stale when last accessed >= N days ago
                     (default: 7)
  --force            Actually delete stale directories
  -h, --help         Show this help message

Protected directories:
  target/user
  target/release
  target/debug
  target/criterion

Protected files:
  Any *.json file directly under target/

Examples:
  ./scripts/clean_stale_targets.sh
  ./scripts/clean_stale_targets.sh --max-age-days 14
  ./scripts/clean_stale_targets.sh --force
EOF
    exit "$exit_code"
}

is_protected_dir() {
    case "$1" in
    user | release | debug | criterion)
        return 0
        ;;
    *)
        return 1
        ;;
    esac
}

dir_size_kib() {
    du -sk "$1" 2>/dev/null | awk '{print $1}'
}

dir_atime_epoch() {
    local path="$1"
    case "$(uname -s)" in
    Darwin)
        stat -f %a "$path" 2>/dev/null || stat -c %X "$path" 2>/dev/null
        ;;
    *)
        stat -c %X "$path" 2>/dev/null || stat -f %a "$path" 2>/dev/null
        ;;
    esac
}

format_timestamp() {
    local epoch="$1"
    date -r "$epoch" '+%Y-%m-%d %H:%M:%S' 2>/dev/null ||
        date -d "@$epoch" '+%Y-%m-%d %H:%M:%S' 2>/dev/null ||
        printf 'unknown'
}

format_size_kib() {
    local kib="$1"
    awk -v kib="$kib" '
        BEGIN {
            if (kib >= 1024 * 1024) {
                printf "%.1fG", kib / (1024 * 1024)
            } else if (kib >= 1024) {
                printf "%.1fM", kib / 1024
            } else {
                printf "%dK", kib
            }
        }
    '
}

main() {
    local max_age_days="${CARGO_TARGET_MAX_AGE_DAYS:-7}"
    local force=false

    while [[ $# -gt 0 ]]; do
        case "$1" in
        --max-age-days)
            if [[ -z "${2:-}" ]] || [[ "$2" =~ ^- ]]; then
                echo "Error: --max-age-days requires a numeric argument" >&2
                usage 1
            fi
            if ! [[ "$2" =~ ^[0-9]+$ ]]; then
                echo "Error: --max-age-days must be a non-negative integer (got: $2)" >&2
                exit 1
            fi
            max_age_days="$2"
            shift 2
            ;;
        --max-age-days=*)
            max_age_days="${1#*=}"
            if ! [[ "$max_age_days" =~ ^[0-9]+$ ]]; then
                echo "Error: --max-age-days must be a non-negative integer (got: $max_age_days)" >&2
                exit 1
            fi
            shift
            ;;
        --force)
            force=true
            shift
            ;;
        -h | --help)
            usage 0
            ;;
        -*)
            echo "Error: Unknown option $1" >&2
            usage 1
            ;;
        *)
            echo "Error: Unexpected argument $1" >&2
            usage 1
            ;;
        esac
    done

    local script_dir
    local repo_root
    local target_dir
    script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    repo_root="$(git -C "$script_dir/.." rev-parse --show-toplevel 2>/dev/null || (cd "$script_dir/.." && pwd))"
    target_dir="$repo_root/target"

    if [[ ! -d "$target_dir" ]]; then
        echo "Error: target directory not found: $target_dir" >&2
        exit 1
    fi

    local now
    local max_age_sec
    now="$(date +%s)"
    max_age_sec=$((max_age_days * 86400))

    local scanned_count=0
    local protected_count=0
    local active_count=0
    local stale_count=0
    local stale_total_kib=0

    local -a stale_dirs=()
    local -a protected_json_files=()

    while IFS= read -r file_path; do
        [[ -n "$file_path" ]] || continue
        protected_json_files+=("$(basename "$file_path")")
    done < <(find "$target_dir" -mindepth 1 -maxdepth 1 -type f -name '*.json' -print | LC_ALL=C sort)

    printf 'Scanning %s\n' "$target_dir"
    printf 'Mode: %s\n' "$([[ "$force" == true ]] && printf 'delete' || printf 'dry-run')"
    printf 'Max age: %s day(s)\n' "$max_age_days"
    echo

    printf '%-40s %10s %-19s %s\n' "Directory" "Size" "Last Accessed" "Status"
    printf '%-40s %10s %-19s %s\n' "---------" "----" "-------------" "------"

    while IFS= read -r dir_path; do
        [[ -n "$dir_path" ]] || continue

        local dir_name
        local size_kib
        local atime_epoch
        local last_accessed
        local status
        local age_sec

        dir_name="$(basename "$dir_path")"
        size_kib="$(dir_size_kib "$dir_path" || echo 0)"
        atime_epoch="$(dir_atime_epoch "$dir_path" || printf '%s' "$now")"
        if ! [[ "$atime_epoch" =~ ^[0-9]+$ ]]; then
            atime_epoch="$now"
        fi
        if (( atime_epoch > now )); then
            age_sec=0
        else
            age_sec=$((now - atime_epoch))
        fi
        last_accessed="$(format_timestamp "$atime_epoch")"

        scanned_count=$((scanned_count + 1))
        status="ACTIVE"

        if is_protected_dir "$dir_name"; then
            status="PROTECTED"
            protected_count=$((protected_count + 1))
        elif (( age_sec >= max_age_sec )); then
            status="STALE"
            stale_count=$((stale_count + 1))
            stale_total_kib=$((stale_total_kib + size_kib))
            stale_dirs+=("$dir_path")
        else
            active_count=$((active_count + 1))
        fi

        printf '%-40s %10s %-19s %s\n' \
            "$dir_name" \
            "$(format_size_kib "$size_kib")" \
            "$last_accessed" \
            "$status"
    done < <(find "$target_dir" -mindepth 1 -maxdepth 1 -type d -print | LC_ALL=C sort)

    if [[ "$force" == true ]] && (( stale_count > 0 )); then
        echo
        printf 'Deleting %s stale director%s...\n' \
            "$stale_count" \
            "$([[ "$stale_count" -eq 1 ]] && printf 'y' || printf 'ies')"
        local dir_path
        for dir_path in "${stale_dirs[@]}"; do
            rm -rf -- "$dir_path"
        done
    fi

    echo
    echo "Summary:"
    printf '  Scanned directories: %s\n' "$scanned_count"
    printf '  Protected: %s\n' "$protected_count"
    printf '  Active: %s\n' "$active_count"
    printf '  Stale: %s\n' "$stale_count"
    if [[ "$force" == true ]]; then
        printf '  Recovered: %s\n' "$(format_size_kib "$stale_total_kib")"
    else
        printf '  Would recover: %s\n' "$(format_size_kib "$stale_total_kib")"
        if (( stale_count > 0 )); then
            echo "  Run with --force to delete stale directories."
        fi
    fi

    if (( ${#protected_json_files[@]} > 0 )); then
        echo
        echo "Protected JSON files skipped:"
        local json_name
        for json_name in "${protected_json_files[@]}"; do
            printf '  %s\n' "$json_name"
        done
    fi
}

main "$@"
