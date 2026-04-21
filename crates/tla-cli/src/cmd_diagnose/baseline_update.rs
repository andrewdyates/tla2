// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use anyhow::{bail, Context, Result};
use sha2::{Digest, Sha256};

use super::types::{SpecResult, SpecVerdict};

pub(super) fn update_baseline_file(
    baseline_path: &std::path::Path,
    baseline_text: &str,
    results: &[SpecResult],
) -> Result<()> {
    // Read-modify-write on raw JSON to preserve fields our struct doesn't model.
    let raw: serde_json::Value =
        serde_json::from_str(baseline_text).context("re-parse baseline as Value")?;
    let refreshed = refresh_baseline_value(raw, results)?;
    let updated = serde_json::to_string_pretty(&refreshed)?;
    std::fs::write(baseline_path, format!("{updated}\n"))
        .with_context(|| format!("write baseline {}", baseline_path.display()))?;
    Ok(())
}

pub(super) fn refresh_baseline_value(
    mut raw: serde_json::Value,
    results: &[SpecResult],
) -> Result<serde_json::Value> {
    let now = chrono::Utc::now().to_rfc3339();
    let git_commit = option_env!("TLA2_GIT_COMMIT")
        .unwrap_or("unknown")
        .to_string();
    let Some(root_obj) = raw.as_object_mut() else {
        bail!("baseline root is not an object");
    };

    let (stats, specs_digest, specs_updated) = {
        let Some(specs_obj) = root_obj.get_mut("specs").and_then(|v| v.as_object_mut()) else {
            bail!("baseline has no 'specs' object");
        };

        let mut specs_updated = 0usize;
        for result in results {
            if result.verdict == SpecVerdict::Skip {
                continue;
            }
            let Some(entry) = specs_obj.get_mut(&result.name) else {
                continue;
            };
            specs_updated += 1;
            if let Some(tla2_obj) = entry
                .get_mut("tla2")
                .and_then(|value| value.as_object_mut())
            {
                tla2_obj.insert(
                    "status".into(),
                    serde_json::Value::String(baseline_status(result.verdict).into()),
                );
                tla2_obj.insert(
                    "states".into(),
                    match result.tla2_states {
                        Some(states) => serde_json::json!(states),
                        None => serde_json::Value::Null,
                    },
                );
                tla2_obj.insert(
                    "error_type".into(),
                    match &result.error_details {
                        Some(details) => serde_json::Value::String(details.clone()),
                        None => serde_json::Value::Null,
                    },
                );
                tla2_obj.insert("last_run".into(), serde_json::Value::String(now.clone()));
                tla2_obj.insert(
                    "git_commit".into(),
                    serde_json::Value::String(git_commit.clone()),
                );
            }
            if let Some(entry_obj) = entry.as_object_mut() {
                entry_obj.insert(
                    "verified_match".into(),
                    serde_json::Value::Bool(matches!(
                        result.verdict,
                        SpecVerdict::Pass | SpecVerdict::FlakyTimeout
                    )),
                );
            }
        }

        let stats = compute_baseline_stats(specs_obj);
        let specs_digest = sha256_jcs_value(&serde_json::Value::Object(specs_obj.clone()))?;
        (stats, specs_digest, specs_updated)
    };

    root_obj.insert("stats".into(), serde_json::Value::Object(stats));
    root_obj.insert(
        "specs_jcs_sha256".into(),
        serde_json::Value::String(specs_digest),
    );
    root_obj.insert(
        "tla2_refresh".into(),
        serde_json::Value::Object(build_tla2_refresh(
            &git_commit,
            &now,
            results.len(),
            specs_updated,
        )),
    );

    Ok(raw)
}

pub(super) fn sha256_jcs_value(value: &serde_json::Value) -> Result<String> {
    let mut canonical = String::new();
    write_canonical_json(value, &mut canonical)?;
    let mut hasher = Sha256::new();
    hasher.update(canonical.as_bytes());
    Ok(format!("{:x}", hasher.finalize()))
}

fn canonicalize_number(number: &serde_json::Number) -> Result<String> {
    if let Some(value) = number.as_i64() {
        return Ok(value.to_string());
    }
    if let Some(value) = number.as_u64() {
        return Ok(value.to_string());
    }
    if let Some(value) = number.as_f64() {
        return format_float_jcs(value);
    }
    bail!("unsupported JSON number for canonicalization: {number}");
}

fn format_float_jcs(value: f64) -> Result<String> {
    if !value.is_finite() {
        bail!("non-finite float not allowed in canonical JSON: {value:?}");
    }
    if value == 0.0 {
        return Ok("0".to_string());
    }

    let mut formatted = format!("{value:?}");
    if let Some(exp_index) = formatted.find(['e', 'E']) {
        let mantissa = formatted[..exp_index].to_string();
        let exponent = &formatted[exp_index + 1..];
        let (sign, digits) = match exponent.as_bytes().first().copied() {
            Some(b'+') => ("+", &exponent[1..]),
            Some(b'-') => ("-", &exponent[1..]),
            _ => ("", exponent),
        };
        let digits = digits.trim_start_matches('0');
        let digits = if digits.is_empty() { "0" } else { digits };
        return Ok(format!("{mantissa}e{sign}{digits}"));
    }

    if formatted.contains('.') {
        while formatted.ends_with('0') {
            formatted.pop();
        }
        if formatted.ends_with('.') {
            formatted.pop();
        }
    }
    Ok(formatted)
}

fn baseline_status(verdict: SpecVerdict) -> &'static str {
    match verdict {
        SpecVerdict::Pass | SpecVerdict::FlakyTimeout => "pass",
        SpecVerdict::ExpectedMismatch | SpecVerdict::StateMismatch => "mismatch",
        _ => "fail",
    }
}

fn build_tla2_refresh(
    git_commit: &str,
    timestamp: &str,
    specs_ran: usize,
    specs_updated: usize,
) -> serde_json::Map<String, serde_json::Value> {
    let mut refresh = serde_json::Map::new();
    refresh.insert(
        "git_commit".into(),
        serde_json::Value::String(git_commit.to_string()),
    );
    refresh.insert(
        "script".into(),
        serde_json::Value::String("tla2 diagnose --update-baseline".to_string()),
    );
    refresh.insert("specs_ran".into(), serde_json::json!(specs_ran));
    refresh.insert("specs_updated".into(), serde_json::json!(specs_updated));
    refresh.insert(
        "timestamp".into(),
        serde_json::Value::String(timestamp.to_string()),
    );
    refresh
}

fn compute_baseline_stats(
    specs_obj: &serde_json::Map<String, serde_json::Value>,
) -> serde_json::Map<String, serde_json::Value> {
    let mut tlc_pass = 0usize;
    let mut tlc_timeout = 0usize;
    let mut tlc_error = 0usize;
    let mut tla2_match = 0usize;
    let mut tla2_mismatch = 0usize;
    let mut tla2_fail = 0usize;
    let mut tla2_untested = 0usize;

    for spec in specs_obj.values() {
        let tlc_status = spec
            .get("tlc")
            .and_then(|tlc| tlc.get("status"))
            .and_then(serde_json::Value::as_str)
            .or_else(|| spec.get("status").and_then(serde_json::Value::as_str))
            .unwrap_or("unknown");
        match tlc_status {
            "pass" => tlc_pass += 1,
            "timeout" => tlc_timeout += 1,
            _ => tlc_error += 1,
        }

        let Some(tla2) = spec.get("tla2").and_then(serde_json::Value::as_object) else {
            tla2_untested += 1;
            continue;
        };

        let tla2_status = tla2
            .get("status")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("untested");
        let verified_match = spec
            .get("verified_match")
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false);
        match tla2_status {
            "pass" if verified_match => tla2_match += 1,
            "mismatch" => tla2_mismatch += 1,
            "fail" => tla2_fail += 1,
            _ => tla2_untested += 1,
        }
    }

    let mut stats = serde_json::Map::new();
    stats.insert("tla2_fail".into(), serde_json::json!(tla2_fail));
    stats.insert("tla2_match".into(), serde_json::json!(tla2_match));
    stats.insert("tla2_mismatch".into(), serde_json::json!(tla2_mismatch));
    stats.insert("tla2_untested".into(), serde_json::json!(tla2_untested));
    stats.insert("tlc_error".into(), serde_json::json!(tlc_error));
    stats.insert("tlc_pass".into(), serde_json::json!(tlc_pass));
    stats.insert("tlc_timeout".into(), serde_json::json!(tlc_timeout));
    stats
}

fn write_canonical_json(value: &serde_json::Value, out: &mut String) -> Result<()> {
    match value {
        serde_json::Value::Null => out.push_str("null"),
        serde_json::Value::Bool(true) => out.push_str("true"),
        serde_json::Value::Bool(false) => out.push_str("false"),
        serde_json::Value::Number(number) => out.push_str(&canonicalize_number(number)?),
        serde_json::Value::String(text) => out.push_str(&serde_json::to_string(text)?),
        serde_json::Value::Array(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_canonical_json(item, out)?;
            }
            out.push(']');
        }
        serde_json::Value::Object(map) => {
            let mut entries: Vec<_> = map.iter().collect();
            entries.sort_by(|(left, _), (right, _)| left.cmp(right));
            out.push('{');
            for (index, (key, item)) in entries.into_iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                out.push_str(&serde_json::to_string(key)?);
                out.push(':');
                write_canonical_json(item, out)?;
            }
            out.push('}');
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "update_baseline_tests.rs"]
mod update_baseline_tests;
