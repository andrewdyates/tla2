// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capture machine and build environment for reproducible benchmarking.
//!
//! Every results.json includes an `environment` block so that scores can be
//! compared across machines with full context on hardware and load.

use serde::Serialize;
use std::path::Path;
use std::process::Command;

#[derive(Debug, Serialize)]
pub(crate) struct Environment {
    pub timestamp: String,
    pub git_commit: String,
    pub git_dirty: bool,
    pub z4_version: String,
    pub hostname: String,
    pub os: &'static str,
    pub arch: &'static str,
    pub cpu_model: String,
    pub cpu_count: u32,
    pub memory_bytes: u64,
    pub load_avg: [f64; 3],
}

impl Environment {
    /// Capture current environment. Call once at the start of a benchmark run.
    pub fn capture(z4_path: &Path) -> Self {
        Self {
            timestamp: Self::now_utc(),
            git_commit: Self::git_commit(),
            git_dirty: Self::git_dirty(),
            z4_version: Self::z4_version(z4_path),
            hostname: Self::hostname(),
            os: std::env::consts::OS,
            arch: std::env::consts::ARCH,
            cpu_model: Self::cpu_model(),
            cpu_count: Self::cpu_count(),
            memory_bytes: Self::memory_bytes(),
            load_avg: Self::load_avg(),
        }
    }

    fn now_utc() -> String {
        cmd_stdout("date", &["-u", "+%Y-%m-%dT%H:%M:%SZ"])
            .unwrap_or_else(|| "unknown".to_string())
    }

    fn git_commit() -> String {
        cmd_stdout("git", &["rev-parse", "--short", "HEAD"])
            .unwrap_or_else(|| "unknown".to_string())
    }

    fn git_dirty() -> bool {
        cmd_stdout("git", &["status", "--porcelain"])
            .map(|s| !s.is_empty())
            .unwrap_or(false)
    }

    fn z4_version(z4_path: &Path) -> String {
        let path_str = z4_path.to_string_lossy();
        Command::new(z4_path)
            .arg("--version")
            .output()
            .ok()
            .and_then(|o| String::from_utf8(o.stdout).ok())
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|| format!("unknown ({})", path_str))
    }

    fn hostname() -> String {
        cmd_stdout("hostname", &[]).unwrap_or_else(|| "unknown".to_string())
    }

    #[cfg(target_os = "macos")]
    fn cpu_model() -> String {
        cmd_stdout("sysctl", &["-n", "machdep.cpu.brand_string"])
            .unwrap_or_else(|| "unknown".to_string())
    }

    #[cfg(not(target_os = "macos"))]
    fn cpu_model() -> String {
        // Linux: parse /proc/cpuinfo
        std::fs::read_to_string("/proc/cpuinfo")
            .ok()
            .and_then(|text| {
                text.lines()
                    .find(|l| l.starts_with("model name"))
                    .and_then(|l| l.split(':').nth(1))
                    .map(|s| s.trim().to_string())
            })
            .unwrap_or_else(|| "unknown".to_string())
    }

    #[cfg(target_os = "macos")]
    fn cpu_count() -> u32 {
        cmd_stdout("sysctl", &["-n", "hw.logicalcpu"])
            .and_then(|s| s.parse().ok())
            .unwrap_or(0)
    }

    #[cfg(not(target_os = "macos"))]
    fn cpu_count() -> u32 {
        std::fs::read_to_string("/proc/cpuinfo")
            .ok()
            .map(|text| text.lines().filter(|l| l.starts_with("processor")).count() as u32)
            .unwrap_or(0)
    }

    #[cfg(target_os = "macos")]
    fn memory_bytes() -> u64 {
        cmd_stdout("sysctl", &["-n", "hw.memsize"])
            .and_then(|s| s.parse().ok())
            .unwrap_or(0)
    }

    #[cfg(not(target_os = "macos"))]
    fn memory_bytes() -> u64 {
        // Linux: parse MemTotal from /proc/meminfo (in kB)
        std::fs::read_to_string("/proc/meminfo")
            .ok()
            .and_then(|text| {
                text.lines()
                    .find(|l| l.starts_with("MemTotal:"))
                    .and_then(|l| {
                        l.split_whitespace().nth(1).and_then(|s| s.parse::<u64>().ok())
                    })
            })
            .map(|kb| kb * 1024)
            .unwrap_or(0)
    }

    fn load_avg() -> [f64; 3] {
        // Parse from `uptime` output — works on macOS and Linux
        cmd_stdout("uptime", &[])
            .and_then(|s| {
                // "... load averages: 2.50 3.10 2.80" (macOS)
                // "... load average: 2.50, 3.10, 2.80" (Linux)
                let after = s.split("load average").last()?;
                let nums: Vec<f64> = after
                    .split(|c: char| !c.is_ascii_digit() && c != '.')
                    .filter_map(|tok| tok.parse().ok())
                    .collect();
                if nums.len() >= 3 {
                    Some([nums[0], nums[1], nums[2]])
                } else {
                    None
                }
            })
            .unwrap_or([0.0; 3])
    }
}

fn cmd_stdout(program: &str, args: &[&str]) -> Option<String> {
    Command::new(program)
        .args(args)
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
}

impl std::fmt::Display for Environment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mem_gb = self.memory_bytes as f64 / (1024.0 * 1024.0 * 1024.0);
        write!(
            f,
            "{} | {} {} | {} ({} cores, {:.0} GB) | load {:.1}/{:.1}/{:.1} | z4 {} | {}{}",
            self.timestamp,
            self.os,
            self.arch,
            self.cpu_model,
            self.cpu_count,
            mem_gb,
            self.load_avg[0],
            self.load_avg[1],
            self.load_avg[2],
            self.z4_version,
            self.git_commit,
            if self.git_dirty { " (dirty)" } else { "" },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_capture_does_not_panic() {
        let env = Environment::capture(&PathBuf::from("/nonexistent/z4"));
        assert!(!env.timestamp.is_empty());
        assert!(!env.os.is_empty());
        assert!(!env.arch.is_empty());
    }

    #[test]
    fn test_display() {
        let env = Environment::capture(&PathBuf::from("/nonexistent/z4"));
        let s = format!("{env}");
        assert!(s.contains(env.os));
    }
}
