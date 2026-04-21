// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[allow(dead_code)]
static TEMP_COUNTER: AtomicUsize = AtomicUsize::new(0);

#[allow(dead_code)]
pub struct TempDir {
    pub path: PathBuf,
}

impl TempDir {
    #[allow(dead_code)]
    pub fn new(prefix: &str) -> Self {
        let n = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let now_ns = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("time went backwards")
            .as_nanos();

        let path = std::env::temp_dir().join(format!(
            "{prefix}-{pid}-{n}-{now_ns}",
            pid = std::process::id()
        ));
        std::fs::create_dir_all(&path).expect("create temp dir");
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// Write bytes to a file, creating parent directories as needed.
#[allow(dead_code)]
pub fn write_file(path: &Path, bytes: &[u8]) {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create temp dir");
    }
    std::fs::write(path, bytes).expect("write temp file");
}

/// Write a TLA+ spec and config to a temp dir, returning both paths.
#[allow(dead_code)]
pub fn write_spec_and_config(
    dir: &TempDir,
    module_name: &str,
    spec: &str,
    cfg: &str,
) -> (PathBuf, PathBuf) {
    let spec_path = dir.path.join(format!("{module_name}.tla"));
    let cfg_path = dir.path.join(format!("{module_name}.cfg"));
    std::fs::write(&spec_path, spec).expect("write spec");
    std::fs::write(&cfg_path, cfg).expect("write cfg");
    (spec_path, cfg_path)
}

/// Run the tla2 binary with the given arguments and return raw output.
#[allow(dead_code)]
pub fn run_tla(args: &[&str]) -> Output {
    run_tla_with_env(args, &[])
}

/// Run the tla2 binary with custom environment variables.
#[allow(dead_code)]
pub fn run_tla_with_env(args: &[&str], env: &[(&str, &str)]) -> Output {
    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.args(args);
    for (k, v) in env {
        cmd.env(k, v);
    }
    cmd.output().expect("failed to execute tla2")
}

/// Run the tla2 binary with a specific timeout and return raw output.
#[allow(dead_code)]
pub fn run_tla_with_timeout(args: &[&str], timeout: Duration) -> Output {
    run_tla_with_env_timeout(args, &[], timeout)
}

/// Run the tla2 binary with custom environment variables and a specific timeout.
#[allow(dead_code)]
pub fn run_tla_with_env_timeout(args: &[&str], env: &[(&str, &str)], timeout: Duration) -> Output {
    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (k, v) in env {
        cmd.env(k, v);
    }
    run_command_with_timeout(cmd, args, timeout)
}

/// Run the tla2 binary and return (exit_code, stdout, stderr).
#[allow(dead_code)]
pub fn run_tla_parsed(args: &[&str]) -> (i32, String, String) {
    run_tla_parsed_with_env(args, &[], &[])
}

/// Run the tla2 binary with a specific timeout and return (exit_code, stdout, stderr).
#[allow(dead_code)]
pub fn run_tla_parsed_with_timeout(args: &[&str], timeout: Duration) -> (i32, String, String) {
    run_tla_parsed_with_env_timeout(args, &[], &[], timeout)
}

/// Run the tla2 binary with env vars and env removals, return (exit_code, stdout, stderr).
/// env_remove is applied first, then env vars are set (so env can override removals).
#[allow(dead_code)]
pub fn run_tla_parsed_with_env(
    args: &[&str],
    env: &[(&str, &str)],
    env_remove: &[&str],
) -> (i32, String, String) {
    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.args(args);
    for k in env_remove {
        cmd.env_remove(k);
    }
    for (k, v) in env {
        cmd.env(k, v);
    }
    let output = cmd.output().expect("failed to execute tla2");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

/// Run the tla2 binary with env vars, env removals, and a specific timeout.
#[allow(dead_code)]
pub fn run_tla_parsed_with_env_timeout(
    args: &[&str],
    env: &[(&str, &str)],
    env_remove: &[&str],
    timeout: Duration,
) -> (i32, String, String) {
    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for k in env_remove {
        cmd.env_remove(k);
    }
    for (k, v) in env {
        cmd.env(k, v);
    }
    let output = run_command_with_timeout(cmd, args, timeout);
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

fn run_command_with_timeout(mut cmd: Command, args: &[&str], timeout: Duration) -> Output {
    let mut child = cmd.spawn().expect("failed to execute tla2");
    let mut out = child.stdout.take().expect("stdout is piped");
    let mut err = child.stderr.take().expect("stderr is piped");

    let stdout_reader = thread::spawn(move || -> std::io::Result<Vec<u8>> {
        let mut bytes = Vec::new();
        out.read_to_end(&mut bytes)?;
        Ok(bytes)
    });
    let stderr_reader = thread::spawn(move || -> std::io::Result<Vec<u8>> {
        let mut bytes = Vec::new();
        err.read_to_end(&mut bytes)?;
        Ok(bytes)
    });

    let start = Instant::now();
    loop {
        if start.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            let stdout = stdout_reader
                .join()
                .expect("join stdout reader")
                .unwrap_or_default();
            let stderr = stderr_reader
                .join()
                .expect("join stderr reader")
                .unwrap_or_default();
            panic!(
                "tla2 subprocess timed out after {timeout:?}: {args:?}\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&stdout),
                String::from_utf8_lossy(&stderr)
            );
        }

        if let Some(status) = child.try_wait().expect("try_wait on tla2") {
            let stdout = stdout_reader
                .join()
                .expect("join stdout reader")
                .expect("read stdout");
            let stderr = stderr_reader
                .join()
                .expect("join stderr reader")
                .expect("read stderr");
            return Output {
                status,
                stdout,
                stderr,
            };
        }

        thread::sleep(Duration::from_millis(5));
    }
}
