// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! HTTP server mode for the explore command.
//!
//! Wraps [`tla_check::InteractiveServer`] in a minimal HTTP/1.1 server.

use std::io::{BufRead, BufReader, Read as IoRead, Write as IoWrite};
use std::net::{TcpListener, TcpStream};

use anyhow::{bail, Context, Result};

use tla_check::InteractiveServer;

/// Run the HTTP explore server on the given port.
pub(crate) fn run_http_server(server: &mut InteractiveServer, port: u16) -> Result<()> {
    let addr = format!("127.0.0.1:{port}");
    let listener = TcpListener::bind(&addr)
        .with_context(|| format!("failed to bind HTTP server on {addr}"))?;
    eprintln!("Explore server listening on http://{addr}");
    eprintln!("Endpoints:");
    eprintln!("  POST /explore/init              -- compute initial states");
    eprintln!("  POST /explore/eval              -- evaluate expression in a state");
    eprintln!("  POST /explore/successors        -- compute successor states");
    eprintln!("  POST /explore/random-trace      -- generate a random trace");
    eprintln!("  POST /explore/mode              -- set exploration mode (concrete/symbolic)");
    eprintln!("  POST /explore/rollback          -- undo last symbolic transition");
    eprintln!("  POST /explore/assume-state      -- assert concrete variable values");
    eprintln!("  POST /explore/assume-transition -- assert action-level constraint");
    eprintln!("  POST /explore/next-model        -- get alternate satisfying assignment");
    eprintln!("  POST /explore/compact           -- compact solver state");
    eprintln!("  POST /explore/apply-in-order    -- apply transitions in sequence");
    eprintln!("  POST /explore/dispose           -- dispose spec and reset server");
    eprintln!("Press Ctrl-C to stop.");

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                if let Err(e) = handle_http_request(server, stream) {
                    eprintln!("HTTP request error: {e}");
                }
            }
            Err(e) => {
                eprintln!("Accept error: {e}");
            }
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Minimal HTTP request/response handling
// ---------------------------------------------------------------------------

struct HttpRequest {
    method: String,
    path: String,
    body: String,
}

fn parse_http_request(stream: &TcpStream) -> Result<HttpRequest> {
    let mut reader = BufReader::new(stream);

    let mut request_line = String::new();
    reader
        .read_line(&mut request_line)
        .context("read request line")?;
    let parts: Vec<&str> = request_line.trim().splitn(3, ' ').collect();
    if parts.len() < 2 {
        bail!("malformed HTTP request line: {request_line:?}");
    }
    let method = parts[0].to_string();
    let path = parts[1].to_string();

    let mut content_length: usize = 0;
    loop {
        let mut header_line = String::new();
        reader
            .read_line(&mut header_line)
            .context("read header line")?;
        let trimmed = header_line.trim();
        if trimmed.is_empty() {
            break;
        }
        if let Some(value) = trimmed.strip_prefix("Content-Length:") {
            content_length = value.trim().parse().unwrap_or(0);
        }
        if let Some(value) = trimmed.strip_prefix("content-length:") {
            content_length = value.trim().parse().unwrap_or(0);
        }
    }

    let mut body = vec![0u8; content_length];
    if content_length > 0 {
        reader.read_exact(&mut body).context("read request body")?;
    }
    let body_str = String::from_utf8_lossy(&body).to_string();

    Ok(HttpRequest {
        method,
        path,
        body: body_str,
    })
}

// TODO(#3751): Add gzip/zstd response compression when Accept-Encoding is present.
// The `flate2` (gzip) and `zstd` crates are not currently in workspace dependencies.
// When added, check the request's Accept-Encoding header and compress the response
// body accordingly, setting Content-Encoding in the response headers.
fn write_http_response(
    stream: &mut TcpStream,
    status: u16,
    status_text: &str,
    body: &[u8],
) -> std::io::Result<()> {
    let header = format!(
        "HTTP/1.1 {status} {status_text}\r\n\
         Content-Type: application/json\r\n\
         Content-Length: {}\r\n\
         Connection: close\r\n\
         \r\n",
        body.len()
    );
    stream.write_all(header.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

fn path_to_method(path: &str) -> Option<&'static str> {
    match path {
        "/explore/init" => Some("init"),
        "/explore/eval" => Some("eval"),
        "/explore/successors" => Some("step"),
        "/explore/random-trace" => Some("random_trace"),
        // Symbolic exploration endpoints (Part of #3751: Apalache Gap 3)
        "/explore/mode" => Some("set_mode"),
        "/explore/rollback" => Some("rollback"),
        "/explore/assume-state" => Some("assume_state"),
        "/explore/assume-transition" => Some("assume_transition"),
        "/explore/next-model" => Some("next_model"),
        "/explore/compact" => Some("compact"),
        "/explore/apply-in-order" => Some("apply_in_order"),
        "/explore/dispose" => Some("dispose"),
        _ => None,
    }
}

fn handle_http_request(server: &mut InteractiveServer, stream: TcpStream) -> Result<()> {
    let req = parse_http_request(&stream)?;
    let mut writer = stream;

    if req.method != "POST" {
        let err_body = serde_json::json!({
            "error": format!("method {} not allowed, use POST", req.method)
        });
        let body_bytes = serde_json::to_vec(&err_body)?;
        write_http_response(&mut writer, 405, "Method Not Allowed", &body_bytes)?;
        return Ok(());
    }

    let rpc_method = match path_to_method(&req.path) {
        Some(m) => m,
        None => {
            let err_body = serde_json::json!({
                "error": format!("unknown endpoint: {}", req.path)
            });
            let body_bytes = serde_json::to_vec(&err_body)?;
            write_http_response(&mut writer, 404, "Not Found", &body_bytes)?;
            return Ok(());
        }
    };

    let params: serde_json::Value = if req.body.trim().is_empty() {
        serde_json::json!({})
    } else {
        serde_json::from_str(&req.body).unwrap_or_else(|_| serde_json::json!({}))
    };

    match server.dispatch_http(rpc_method, params) {
        Ok(result) => {
            let body_bytes = serde_json::to_vec(&result)?;
            write_http_response(&mut writer, 200, "OK", &body_bytes)?;
        }
        Err(msg) => {
            let err_body = serde_json::json!({"error": msg});
            let body_bytes = serde_json::to_vec(&err_body)?;
            write_http_response(&mut writer, 500, "Internal Server Error", &body_bytes)?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::TcpListener;
    use std::sync::Arc;

    #[test]
    fn test_path_to_method_known_endpoints() {
        assert_eq!(path_to_method("/explore/init"), Some("init"));
        assert_eq!(path_to_method("/explore/eval"), Some("eval"));
        assert_eq!(path_to_method("/explore/successors"), Some("step"));
        assert_eq!(
            path_to_method("/explore/random-trace"),
            Some("random_trace")
        );
    }

    #[test]
    fn test_path_to_method_symbolic_endpoints() {
        assert_eq!(path_to_method("/explore/mode"), Some("set_mode"));
        assert_eq!(path_to_method("/explore/rollback"), Some("rollback"));
        assert_eq!(
            path_to_method("/explore/assume-state"),
            Some("assume_state")
        );
        assert_eq!(
            path_to_method("/explore/assume-transition"),
            Some("assume_transition")
        );
        assert_eq!(path_to_method("/explore/next-model"), Some("next_model"));
        assert_eq!(path_to_method("/explore/compact"), Some("compact"));
        assert_eq!(
            path_to_method("/explore/apply-in-order"),
            Some("apply_in_order")
        );
        assert_eq!(path_to_method("/explore/dispose"), Some("dispose"));
    }

    #[test]
    fn test_path_to_method_unknown() {
        assert_eq!(path_to_method("/explore/unknown"), None);
        assert_eq!(path_to_method("/foo"), None);
        assert_eq!(path_to_method(""), None);
    }

    #[test]
    fn test_explore_init_round_trip() {
        use std::io::{Read as _, Write as _};

        let src = r#"---- MODULE TestExplore ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ x < 3
===="#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let result = tla_core::lower(tla_core::FileId(0), &tree);
        let module = Arc::new(result.module.expect("lower should succeed"));
        let config = tla_check::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut server = InteractiveServer::new(module, config);

        let listener = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral port");
        let port = listener.local_addr().expect("local addr").port();

        let handle = std::thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept");
            handle_http_request(&mut server, stream).expect("handle");
            server
        });

        let mut client = TcpStream::connect(format!("127.0.0.1:{port}")).expect("connect");
        let req = "POST /explore/init HTTP/1.1\r\n\
                   Host: localhost\r\n\
                   Content-Length: 2\r\n\
                   \r\n\
                   {}";
        client.write_all(req.as_bytes()).expect("write");
        client.flush().expect("flush");

        let mut response = String::new();
        client.read_to_string(&mut response).expect("read");

        assert!(
            response.starts_with("HTTP/1.1 200 OK"),
            "expected 200 OK, got: {response}"
        );
        let body_start = response.find("\r\n\r\n").expect("find body") + 4;
        let body = &response[body_start..];
        let parsed: serde_json::Value = serde_json::from_str(body).expect("parse JSON body");
        let arr = parsed.as_array().expect("result should be array");
        assert_eq!(arr.len(), 1, "Init == x = 0 should produce exactly 1 state");
        assert_eq!(arr[0]["variables"]["x"], serde_json::json!(0));
        assert!(arr[0]["state_id"].is_u64());

        let _server = handle.join().expect("server thread");
    }

    #[test]
    fn test_explore_successors_round_trip() {
        use std::io::{Read as _, Write as _};

        let src = r#"---- MODULE TestSucc ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ x < 2
===="#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let result = tla_core::lower(tla_core::FileId(0), &tree);
        let module = Arc::new(result.module.expect("lower should succeed"));
        let config = tla_check::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut server = InteractiveServer::new(module, config);

        let init_result = server
            .dispatch_http("init", serde_json::json!({}))
            .expect("init should succeed");
        let states: Vec<tla_check::StateSnapshot> =
            serde_json::from_value(init_result).expect("parse init states");
        assert_eq!(states.len(), 1);
        let state_id = states[0].state_id;

        let listener = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral port");
        let port = listener.local_addr().expect("local addr").port();

        let handle = std::thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept");
            handle_http_request(&mut server, stream).expect("handle");
            server
        });

        let body = format!("{{\"state_id\": {state_id}}}");
        let req = format!(
            "POST /explore/successors HTTP/1.1\r\n\
             Host: localhost\r\n\
             Content-Length: {}\r\n\
             \r\n\
             {}",
            body.len(),
            body
        );
        let mut client = TcpStream::connect(format!("127.0.0.1:{port}")).expect("connect");
        client.write_all(req.as_bytes()).expect("write");
        client.flush().expect("flush");

        let mut response = String::new();
        client.read_to_string(&mut response).expect("read");
        assert!(
            response.starts_with("HTTP/1.1 200 OK"),
            "expected 200 OK, got: {response}"
        );

        let body_start = response.find("\r\n\r\n").expect("find body") + 4;
        let body = &response[body_start..];
        let parsed: serde_json::Value = serde_json::from_str(body).expect("parse JSON body");
        let arr = parsed.as_array().expect("result should be array");
        assert_eq!(arr.len(), 1, "should have 1 successor from x=0");
        assert_eq!(arr[0]["variables"]["x"], serde_json::json!(1));

        let _server = handle.join().expect("server thread");
    }

    #[test]
    fn test_explore_eval_round_trip() {
        let src = r#"---- MODULE TestEval ----
VARIABLE x
Init == x = 5
Next == x' = x
===="#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let result = tla_core::lower(tla_core::FileId(0), &tree);
        let module = Arc::new(result.module.expect("lower should succeed"));
        let config = tla_check::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut server = InteractiveServer::new(module, config);

        let init_result = server
            .dispatch_http("init", serde_json::json!({}))
            .expect("init");
        let states: Vec<tla_check::StateSnapshot> =
            serde_json::from_value(init_result).expect("parse");
        let state_id = states[0].state_id;

        let eval_result = server
            .dispatch_http(
                "eval",
                serde_json::json!({"state_id": state_id, "expr": "x + 10"}),
            )
            .expect("eval");
        assert_eq!(eval_result, serde_json::json!(15));
    }

    #[test]
    fn test_explore_random_trace() {
        let src = r#"---- MODULE TestTrace ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ x < 5
===="#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let result = tla_core::lower(tla_core::FileId(0), &tree);
        let module = Arc::new(result.module.expect("lower should succeed"));
        let config = tla_check::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut server = InteractiveServer::new(module, config);

        let trace_result = server
            .dispatch_http("random_trace", serde_json::json!({"steps": 10}))
            .expect("random_trace");
        let trace: Vec<tla_check::StateSnapshot> =
            serde_json::from_value(trace_result).expect("parse trace");

        assert_eq!(trace.len(), 6, "trace should be 6 states (deadlock at x=5)");
        assert_eq!(trace[0].variables["x"], serde_json::json!(0));
        assert_eq!(trace[5].variables["x"], serde_json::json!(5));
    }

    #[test]
    fn test_explore_unknown_endpoint_404() {
        use std::io::{Read as _, Write as _};

        let src = r#"---- MODULE Test404 ----
VARIABLE x
Init == x = 0
Next == x' = x
===="#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let result = tla_core::lower(tla_core::FileId(0), &tree);
        let module = Arc::new(result.module.expect("lower should succeed"));
        let config = tla_check::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut server = InteractiveServer::new(module, config);

        let listener = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral port");
        let port = listener.local_addr().expect("local addr").port();

        let handle = std::thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept");
            handle_http_request(&mut server, stream).expect("handle");
        });

        let req = "POST /explore/bogus HTTP/1.1\r\n\
                   Host: localhost\r\n\
                   Content-Length: 2\r\n\
                   \r\n\
                   {}";
        let mut client = TcpStream::connect(format!("127.0.0.1:{port}")).expect("connect");
        client.write_all(req.as_bytes()).expect("write");
        client.flush().expect("flush");

        let mut response = String::new();
        client.read_to_string(&mut response).expect("read");
        assert!(
            response.starts_with("HTTP/1.1 404 Not Found"),
            "expected 404, got: {response}"
        );

        handle.join().expect("server thread");
    }
}
