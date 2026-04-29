# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

import importlib.util
import sys
from pathlib import Path


def _load_module():
    repo_root = Path(__file__).resolve().parent.parent
    script_path = repo_root / "scripts" / "rust_function_span_scan.py"
    module_name = "tla2_rust_function_span_scan"
    spec = importlib.util.spec_from_file_location(module_name, script_path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def test_parse_set_expr_fixture_span_is_correct():
    module = _load_module()
    fixture = (
        Path(__file__).resolve().parent
        / "fixtures"
        / "rust_function_span_scan"
        / "parse_set_expr_noise.rs"
    )
    spans = module.scan_file(fixture)
    parse_set_expr = next(span for span in spans if span.name == "parse_set_expr")
    assert parse_set_expr.lines == 15
    assert parse_set_expr.lines < 500


def test_trait_signature_without_body_is_ignored(tmp_path):
    module = _load_module()
    source = "\n".join(
        [
            "trait Demo {",
            "    fn declared(&self);",
            "    fn defaulted(&self) {",
            "        let _s = \"{\";",
            "    }",
            "}",
        ]
    )
    path = tmp_path / "trait_fixture.rs"
    path.write_text(source, encoding="utf-8")
    spans = module.scan_file(path)
    names = {span.name for span in spans}
    assert "defaulted" in names
    assert "declared" not in names


def test_unicode_char_literal_escape_does_not_affect_brace_depth(tmp_path):
    module = _load_module()
    source = "\n".join(
        [
            "impl Demo {",
            "    fn unicode_chars(&self) {",
            "        let _left = '\\u{7B}';",
            "        let _right = '\\u{7D}';",
            "    }",
            "",
            "    fn after(&self) {}",
            "}",
        ]
    )
    path = tmp_path / "unicode_char_fixture.rs"
    path.write_text(source, encoding="utf-8")
    spans = module.scan_file(path)
    spans_by_name = {span.name: span for span in spans}
    assert spans_by_name["unicode_chars"].lines == 4
    assert spans_by_name["after"].lines == 1


def test_raw_identifier_function_name_is_preserved(tmp_path):
    module = _load_module()
    source = "\n".join(
        [
            "impl Demo {",
            "    fn r#type(&self) {",
            "        let _s = \"{\";",
            "    }",
            "}",
        ]
    )
    path = tmp_path / "raw_identifier_fixture.rs"
    path.write_text(source, encoding="utf-8")
    spans = module.scan_file(path)
    span = next(s for s in spans if s.name == "r#type")
    assert span.lines == 3


def test_function_pointer_type_in_signature_does_not_hide_function(tmp_path):
    module = _load_module()
    source = "\n".join(
        [
            "impl Demo {",
            "    fn takes_fn_ptr(&self, f: fn(i32) -> i32) {",
            "        let _x = f(1);",
            "    }",
            "",
            "    fn after(&self) {}",
            "}",
        ]
    )
    path = tmp_path / "fn_pointer_signature_fixture.rs"
    path.write_text(source, encoding="utf-8")
    spans = module.scan_file(path)
    spans_by_name = {span.name: span for span in spans}
    assert spans_by_name["takes_fn_ptr"].lines == 3
    assert spans_by_name["after"].lines == 1


def test_braces_in_signature_const_expression_do_not_start_function_body(tmp_path):
    module = _load_module()
    source = "\n".join(
        [
            "impl Demo {",
            "    fn const_expr_arg(&self, _arr: [u8; { 1 + 2 }]) {",
            "        let _x = 1;",
            "    }",
            "",
            "    fn after(&self) {}",
            "}",
        ]
    )
    path = tmp_path / "const_expr_signature_fixture.rs"
    path.write_text(source, encoding="utf-8")
    spans = module.scan_file(path)
    spans_by_name = {span.name: span for span in spans}
    assert spans_by_name["const_expr_arg"].lines == 3
    assert spans_by_name["after"].lines == 1
