# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Example test file demonstrating testing patterns for andrewdyates.  # template-ok

Run tests with:
    pytest tests/                    # Run all tests
    pytest tests/test_example.py    # Run this file
    pytest -v                        # Verbose output
    pytest -k "test_name"            # Run specific test

Test naming conventions:
    - test_<function>_<scenario>_<expected> - e.g., test_parse_empty_input_returns_none
    - Group related tests in classes: class Test<Feature>
"""

from __future__ import annotations

from pathlib import Path

import pytest


class TestExamplePatterns:
    """Demonstrates testing patterns - replace with real tests."""

    def test_basic_assertion(self):
        """Test with explicit expected value - never use 'assert True'."""
        result = 2 + 2
        assert result == 4, "Assertion failed: result == 4"

    def test_string_comparison(self):
        """String tests should check exact content."""
        text = "hello world"
        assert text.startswith("hello"), "Assertion failed: text.startswith(\"hello\")"
        assert "world" in text, "Assertion failed: \"world\" in text"
        assert len(text) == 11, "Assertion failed: len(text) == 11"

    def test_list_contents(self):
        """List tests should verify structure and content."""
        items = [1, 2, 3]
        assert len(items) == 3, "Assertion failed: len(items) == 3"
        assert items[0] == 1, "Assertion failed: items[0] == 1"
        assert 2 in items, "Assertion failed: 2 in items"

    def test_dict_structure(self):
        """Dict tests should verify keys and values."""
        data = {"name": "test", "value": 42}
        assert "name" in data, "Assertion failed: \"name\" in data"
        assert data["value"] == 42, "Assertion failed: data[\"value\"] == 42"
        assert len(data) == 2, "Assertion failed: len(data) == 2"

    def test_exception_handling(self):
        """Use pytest.raises for exception tests."""
        with pytest.raises(ValueError, match="invalid literal"):
            int("not a number")

    def test_file_exists(self, tmp_path):
        """Pytest provides tmp_path fixture for file tests."""
        test_file = tmp_path / "test.txt"
        test_file.write_text("content")
        assert test_file.exists(), f"Expected {test_file} to exist"
        assert test_file.read_text() == "content", "Assertion failed: test_file.read_text() == \"content\""


class TestProjectStructure:
    """Verify andrewdyates project structure exists."""  # template-ok

    def test_required_directories_exist(self):
        """Ensure standard directories are present."""
        root = Path(__file__).parent.parent
        assert (root / "tests").is_dir(), f"Expected {root / 'tests'} to be a directory"
        assert (root / ".AI Model").is_dir(), f"Expected {root / '.AI Model'} to be a directory"

    def test_required_files_exist(self):
        """Ensure standard files are present."""
        root = Path(__file__).parent.parent
        assert (root / "design doc").is_file(), f"Expected {root / 'design doc'} to be a file"
        assert (root / "ruff.toml").is_file(), f"Expected {root / 'ruff.toml'} to be a file"


def test_standalone_function():
    """Standalone tests work but classes group related tests better."""
    assert Path(__file__).suffix == ".py", "Assertion failed: Path(__file__).suffix == \".py\""
