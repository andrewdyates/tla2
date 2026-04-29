#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""
Andrew Yates <andrewyates.name@gmail.com>

REST-based `gh issue list` fallback.

Why this exists:
- `gh issue list` uses GitHub GraphQL and can fail when GraphQL quota is exhausted.
- GitHub REST endpoints typically remain available; this script lists issues via REST.

Examples:
  ./scripts/gh_issue_list_rest.py --label needs-review
  ./scripts/gh_issue_list_rest.py --label blocked --state open --limit 200
  ./scripts/gh_issue_list_rest.py --state open --json number,title,labels
  ./scripts/gh_issue_list_rest.py --search "label:needs-review state:open"
  ./scripts/gh_issue_list_rest.py --search "repo:andrewdyates/tla2 state:open tlc"
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from typing import Any, Iterable


def _run(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, check=False, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def _die(msg: str) -> "None":
    print(f"error: {msg}", file=sys.stderr)
    raise SystemExit(2)


def _format_gh_api_failure(*, repo: str, stderr: str, stdout: str) -> str:
    blob = "\n".join([stderr.strip(), stdout.strip()]).strip()
    lower = blob.lower()

    # GitHub commonly returns 404 for private resources when the token isn't
    # authorized for the org (SAML SSO) or lacks permissions.
    if "resource protected by organization saml enforcement" in lower:
        return (
            "GitHub API access blocked by org SAML enforcement.\n"
            "Fix: `gh auth refresh` and complete the SSO flow, then retry."
        )

    if "api rate limit exceeded" in lower or "rate limit" in lower:
        return (
            "GitHub API rate limit exceeded.\n"
            "Fix: wait for quotas to reset, or reduce `gh` calls. See: docs/github_cli_rate_limits.md"
        )

    if "not found" in lower and ("http 404" in lower or "\"status\": \"404\"" in lower or "\"status\":404" in lower):
        return (
            f"GitHub API returned 404 Not Found for repo {repo!r}.\n"
            "This often means the repo is private or your token isn't authorized for the org via SSO.\n"
            "Fix: `gh auth status` then `gh auth refresh` (complete SSO), then retry."
        )

    if blob:
        return blob
    return "gh api failed (no stderr)"


def _parse_owner_repo(remote_url: str) -> str | None:
    url = remote_url.strip()

    m = re.match(r"^git@github\.com:(?P<path>.+)$", url)
    if m:
        path = m.group("path")
    else:
        m = re.match(r"^ssh://git@github\.com/(?P<path>.+)$", url)
        if m:
            path = m.group("path")
        else:
            m = re.match(r"^https://github\.com/(?P<path>.+)$", url)
            if not m:
                return None
            path = m.group("path")

    path = path.rstrip("/")
    if path.endswith(".git"):
        path = path[: -len(".git")]

    if path.count("/") != 1:
        return None
    return path


def _default_repo() -> str | None:
    env_repo = os.environ.get("GITHUB_REPOSITORY")
    if env_repo and env_repo.count("/") == 1:
        return env_repo

    r = _run(["git", "remote", "get-url", "origin"])
    if r.returncode != 0:
        return None

    return _parse_owner_repo(r.stdout)


def _parse_search(search: str) -> tuple[str | None, str | None, list[str], list[str]]:
    """Parse a small subset of GitHub search syntax.

    Supported tokens:
      - repo:owner/repo
      - label:NAME (repeatable)
      - state:open|closed|all
      - is:open|closed

    Everything else is treated as a case-insensitive substring filter on the issue title.
    """
    repo: str | None = None
    state: str | None = None
    labels: list[str] = []
    terms: list[str] = []

    for raw in (search or "").split():
        tok = raw.strip()
        if not tok:
            continue

        if tok.startswith("repo:"):
            v = tok[len("repo:") :]
            if v.count("/") == 1:
                repo = v
            else:
                _die(f"unsupported repo token in --search: {tok}")
            continue

        if tok.startswith("label:"):
            v = tok[len("label:") :].strip()
            if not v:
                _die(f"empty label token in --search: {tok}")
            labels.append(v)
            continue

        if tok.startswith("state:"):
            v = tok[len("state:") :].strip()
            if v not in ("open", "closed", "all"):
                _die(f"unsupported state token in --search: {tok}")
            state = v
            continue

        if tok.startswith("is:"):
            v = tok[len("is:") :].strip()
            if v in ("open", "closed"):
                state = v
                continue

        terms.append(tok)

    return repo, state, labels, terms


def _issue_matches_terms(issue: dict[str, Any], terms: list[str]) -> bool:
    if not terms:
        return True
    title = issue.get("title")
    if not isinstance(title, str):
        return False
    lower = title.lower()
    return all(t.lower() in lower for t in terms)


def _gh_api_issues_page(
    *,
    repo: str,
    state: str,
    labels: list[str],
    per_page: int,
    page: int,
) -> list[dict[str, Any]]:
    cmd = [
        "gh",
        "api",
        "--method",
        "GET",
        f"/repos/{repo}/issues",
        "-f",
        f"state={state}",
        "-f",
        f"per_page={per_page}",
        "-f",
        f"page={page}",
    ]
    if labels:
        cmd += ["-f", f"labels={','.join(labels)}"]

    r = _run(cmd)
    if r.returncode != 0:
        _die(_format_gh_api_failure(repo=repo, stderr=r.stderr, stdout=r.stdout))
    try:
        data = json.loads(r.stdout)
    except json.JSONDecodeError as e:
        _die(f"invalid JSON from gh api: {e}")

    if not isinstance(data, list):
        _die(f"unexpected response type from /issues: {type(data).__name__}")
    return data


def _iter_issues(
    *,
    repo: str,
    state: str,
    labels: list[str],
    limit: int,
    include_prs: bool,
) -> Iterable[dict[str, Any]]:
    per_page = min(100, max(1, limit))
    page = 1
    seen = 0
    while seen < limit:
        batch = _gh_api_issues_page(
            repo=repo, state=state, labels=labels, per_page=per_page, page=page
        )
        if not batch:
            return
        page += 1
        for issue in batch:
            if not include_prs and isinstance(issue, dict) and "pull_request" in issue:
                continue
            yield issue
            seen += 1
            if seen >= limit:
                return


def _as_labels(issue: dict[str, Any]) -> list[str]:
    labels = issue.get("labels", [])
    if not isinstance(labels, list):
        return []
    out: list[str] = []
    for l in labels:
        if isinstance(l, dict) and isinstance(l.get("name"), str):
            out.append(l["name"])
    return out


def _select_fields(issue: dict[str, Any], fields: list[str]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for f in fields:
        if f == "number":
            out["number"] = issue.get("number")
        elif f == "title":
            out["title"] = issue.get("title")
        elif f == "url":
            out["url"] = issue.get("html_url")
        elif f == "state":
            out["state"] = issue.get("state")
        elif f == "labels":
            out["labels"] = _as_labels(issue)
        elif f == "author":
            user = issue.get("user", {})
            out["author"] = user.get("login") if isinstance(user, dict) else None
        elif f == "assignees":
            assignees = issue.get("assignees", [])
            if isinstance(assignees, list):
                out["assignees"] = [
                    a.get("login") for a in assignees if isinstance(a, dict) and "login" in a
                ]
            else:
                out["assignees"] = []
        elif f == "createdAt":
            out["createdAt"] = issue.get("created_at")
        elif f == "updatedAt":
            out["updatedAt"] = issue.get("updated_at")
        else:
            _die(f"unsupported --json field: {f}")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description="List GitHub issues via REST (GraphQL-free gh issue list fallback)."
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Run a small offline self-test (no GitHub API calls).",
    )
    parser.add_argument(
        "--repo",
        help="owner/repo (default: infer from origin remote or $GITHUB_REPOSITORY)",
    )
    parser.add_argument(
        "--state", choices=["open", "closed", "all"], default="open", help="Issue state"
    )
    parser.add_argument(
        "--label",
        action="append",
        default=[],
        help="Label filter (repeatable). Uses REST /issues labels=... which is AND semantics.",
    )
    parser.add_argument(
        "--search",
        help=(
            "Subset of GitHub search syntax (GraphQL-free). Supports repo:, label:, "
            "state:, is:. Other tokens filter by title substring."
        ),
    )
    parser.add_argument("--limit", type=int, default=50, help="Max issues to return")
    parser.add_argument(
        "--include-prs",
        action="store_true",
        help="Include pull requests (REST /issues returns PRs too; default filters them out).",
    )
    parser.add_argument(
        "--json",
        dest="json_fields",
        help="Comma-separated fields: number,title,url,state,labels,author,assignees,createdAt,updatedAt",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    args = parser.parse_args()

    if args.self_test:
        cases = {
            "https://github.com/andrewdyates/tla2": "andrewdyates/tla2",
            "https://github.com/andrewdyates/tla2": "andrewdyates/tla2",
            "https://github.com/andrewdyates/tla2": "andrewdyates/tla2",
            "https://github.com/andrewdyates/tla2": "andrewdyates/tla2",
            "https://github.com/andrewdyates/tla2": "andrewdyates/tla2",
        }
        for inp, expected in cases.items():
            got = _parse_owner_repo(inp)
            if got != expected:
                _die(f"self-test failed: {_parse_owner_repo.__name__}({inp!r}) => {got!r}, want {expected!r}")
        search_cases = {
            "label:needs-review state:open tlc": (None, "open", ["needs-review"], ["tlc"]),
            "repo:andrewdyates/tla2 is:closed label:bug": ("andrewdyates/tla2", "closed", ["bug"], []),
        }
        for inp, expected in search_cases.items():
            got = _parse_search(inp)
            if got != expected:
                _die(f"self-test failed: {_parse_search.__name__}({inp!r}) => {got!r}, want {expected!r}")
        print("ok")
        return

    search_repo: str | None = None
    search_state: str | None = None
    search_labels: list[str] = []
    search_terms: list[str] = []
    if args.search:
        search_repo, search_state, search_labels, search_terms = _parse_search(args.search)

    repo = args.repo or search_repo or _default_repo()
    if not repo:
        _die("could not infer --repo; pass --repo owner/repo")

    if args.limit <= 0:
        _die("--limit must be > 0")

    state = args.state
    if args.state == "open" and search_state:
        state = search_state

    labels = list(args.label)
    for l in search_labels:
        if l not in labels:
            labels.append(l)

    issues = list(
        _iter_issues(
            repo=repo,
            state=state,
            labels=labels,
            limit=args.limit,
            include_prs=args.include_prs,
        )
    )

    if search_terms:
        issues = [
            i
            for i in issues
            if isinstance(i, dict) and _issue_matches_terms(i, search_terms)
        ]

    if args.json_fields:
        fields = [f.strip() for f in args.json_fields.split(",") if f.strip()]
        if not fields:
            _die("--json requires at least one field")
        out = [_select_fields(i, fields) for i in issues if isinstance(i, dict)]
        if args.pretty:
            print(json.dumps(out, indent=2, sort_keys=True))
        else:
            print(json.dumps(out))
        return

    for issue in issues:
        if not isinstance(issue, dict):
            continue
        number = issue.get("number", "?")
        state = issue.get("state", "")
        state_out = state.upper() if isinstance(state, str) else ""
        title = issue.get("title", "")
        title_out = title if isinstance(title, str) else ""
        labels_out = ", ".join(_as_labels(issue))
        updated_out = issue.get("updated_at", "")
        updated_out = updated_out if isinstance(updated_out, str) else ""
        print(f"{number}\t{state_out}\t{title_out}\t{labels_out}\t{updated_out}")


if __name__ == "__main__":
    main()
