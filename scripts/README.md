# Scripts

Andrew Yates

## GitHub CLI rate-limit workarounds

When GitHub GraphQL quota is exhausted, `gh issue list` can fail with:

`GraphQL: API rate limit already exceeded ...`

Use the REST-based fallback script:

- List open issues with a label: `./scripts/gh_issue_list_rest.py --label needs-review --limit 200`
- List do-audit queue: `./scripts/gh_issue_list_rest.py --label do-audit --limit 200`
- List blocked issues: `./scripts/gh_issue_list_rest.py --label blocked --state open --limit 200`
- Query a small subset of GitHub search syntax (still GraphQL-free): `./scripts/gh_issue_list_rest.py --search "repo:andrewdyates/tla2 state:open label:bug"`

## Validation

CoffeeCan codegen/AOT validation: run `validate_coffecan_codegen_poc.py` from this directory.

Example:
```bash
python3 scripts/validate_coffecan_codegen_poc.py --beans 10 --output-json target/coffecan_codegen_poc_10.json
```

Prereqs: `~/tlaplus/tla2tools.jar` and
`~/tlaplus-examples/specifications/CoffeeCan/CoffeeCan.tla`.

Current-report routing validation: run `check_current_doc_routing.py` from this directory
to catch regressions where active `current` docs drift back to stale
`MCBoulanger` timeout wording or other frozen routing assumptions.
