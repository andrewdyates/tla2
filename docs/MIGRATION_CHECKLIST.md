# Migration Checklist

Copyright 2026 Andrew Yates.
Author: Andrew Yates <andrewyates.name@gmail.com>

Steps to align an existing repo with andrewdyates.

> **Note:** For new repos, `init_from_template.sh` handles hooks and labels automatically.
> This checklist is for **existing repos** that need alignment.

## Quick Alignment

3. Re-run audit to verify

## Manual Steps

### Required Files
- [ ] .AI Model/rules/andrewdyates.md - Core rules
- [ ] .AI Model/rules/org_chart.md - Org reference
- [ ] .AI Model/roles/*.md - Role definitions

### Recommended Files
- [ ] `[internal document]` - Strategic direction
- [ ] `ideas/` directory - Future backlog
- [ ] `.pre-commit-config.yaml` - Pre-commit hooks

### Git Hooks
- [ ] Verify hooks: `ls -la .git/hooks/`

### Labels
- [ ] Verify: `gh label list`

## Troubleshooting

### Hooks not working
```bash
```

### Missing labels
```bash
```

### Preview sync changes
```bash
```
