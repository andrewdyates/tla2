<!-- Andrew Yates <andrewyates.name@gmail.com> -->
# Eval Registry

Standard layout for eval specs, reusable templates, and results so repos can share
a consistent format.

## Directory Layout

```
evals/
├── registry/    # YAML eval specs
├── templates/   # Reusable eval runners
├── results/     # Output artifacts (gitignored)
└── logs/        # Execution logs (gitignored)
```

## Registry Format

Each YAML file in `evals/registry/` defines a single eval. Minimal fields:

- `id`: Unique eval identifier (kebab-case).
- `version`: Integer schema version for the eval spec.
- `description`: Short human-readable description.
- `owner`: Contact or team responsible for the eval.
- `entrypoint`: Template runner entrypoint (module:function or script).
- `inputs`: Dataset and runner parameters.
- `metrics`: List of metric names.
- `outputs`: Result and log paths with `{run_id}` placeholders.

See evals/registry/example.yaml for a concrete example.

## Results Format

Store results under `evals/results/<eval_id>/<run_id>/` and logs under
`evals/logs/<eval_id>/<run_id>/`.

Minimal output files:

```
evals/results/<eval_id>/<run_id>/
├── metadata.json
└── results.json
```

Recommended `metadata.json` fields:

```
{
  "eval_id": "example-qa",
  "run_id": "2026-01-25T12-00-00Z",
  "git_commit": "abc1234",
  "spec_path": "evals/registry/example.yaml",
  "runner": "evals.templates.simple_qa",
  "started_at": "2026-01-25T12:00:00Z",
  "finished_at": "2026-01-25T12:04:31Z"
}
```

Recommended `results.json` fields:

```
{
  "metrics": {
    "exact_match": 0.75,
    "f1": 0.82
  },
  "items": []
}
```

`items` is optional and can include per-example outputs when needed.

### Claim Validation

For evals that support automated claim validation (e.g., benchmark scores in commit
messages), the `metrics` object **must** include `passed` and `total` integer fields:

```
{
  "metrics": {
    "passed": 45,
    "total": 55,
    "accuracy": 0.818
  }
}
```

Constraints:
- `passed`: Non-negative integer (>= 0)
- `total`: Positive integer (>= 1)
- `passed` must not exceed `total`

benchmark claims. See evals/schema/results.schema.json for the formal schema
definition.

## Templates

Templates in `evals/templates/` implement the runner referenced by `entrypoint`.
Each runner should accept the eval spec and write `metadata.json` and
`results.json` to the output directory described above.
