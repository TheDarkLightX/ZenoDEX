# Python Typing Ratchet

ZenoDEX has high Python annotation coverage, but full typing assurance is a
separate claim. A function signature annotation says what the code intends. A
type-checking gate says the repository keeps that intent coherent as code
changes.

## Current Ratchet

Run the typing audit:

```bash
python3 tools/type_coverage_audit.py
```

Run it as a failing gate:

```bash
python3 tools/type_coverage_audit.py --check
```

The gate currently enforces:

- at least `98.9%` fully typed function signatures in `src/`;
- at least `97.5%` fully typed function signatures in `src/core` plus
  `src/state`;
- at least `25` tracked files present in the configured mypy file list.

This is a ratchet, not a proof that Python runtime values can never violate a
type contract. It prevents the already-high annotation surface from silently
sliding backward while stricter mypy coverage is promoted module by module.

## Mypy Gate

The configured mypy gate is:

```bash
.venv/bin/mypy
```

That gate checks the curated file list in `pyproject.toml`. It is currently a
partial gate, because the config intentionally uses:

```toml
ignore_missing_imports = true
follow_imports = "skip"
check_untyped_defs = true
```

So selected files are checked, but imported modules are not deeply followed.

## Stronger Next Step

The next useful promotion is a stricter functional-core lane:

```bash
.venv/bin/mypy src/core src/state \
  --follow-imports=normal \
  --ignore-missing-imports \
  --check-untyped-defs \
  --no-implicit-optional
```

That stricter lane is intentionally not claimed clean yet. It currently exposes
cross-module typing work that should be retired in small, reviewable patches:
nullable JSON parsing, tuple union narrowing, reused local variable names, and
third-party adapter ignores.

## Assurance Meaning

The current state supports this claim:

```text
high annotation coverage + clean configured mypy gate + ratchet audit
  -> accidental type-surface regression is harder to introduce silently
```

It does not support this stronger claim yet:

```text
all Python consensus-critical code is strictly type-checked end to end
```

That stronger claim needs the functional-core lane above to be made clean and
then added to CI.
