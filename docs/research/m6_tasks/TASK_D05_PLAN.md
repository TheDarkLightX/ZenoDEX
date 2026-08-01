# FCIS M6 Task D05 Plan

TASK_ID: D05
TITLE: Derive the TCG publisher inventory independently

## Scope

D05 creates a typed source-derived publisher inventory for the Tree-Chord-Gate
authority model. The inventory is built from a reviewed deployment/build
configuration and the current bytes of its declared source files. The runtime
certificate is deliberately outside the builder input.

The inventory covers the required API, CLI, administrator, migration worker,
recovery worker, proof verifier, legacy runtime, background outbox worker, and
direct datastore adapter surfaces. It records whether a reviewed surface is
effect-capable or an authority sink so later no-bypass work has a stable
machine-readable target.

## Required outputs

- `config/deploy/fcis_m6_tcg_inventory_v1.json`
- `src/core/fcis_tcg_inventory.py`
- `tools/build_fcis_m6_d05_tcg_inventory.py`
- `experiments/fcis_m6_d05_tcg_inventory_check.py`
- `tests/core/test_fcis_m6_d05_tcg_inventory.py`
- `docs/research/m6_tasks/TASK_D05_TCG_INVENTORY_VECTOR.json`
- `docs/research/FCIS_M6_D05_TCG_INVENTORY_SCHEMA_V1.md`
- this plan, report, evidence, and source manifest

## Fail-closed acceptance

```text
python3 -m py_compile <all changed D05 Python files>
python3 -m ruff check <all changed D05 Python files>
python3 -m ruff format --check <all changed D05 Python files>
python3 -m mypy --strict <all changed D05 Python files>
python3 -m pytest -q tests/core/test_fcis_m6_d05_tcg_inventory.py
python3 tools/build_fcis_m6_d05_tcg_inventory.py --check
python3 experiments/fcis_m6_d05_tcg_inventory_check.py
python3 -m json.tool docs/research/m6_tasks/TASK_D05_TCG_INVENTORY_VECTOR.json
```

The checker must show that an inserted publisher and a source/configuration
substitution change both external roots. Omission of a required publisher,
duplicate publisher IDs, and unanchored paths must reject.

## Nonclaims

D05 is tested unmounted source-inventory evidence. It does not prove that the
reviewed configuration enumerates every production publisher, that the source
files are reachable in deployment, that an API or worker authenticates a
caller, that a datastore is authoritative, or that TCG, DRA, proof-context,
no-bypass, migration, recovery, destination, or value-moving obligations are
closed. The listed research-model adapter surfaces remain premises for later
independent audits.
