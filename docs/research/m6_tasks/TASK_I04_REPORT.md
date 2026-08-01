# FCIS M6 Task I04 Report

TASK_ID: I04
BASE_SHA: 79ed2a34312cab21c7335d1eb16e80f9715a2905
SOURCE_HEAD_SHA: 1cd7680a9f8fd7ca221e99ab281df75f3bae36f5
SOURCE_HEAD_TREE: 23a77e8d396a41c942ade2fc15647cd092fe510e
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_i04_destination_dedup.py
- tests/core/test_fcis_m6_i04_destination_dedup.py
- docs/research/m6_tasks/TASK_I04_DESTINATION_DEDUP_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_I04_PLAN.md

IMPLEMENTATION_HEAD_SHA: 1cd7680a9f8fd7ca221e99ab281df75f3bae36f5
IMPLEMENTATION_TREE: 23a77e8d396a41c942ade2fc15647cd092fe510e
IMPLEMENTATION_PARENT: 79ed2a34312cab21c7335d1eb16e80f9715a2905

CLAIM_IMPLEMENTED: I04 adds a verifier-gated deterministic destination
deduplication model. It accepts native idempotency-key, query-by-effect-ID,
and application-owned receipt-table mechanisms. Each accepted effect is
recorded by effect ID, destination, and payload root. Duplicate attempts return
the original destination receipt root as ALREADY_ACCEPTED; changed payload,
destination, or adapter profile rejects without changing destination state.
Unsupported mechanisms and forged contract roots are UNMOUNTABLE.

COMMANDS_RUN:
- python3 -m ruff format experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py
- python3 -m ruff check experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py
- python3 -m ruff format --check experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py
- python3 -m mypy --strict experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py
- python3 -m py_compile experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i04_destination_dedup.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I04
- sha256sum --check --strict docs/research/m6_tasks/TASK_I04_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Focused I04 suite passed: 6 passed.
- All three declared dedup mechanisms produced the same observational
  duplicate contract: stable effect ID, payload root, and receipt root.
- Same-effect payload mutation rejected as PAYLOAD_CONFLICT with unchanged
  destination state.
- Destination and adapter-profile crossings rejected before acceptance.
- Forged contract roots and unsupported caller-asserted exactly-once modes
  returned UNMOUNTABLE.
- Duplicate and noncanonical destination-record collections rejected.
- Invalid effect input rejected without creating destination state.
- Ruff, formatting, strict mypy, Python compilation, packet validation, and the
  source manifest pass.

MUTANTS_ADDED: None. The focused suite contains negative witnesses for payload
collision, destination crossing, adapter-profile crossing, forged contract,
unsupported mechanism, duplicate records, noncanonical order, and invalid
effect input.

FORMAL_EVIDENCE: None. I04 supplies executable deterministic adapter evidence;
it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- I04 does not prove any external destination's native idempotency, query, or
  application receipt-table implementation.
- I04 does not verify acknowledgment provenance, destination receipt bytes,
  lost acknowledgments, worker delivery, or retry recovery.
- I04 does not prove concurrent linearizability, production datastore
  behavior, runtime reachability, migration, no-bypass coverage, accounting,
  or zUSD safety.
- No network, production destination, caller, or value-moving path is
  mounted. M6 remains research-only and non-promotable.

REVIEW_RISKS: The three mechanisms share one immutable reference state machine
to expose the common observational contract. Production adapters still need
mechanism-specific refinement evidence, receipt provenance binding, failure
and timeout behavior, and an explicit unmount decision when the destination
cannot provide a verified dedup contract.
