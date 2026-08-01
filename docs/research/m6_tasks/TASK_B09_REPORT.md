# FCIS M6 Task B09 Report

TASK_ID: B09
BASE_SHA: aca4c441aef978ee74d145202c55c556700cbfa3
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-B09-three-way-parity-20260731

IMPLEMENTATION_HEAD_SHA: 6c0c881cdcbd05b8a6ca2011b08bec5e2828d25a
IMPLEMENTATION_TREE: 7c1981d57960d31bdfeb2355a7a7c5440a8cd275
IMPLEMENTATION_PARENT: aca4c441aef978ee74d145202c55c556700cbfa3

FILES_CHANGED:

- docs/research/m6_tasks/TASK_B09_PLAN.md
- docs/research/m6_tasks/TASK_B09_REPORT.md
- docs/research/m6_tasks/TASK_B09_EVIDENCE.json
- docs/research/m6_tasks/TASK_B09_SOURCE_MANIFEST.sha256
- docs/research/m6_tasks/TASK_B09_ARTIFACTS/
- experiments/fcis_fee_apportionment_parity.py
- experiments/fcis_m6_b09_artifact_index.py
- experiments/julia/fcis_fee_apportionment_oracle.jl
- formal/fcis_m6_b09_rust_parity/

CLAIM_IMPLEMENTED: B09 adds a standalone, unmounted Python/Rust/Julia
three-way parity campaign for the SRGD fee-apportionment candidate. The
production-D protocol preserves grouped candidates, exact rejection
code/path, semantic allocations, canonical state/allocation/result bytes,
and the result digest. The Julia lane independently recomputes the
arithmetic, selector, state, and canonical JSON bytes. The small-domain lane
exhausts the parameterized arithmetic reference through D=12.

COMMANDS_RUN:

- cargo fmt --manifest-path formal/fcis_m6_b09_rust_parity/Cargo.toml -- --check
- cargo check --manifest-path formal/fcis_m6_b09_rust_parity/Cargo.toml
- cargo test --manifest-path formal/fcis_m6_b09_rust_parity/Cargo.toml
- cargo clippy --manifest-path formal/fcis_m6_b09_rust_parity/Cargo.toml --all-targets -- -D warnings
- python3 -m py_compile experiments/fcis_fee_apportionment_parity.py experiments/fcis_m6_b09_artifact_index.py
- python3 -m ruff check experiments/fcis_fee_apportionment_parity.py experiments/fcis_m6_b09_artifact_index.py
- python3 experiments/fcis_fee_apportionment_parity.py
- python3 experiments/fcis_m6_b09_artifact_index.py docs/research/m6_tasks/TASK_B09_ARTIFACTS
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks B09
- git diff --check

RESULTS:

- Production campaign: 1,022 records matched byte-for-byte.
- Shared baseline: 12 of 12 vectors matched, including grouped multi-key and
  aggregate-overflow cases.
- Production edge campaign: 10 of 10 records matched.
- Adaptive campaign: 1,000 of 1,000 state-carrying records matched.
- Python, Rust, and Julia production output SHA-256:
  0888b330c56dbff0bcdf8611532c176088da32ac5e1f4db7100cd2ff221e55ed.
- Small-domain campaign: 1,229,773 records matched for every denominator
  from 1 through 12 under the declared arithmetic reference.
- Python and Julia small-domain output SHA-256:
  1a59f2023c36fa0576bc37fa380731dd8543d7a6a90ced66fb30306b954e304b.
- Standalone Rust cargo test completed with zero test cases and no failures;
  strict Clippy and rustfmt passed.
- The compressed evidence index records decompressed and compressed hashes for
  every retained corpus member.
- No caller, datastore adapter, authority switch, deployment path, or
  value-moving path was mounted.

MUTANTS_ADDED:

- B09_JULIA_SUBSTRING_RECORD: initial SubString dispatch failure was retained
  and repaired before parity promotion.
- B09_JULIA_GROUP_KEY_SHADOW: local binding shadowed the keys function and
  failed closed before repair.
- B09_JULIA_ZERO_SUPPORT_SELECTOR: adaptive-0862 exposed selection of a
  zero-fraction role; the independent selector was corrected to filter
  eligibility before score ordering.
- B09_JULIA_BIGINT_SUBSTRING: the small-domain lane retained a
  SubString-to-BigInt failure witness and repaired it before the green run.

FORMAL_EVIDENCE: B09 supplies exact cross-language refinement evidence for
the declared unmounted candidate relation. Every production record compares
decision, rejection code/path, grouped semantic fields, canonical state
bytes, allocation bytes, result bytes, and result digest. The exhaustive
small-domain lane compares an independently implemented Python arithmetic
reference with Julia and records counts and hashes. This is executable
refinement evidence rather than a production theorem.

REMAINING_NONCLAIMS:

- B09 does not prove requirements completeness, economic correctness, or
  production consensus behavior.
- B09 does not mount the kernel into runtime, datastore, authority,
  migration, effect, API, deployment, or value-moving paths.
- The small-domain campaign does not claim a runtime-configurable denominator.
- The Rust carrier remains BigUint; B09 does not prove a fixed-width U256
  implementation or production adapter refinement.
- No remote implementation commit, hosted CI run, draft PR, or publication is
  claimed.
- The repository's local exclude hides experiments/; only the four named B09
  experiment artifacts were force-added.

REVIEW_RISKS: The parity harness is a 1,419-line research hotspot spanning
three languages and canonical serialization. Its agreement is bounded by the
declared input protocol and existing Python candidate constructors. The
production Rust harness is standalone and unmounted. The compressed corpus
is validated through the artifact index; a future regeneration must rerun the
recorded campaign and compare the decompressed hashes.
