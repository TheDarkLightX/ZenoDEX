# FCIS M6 Task G02 report: proof-context codec and parity

TASK_ID: G02
BASE_SHA: e38775eab0c71f2771c65a1b669d696467d1e35f
SOURCE_HEAD_SHA: fbbad8f53c9d89c6818167820f8469aa68526947
SOURCE_HEAD_TREE: 6f071f39be8ce01cee61ec44941590c3ceb647ea
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_g02_proof_context_v1.json
- src/core/fcis_m6_g02_proof_context_codec.py
- experiments/fcis_m6_g02_proof_context_check.py
- tests/core/test_fcis_m6_g02_proof_context_codec.py
- tests/core/test_fcis_m6_g02_proof_context_codec_properties.py
- tools/build_fcis_m6_g02_proof_context.py
- docs/research/m6_tasks/TASK_G02_PROOF_CONTEXT_V1.json
- docs/research/m6_tasks/TASK_G02_RUST_INPUT.tsv
- docs/research/m6_tasks/TASK_G02_RUST_PAYLOAD.hex
- docs/research/m6_tasks/TASK_G02_RUST_ROOT.txt
- formal/fcis_m6_g02_proof_context_parity/Cargo.toml
- formal/fcis_m6_g02_proof_context_parity/Cargo.lock
- formal/fcis_m6_g02_proof_context_parity/src/main.rs

IMPLEMENTATION_HEAD_SHA: fbbad8f53c9d89c6818167820f8469aa68526947
IMPLEMENTATION_TREE: 6f071f39be8ce01cee61ec44941590c3ceb647ea
IMPLEMENTATION_PARENT: e38775eab0c71f2771c65a1b669d696467d1e35f

CLAIM_IMPLEMENTED: G02 defines one bounded fixed-order binary codec for the
G01 proof-context value. The decoder returns typed success or rejection,
revalidates the complete G01 semantic value, and exposes a distinct transport
codec root. Python and Rust reproduce the same canonical payload and codec
root from a source-bound vector.

COMMANDS_RUN:
- `python3 -m json.tool config/deploy/fcis_m6_g02_proof_context_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_G02_PROOF_CONTEXT_V1.json`
- `PYTHONPATH=. python3 tools/build_fcis_m6_g02_proof_context.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_g02_proof_context_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py`
- `python3 -m py_compile src/core/fcis_m6_g02_proof_context_codec.py experiments/fcis_m6_g02_proof_context_check.py tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py tools/build_fcis_m6_g02_proof_context.py`
- `python3 -m ruff check src/core/fcis_m6_g02_proof_context_codec.py experiments/fcis_m6_g02_proof_context_check.py tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py tools/build_fcis_m6_g02_proof_context.py`
- `python3 -m ruff format --check src/core/fcis_m6_g02_proof_context_codec.py experiments/fcis_m6_g02_proof_context_check.py tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py tools/build_fcis_m6_g02_proof_context.py`
- `python3 -m mypy --strict src/core/fcis_m6_g02_proof_context_codec.py experiments/fcis_m6_g02_proof_context_check.py tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py tools/build_fcis_m6_g02_proof_context.py`
- `cargo fmt --check --manifest-path formal/fcis_m6_g02_proof_context_parity/Cargo.toml`
- `cargo clippy --quiet --manifest-path formal/fcis_m6_g02_proof_context_parity/Cargo.toml -- -D warnings`
- `cargo run --quiet --manifest-path formal/fcis_m6_g02_proof_context_parity/Cargo.toml -- docs/research/m6_tasks/TASK_G02_RUST_INPUT.tsv docs/research/m6_tasks/TASK_G02_RUST_PAYLOAD.hex docs/research/m6_tasks/TASK_G02_RUST_ROOT.txt`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks G02`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_G02_SOURCE_MANIFEST.sha256`

RESULTS:
- G02 focused and property suite passed: 6 passed.
- Combined G01 and G02 focused/property suite passed: 12 passed.
- Deterministic Hypothesis campaigns used 24 examples for generated
  state-root substitutions and 24 examples for generated trailing-byte
  mutations.
- Independent Python checker passed:
  `G02_PROOF_CONTEXT_CHECKS_PASS 0xef59b94d7624fa21d8d5a1045907a0a7ff731778f0e0064d6247bdf82e7f05fb`.
- Source-bound vector check passed: `G02_PROOF_CONTEXT_VECTOR_MATCH`.
- Rust payload and root parity passed:
  `G02_RUST_PARITY_PASS 0xef59b94d7624fa21d8d5a1045907a0a7ff731778f0e0064d6247bdf82e7f05fb`.
- Python compilation, Ruff, Ruff formatting, strict mypy, Rustfmt, Clippy,
  JSON parsing, and diff checks passed.

MUTANTS_ADDED: foreign codec version, unknown field, reordered fields, wrong
field tag, trailing frame bytes, crossed G01 context root, generated state-root
substitutions, and generated trailing-byte mutations.

FORMAL_EVIDENCE: None. G02 supplies typed executable evidence, deterministic
property tests, and independent Python/Rust codec parity. It adds no
machine-checked Lean theorem and no proof-verifier authority.

REMAINING_NONCLAIMS:
- G02 does not authenticate the caller or make a caller-constructed context a
  verified witness.
- G02 does not pin a G03 verifier registry or bind G04 public inputs to ANF.
- The Rust harness checks codec byte/root parity; it is not a semantic proof
  verifier and does not independently authorize the supplied context fields.
- G02 does not prove filesystem, datastore, crash-recovery, runtime, migration,
  destination, or value-moving behavior.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The codec is structurally canonical only for the fixed G02
schema. A structurally valid context can still be semantically unauthorized
until a later registry, public-input, proof, and runtime authority boundary
revalidates and owns it. A preliminary direct script invocation without the
documented `PYTHONPATH=.` prefix failed to import the repository package; the
documented final command is explicit and passed.
