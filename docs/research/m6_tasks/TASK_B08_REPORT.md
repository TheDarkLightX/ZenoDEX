# FCIS M6 Task B08 Report

TASK_ID: B08
BASE_SHA: `4b1807f8b15bfbfd5b83c34c5f17c2a3a3d83248`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-B08-arithmetic-refinement-20260731`

IMPLEMENTATION_HEAD_SHA: `aae4912d3f0df953c14cfda7f6a83e73c0b8252b`
IMPLEMENTATION_TREE: `91824ae7d157b1dd8aeb6691086079db590ff3b2`

FILES_CHANGED:

- `docs/research/m6_tasks/TASK_B08_PLAN.md`
- `docs/research/m6_tasks/TASK_B08_KANI_RECEIPT.json`
- `docs/research/m6_tasks/TASK_B08_SMT_RESULT.json`
- `docs/research/m6_tasks/TASK_B08_REPORT.md`
- `docs/research/m6_tasks/TASK_B08_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_B08_SOURCE_MANIFEST.sha256`
- `formal/fcis_m6_b08_arithmetic/Cargo.toml`
- `formal/fcis_m6_b08_arithmetic/Cargo.lock`
- `formal/fcis_m6_b08_arithmetic/src/lib.rs`
- `formal/fcis_m6_b08_arithmetic/check_srgd_bounds.py`
- `formal/fcis_m6_b08_arithmetic/srgd_bounds.smt2`

CLAIM_IMPLEMENTED: B08 adds a dependency-free heap-free arithmetic refinement
crate and a fail-closed dual-solver SMT harness for the unmounted SRGD
candidate. Kani proves the explicit quotient/remainder, valid fixed-role
allocation, and selector-score obligations over the declared u16 amount and
u32 intermediate refinement subset. Z3 4.15.4 and CVC5 1.1.2 each return
`unsat` for all five full mathematical-U256 negated obligations: q*w width,
r*w < D^2, base <= amount, valid three-role allocation <= amount, and score
range. The checker isolates each query, rejects `sat`, `unknown`, timeout,
solver error, and unexpected output, and records rendered query hashes.

COMMANDS_RUN:

- `cargo fmt --manifest-path formal/fcis_m6_b08_arithmetic/Cargo.toml -- --check`
- `cargo test --manifest-path formal/fcis_m6_b08_arithmetic/Cargo.toml`
- `cargo clippy --manifest-path formal/fcis_m6_b08_arithmetic/Cargo.toml --all-targets -- -D warnings`
- `cargo kani -Z unstable-options --manifest-path formal/fcis_m6_b08_arithmetic/Cargo.toml --lib --output-format terse --harness-timeout 120s`
- `python3 formal/fcis_m6_b08_arithmetic/check_srgd_bounds.py --timeout-seconds 120 --json-out docs/research/m6_tasks/TASK_B08_SMT_RESULT.json`
- `python3 -m py_compile formal/fcis_m6_b08_arithmetic/check_srgd_bounds.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks B08`

RESULTS:

- Standalone Rust tests: `4 passed`; doc-tests: `0 passed, 0 failed`.
- Rust formatting and strict Clippy: pass.
- Kani: `3 successfully verified harnesses, 0 failures`.
- Z3: five isolated queries returned `unsat`.
- CVC5: the same five isolated queries returned `unsat`.
- No timeout or `unknown` occurred in the final checker run.
- The initial u32 symbolic quota harness timed out at 120 seconds. That
  witness is retained in `TASK_B08_KANI_RECEIPT.json` and is explicitly
  non-supporting. The final Kani model uses an explicit u16/u32 refinement.
- No caller, datastore adapter, authority switch, deployment path, or
  value-moving path was mounted.

MUTANTS_ADDED:

- `B08_U32_KANI_TIMEOUT`: retained timeout witness prevents promotion of the
  unsupported wider Kani model.
- `B08_NEGATED_OBLIGATION_SAT`: each SMT query is a fail-closed negated
  obligation; any satisfiable result causes checker failure.
- `B08_SOLVER_UNKNOWN_OR_TIMEOUT`: checker rejects both outcomes and exits
  without producing a supporting receipt.

FORMAL_EVIDENCE: Kani and independent Z3/CVC5 SMT receipts are included.
The SMT model uses exact mathematical integers with the full admitted bound
`0 <= amount <= 2^256 - 1`, Euclidean decomposition, arbitrary nonnegative
three-role weights summing to `D`, supported bonus bits, exact seat count, and
the signed selector interval. The Kani model has an explicit embedding into
production `BigUint::from(x)` for its strict subset.

REMAINING_NONCLAIMS:

- B08 does not prove a fixed-width U256 library implementation because the
  production carrier is `BigUint` and the full transition contains heap-backed
  collections and canonicalization code.
- The successful Kani proof is not a full 256-bit machine proof; the full-width
  obligations are supported by exact mathematical SMT checks.
- B08 does not complete Python/Rust/Julia byte and root parity; that is B09.
- B08 does not prove production consensus, datastore, authority, migration,
  effect, or value-moving behavior.
- The Rust and SMT artifacts remain unmounted research evidence and authorize
  no value movement.
- No remote implementation commit, hosted CI run, draft PR, or publication is
  claimed.

REVIEW_RISKS: The Kani layer is intentionally narrower than U256 because the
initial symbolic u32 quota harness timed out. SMT solver support is exact for
the stated mathematical equations, while the BigUint adapter and production
fixed-width refinement remain open. The three-role allocation proof relies on
the stated policy-weight sum, Euclidean decomposition, supported bonus, and
seat-count premises; malformed inputs remain rejection cases outside the
accepted relation.
