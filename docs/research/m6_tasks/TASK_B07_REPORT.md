# FCIS M6 Task B07 Report

TASK_ID: B07
BASE_SHA: `1ce445409c0e783e3b927e0bd389693cdefb7f59`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-B07-rust-srgd-transition-20260731`

IMPLEMENTATION_HEAD_SHA: `dedba1713e23e00b07d9bc953a503864f6c5afb3`
IMPLEMENTATION_TREE: `830b9cf8285ddb00e66e35ed5cb1841760c89673`

FILES_CHANGED:

- `rust-runtime/crates/zenodex-runtime-core/src/fcis_fee_apportionment.rs`
- `docs/research/m6_tasks/TASK_B07_REPORT.md`
- `docs/research/m6_tasks/TASK_B07_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_B07_SOURCE_MANIFEST.sha256`

CLAIM_IMPLEMENTED: The unmounted Rust FCIS SRGD transition now uses checked
residual-product arithmetic, wide signed selector scores, checked wide
post-deficit arithmetic, and an independent postcondition relation before
constructing accepted allocation evidence. The relation rechecks the fixed
role profile, Euclidean fractions and bases, zero-weight support, local quota
amounts, aggregate conservation, bonus count and support, deterministic score
order, U256 bounds, post-deficit recurrence, strict bounds, and conservation.
The result remains a pure `Result<Accept, Reject>` transition with no external
effects.

COMMANDS_RUN:

- `cargo fmt --all -- --check` from `rust-runtime/`
- `cargo check -p zenodex-runtime-core` from `rust-runtime/`
- `cargo test -p zenodex-runtime-core fcis_fee_apportionment --lib` from
  `rust-runtime/`
- `cargo test -p zenodex-runtime-core` from `rust-runtime/`
- `cargo clippy -p zenodex-runtime-core --all-targets -- -D warnings` from
  `rust-runtime/`
- `git diff --check`
- `git diff --cached --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks B07`

RESULTS:

- Rust formatting: pass.
- Rust compilation: pass.
- Focused FCIS tests: `7 passed`.
- Full runtime-core suite: `196` unit tests passed, `6` robustness tests
  passed, and doc-tests passed.
- Strict clippy: pass with `-D warnings`.
- U256 maximum quota witness: pass through the bounded `AmountU256` carrier.
- Signed-width and postcondition mutation witnesses: pass.
- No new caller, datastore adapter, authority switch, deployment, or
  value-moving path was mounted.

MUTANTS_ADDED: Five named executable Rust witnesses are included:

- `B07_SIGNED_DEFICIT_REWARD_OVERFLOW`: malformed buyback and treasury
  deficits cannot overflow while deriving the rewards deficit.
- `B07_WIDE_SELECTOR_SCORE`: selector score ordering remains defined for
  extreme signed inputs through i64 intermediates.
- `B07_POST_DEFICIT_BOUND`: an out-of-range post deficit is rejected.
- `B07_AMOUNT_CONSERVATION`: a mutated allocation amount is rejected by the
  independent postcondition relation.
- `B07_U256_MAX_QUOTA`: the maximum admitted amount preserves quota base and
  remainder bounds.

FORMAL_EVIDENCE: None added. B07 supplies checked Rust arithmetic and
executable refinement witnesses. The B08 Kani/SMT arithmetic obligation and
the B09 three-way parity campaign remain open.

REMAINING_NONCLAIMS:

- B07 does not prove the general SRGD theorem or provide Kani/SMT evidence.
- B07 does not complete Python/Rust/Julia canonical-byte, root, and rejection
  parity over the full required domains.
- B07 uses the existing bounded `num_bigint::BigUint` carrier with explicit
  U256 admission checks; it does not supply a separately verified fixed-width
  U256 library refinement.
- B07 does not prove production consensus, datastore, authority, migration,
  effect, or value-moving behavior.
- The Rust module remains an unmounted research/candidate kernel and
  authorizes no value movement.
- No remote implementation commit, hosted CI run, draft PR, or publication is
  claimed.

REVIEW_RISKS: The Rust source is a 1,200-line hotspot because it owns the
candidate values, arithmetic, canonical bytes, and tests in one historical
module. The new postcondition relation intentionally recomputes the quota
relation, which reduces trust in intermediate producer values at the cost of
local duplication. Fixed-width machine refinement, cross-runtime parity, and
runtime mounting remain outside B07.
