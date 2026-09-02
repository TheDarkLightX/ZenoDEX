# Opus independent review — candidate C8-p9 (repair of P25)

- Branch: `codex/formal-core-fable-20260901`
- Subject `S26`: `240255e1e724bb98c72a9b7e2d40ce4ff63bc724` (parent `071a6b5f490569b411d9b445613d811f21f24015` = the R22 receipt)
- Artifact `P26`: `5de48174fe7dd09c8a99d4c432f97c92c2f16847` (parent = S26)
- Review worktree: `/tmp/zenodex-formal-core-opus-c8p9`, detached at P26, clean before and after every probe
- Authority asserted by this review: **NONE**. The claim ceiling did not move.

**Grade: A-**  — 0 P1, 0 P2, 3 P3 (NEW-16, NEW-17, NEW-18).
NEW-13 CLOSED, NEW-14 CLOSED (with a stated residual I accept as follow-up),
NEW-15 CLOSED for its stated class but its mutation row is not yet total.

---

## 1. Shape of the change

`P26` is artifact-only. A semantic JSON diff of `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`
against its predecessor shows exactly four changed scalars and nothing else:

```
packet_commit_parent  a18699202... -> 240255e1e...
subject_commit        a18699202... -> 240255e1e...
subject_parent        0daf9ef64... -> 071a6b5f4...
subject_tree          0a74df56f... -> 13729394d...
```

`subject_tree` equals `git rev-parse 240255e1e^{tree}`. `packet_write_set` is exactly the two
docs paths, matching the actual P26 diff. No `claim_ceiling`, `completion_scope`, `nonclaims`,
`source_pins`, `lean_evidence`, `esso_evidence`, or `hygiene_selection` entry moved.

`S26` touches five files: the two Python test files, the Rust totality test, and two new
THV evidence packets (`...-resource-bounds-v6`, `...-o008-transition-resource-bound-totality-v3`).
None of the five is inside the O-008 packet's own pinned surface (42 `source_pins`,
39 `hygiene_selection` rows), which is why the packet regenerated with pointer changes only.
That is the correct behaviour, not a stale-pin defect.

## 2. Replays (all at P26)

| Gate | Result |
|---|---|
| `check_o008_formal_cycle_v1.py` (no `--replay`) | exit 0, `ok=true`, `packet_admitted=true`, `current_applicable=true`, `current_source_drift=[]`, `NOT_RUN`, stderr empty, 4.9s |
| `check_o008_formal_cycle_v1.py --replay` | exit 0, **`EXECUTED_PASS`, 28/28 runs exit 0**, `errors=[]`, stderr empty, ~8.5 min |
| `cargo fmt --all -- --check` | **exit 0** |
| `cargo test --offline --locked` | exit 0, 54 test binaries, **527 passed, 0 failed** |
| `cargo clippy --offline --locked --all-targets -- -D warnings` | exit 0, zero warning/error lines |
| pytest: changed suites + Rust replay + both module suites | **68 passed** |
| pytest: wider pinned suites (abi_v1, atom coverage, both goldens, lane producers) | **190 passed** |
| `run_test_hygiene_gate_v1.py --base-ref 071a6b5f4` | `ok=true`, 3 critical paths covered, 90 pinned node ids, 111 tests passed; selected exactly the two new evidence ids |
| Lean 1: `lake env lean -DwarningAsError=true Proofs/GlobalClaimantCustodyRelationV1.lean` | exit 0, stdout and stderr both 0 bytes (Lean 4.27.0) |
| Lean 2: `pytest tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 6 passed |
| Lean 3: `lake env lean -DwarningAsError=true Proofs/GlobalAccountingAllocationCertificateV1.lean` | exit 0, stdout and stderr both 0 bytes |
| Lean 4: `pytest tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | 6 passed |

The four Lean commands were run strictly serially, one process at a time.

**Claim ceiling, byte-identical in both checker modes:**
`formal_core_complete=false`, `whole_value_movement_safe=false`,
`value_movement_gates_closed=0 / 12`, `o008_status=OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`,
and `migration/production/publication/release/settlement/value_movement/verifier_authority`
all `NONE`. Nothing moved.

**Vacuity probe (the gate is live, not decorative):** appending one comment line to the pinned
`src/core/global_economic_state_effect_refinement_v1.py` makes the checker exit 1 with
`current_applicable=false` and `current_source_drift=["src/core/global_economic_state_effect_refinement_v1.py"]`.

**Pin integrity:** every `source_pins` and `test_pins` sha256 in both new THV packets equals both
the committed blob at P26 and the worktree bytes. Zero mismatches. All pinned node ids collect,
including the new `test_reject_code_families_match_across_languages`.

## 3. Closure of the P25 findings

| Finding | Verdict | Evidence |
|---|---|---|
| NEW-13 non-recursive glob | **CLOSED** | mutant + control below |
| NEW-14 crate fmt | **CLOSED** (residual accepted as follow-up) | `cargo fmt` exit 0 + control below |
| NEW-15 unpinned reject-enum families | **CLOSED for the stated class**; row not yet total | 7 drift mutants all die; 3 new survivors → NEW-16 |

### NEW-13 — CLOSED

The repair is `crate_src.glob("*.rs")` → `crate_src.rglob("*.rs")`. The crate has one
subdirectory, `src/economic_command_authentication/`, holding two `.rs` files that the old
scan never read: `glob` reads 88 files, `rglob` reads 90.

My P25 survivor, re-run:

- `pub const MAX_OPUS_SUBDIR_PROBE_V1: usize = 7;` appended to
  `zk/global_settlement_abi_v1/src/economic_command_authentication/types.rs`
  → `test_every_canonical_rust_bound_has_a_python_twin` **FAILS**. Killed.
- **Control**, same mutant with the R22 bytes of the test file restored → **PASSES**.
  The survivor is reproduced on the old code and killed by the new code, so the kill is the
  repair and not an accident of the tree.

Bound counts on the clean tree: 37 unique under `glob`, 37 unique under `rglob`
(the subdir files currently declare no `MAX_` bound), so `assert len(rust_bounds) >= 37` holds
and remains a live anti-shrink floor. Two further probes of that floor:

- visibility downgrade `pub const MAX_ASSET_BALANCE_ROWS_V1` → `pub(crate) const …` → **KILLED**
  (count drops to 36, the floor fires).
- a `pub const MAX_…` with a non-evaluable initialiser (`= some_fn();`) → **KILLED** loudly via
  `evaluate()` raising, i.e. fail-closed rather than silently skipped.

### NEW-14 — CLOSED, with a residual I accept as follow-up

`cargo fmt --all -- --check` on `zk/global_settlement_abi_v1` exits **0** at P26.
**Control:** restoring the R22 bytes of `tests/transition_resource_bound_totality.rs` makes the
same command exit 1 with exactly **6** `Diff in` hunks in that one file — matching the packet's
"six cosmetic hunks" claim exactly. The S26 diff for that file is pure reformatting; no assertion,
target, or expectation changed.

Residual, as the prompt asked me to judge honestly: the crate is in **neither** fmt manifest of
`tools/run_rust_runtime_parity_gate.sh` (`RUST_MANIFESTS`, 11 kernel crates; `RISC0_FORMAT_MANIFESTS`,
4 RISC0 crates), and `grep` finds no reference to `global_settlement_abi_v1` in any `tools/*.sh`
or `.github/workflows/*.yml`. So nothing re-checks the crate's formatting on a future commit.

**I accept this as a follow-up and do not hold it against the grade**, for three reasons:
(1) the finding I raised was about this file's formatting, which is fixed and byte-pinned;
(2) wiring that shell script is outside this campaign's write set, as stated;
(3) the THV source pin does give forward protection of a different kind — any future edit to that
file changes its sha256 and re-enters the hygiene gate, which is what actually fires in this repo's
workflow. What is *not* protected is a future edit that lands together with a pin refresh, which is
exactly what a manifest entry would cover. That is the follow-up.

### NEW-15 — CLOSED for the stated class

`test_reject_code_families_match_across_languages` parses each Rust `pub enum` block and compares
it member-for-member and in order against the Python enum, plus `member.value == member.name`.
Live counts agree: asset 12, managed 15, identical names in identical order.

Every drift mutant I could state from the finding dies:

| Mutant | Verdict |
|---|---|
| grow Rust only (`OPUS_PROBE_VARIANT,` appended) | KILLED |
| grow Python only | KILLED |
| reorder Rust only (`SELF_TRANSFER` ↔ `ZERO_AMOUNT`) | KILLED |
| reorder Python only (managed: `ISSUE_DISABLED` ↔ `BURN_DISABLED`) | KILLED |
| rename Python only (`SELF_TRANSFER` → `SELF_TRANSFER_RENAMED`) | KILLED |
| rename Rust only (managed: `SUPPLY_OVERFLOW` → `SUPPLY_OVERFLOW_RENAMED`) | KILLED |
| value drift Python only (`ZERO_AMOUNT = "ZERO_AMOUNT_X"`) | KILLED |

Seven for seven. The non-vacuity anchor (`POST_STATE_RESOURCE_BOUND_EXCEEDED` present) is there.

## 4. New findings

### NEW-16 (P3) — the Rust variant parser is narrower than the mutation row it certifies

`rust_variants()` collects members with `re.findall(r"^\s*([A-Z][A-Z0-9_]*),", block, re.M)` and
the test then compares two **lists for equality**. Any variant line the regex cannot match is
silently dropped from the Rust side, so a Rust-only addition in a non-matching form leaves the two
lists equal and the pin reports agreement.

Three confirmed survivors, added to `AssetTransferRejectCodeV1` in Rust only:

| Mutant | Family pin | `cargo check` | `clippy -D warnings` | 6 Rust targets naming the enum |
|---|---|---|---|---|
| `OPUS_PROBE_NOCOMMA` appended with no trailing comma | **SURVIVED** | exit 0 | 0 diagnostics | all pass |
| `OpusProbeCamel,` in idiomatic Rust CamelCase | **SURVIVED** | exit 0 | 0 diagnostics | all pass (27 tests) |
| `OPUS_PROBE_PAYLOAD(u32),` tuple variant | **SURVIVED** | exit 0 | 0 diagnostics | all pass |

Nothing else catches them: `grep` finds **no exhaustive `match`** on either reject enum anywhere in
`zk/global_settlement_abi_v1/src`, so adding a variant does not break compilation; there is no
`strum`/variant-enumeration test; and both enums already carry `#[allow(non_camel_case_types)]`,
so the CamelCase form draws no lint either. The CamelCase case is the realistic one — it is what a
Rust author following the language's own convention would write.

The v3 packet's mutation row states *"grow or reorder either transition reject enum in one language
only"* is killed by this node. Three members of that class survive. This is the same shape as
NEW-13 — a totality row whose scanner is narrower than the claim it certifies — recurring for a
second consecutive round, which is why I am naming the pattern and not just the instance.

Suggested fix (either is sufficient): after slicing the enum block, require every non-blank,
non-comment, non-attribute, non-brace line to parse, so an unparsed line is a failure rather than a
silent drop; or assert the parsed Rust variant count equals a pinned literal (12 and 15) in addition
to the list equality.

### NEW-17 (P3) — docstring/implementation drift in the repaired test

`test_every_canonical_rust_bound_has_a_python_twin` still documents
*"Every `pub const MAX_...` declaration in the crate's **src/\*.rs**"* while the body now uses
`rglob`. The v6 packet's `claim_scope` is correct ("the crate-wide parity scan recurses (rglob)");
only the in-file docstring is stale. Worth fixing because that exact wording is what made the P25
survivor easy to miss in the first place, and the campaign's own rule requires the docstring to
match what the test does.

### NEW-18 (P3, coverage) — family-set equality without per-member production parity

The new pin proves the two families hold the same members in the same order. It says nothing about
which input produces which member. Measured on the live tree:

- `BALANCE_OVERFLOW` is asserted by **zero** tests in **either** language, in **both** families.
- The Rust managed-lifecycle family has **6 of 15** members with no asserting Rust test:
  `BALANCE_OVERFLOW`, `BURN_DISABLED`, `DISABLED_ASSET`, `ISSUE_DISABLED`, `UNKNOWN_ASSET`,
  `UNKNOWN_COMMAND`.
- Both families otherwise cover 11 of 12 (asset) in each language.

Every member *is* constructed somewhere in both implementations, so none of them is dead code —
this is a coverage gap, not a soundness hole, and I grade it accordingly. Related and also unpinned:
no gated test compares cross-language reject **precedence** for these two families, which this
repo's own CBC rules call part of the consensus contract.

### Observation (no grade weight)

The repaired Python test file is not `ruff format`-clean; `ruff format --diff` wants to rewrap the
two long tuple lines the repair added. But the file was already not clean at R22 (one pre-existing
hunk at the managed-ceiling assert), `E501` is disabled in `pyproject.toml`, `ruff check` passes,
and `ruff format` is gated nowhere in this repo. I note only the asymmetry: this commit certifies
rustfmt cleanliness on the Rust side while adding Python that its own formatter would reformat.

## 5. Grade

**A-.** 0 P1, 0 P2, 3 P3.

For: every replay is green and reproduced from a clean detached worktree, the checker is
demonstrably non-vacuous, all pins equal committed bytes, the claim ceiling is byte-identical, the
tree was pristine after every mutation probe, and each P25 finding has a control proving the repair
— not luck — is what kills the mutant.

Against: NEW-15's mutation row still has three surviving members, each of which compiles, passes
clippy with warnings denied, and passes every other Rust and Python gate; and the underlying
pattern — a regex scanner asserted to be total over a class it does not cover — has now recurred
twice. That keeps this at the same grade as R22 rather than moving it up.

Authority: **NONE**. Nothing in this review supports raising any authority, closing any of the
twelve value-movement gates, or changing `o008_status`.
