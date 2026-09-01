# Opus review receipt: candidate C1 at P = 3b3528bacc13c65bc386dacff7e3ee6943605ca1

Reviewer: Opus 5 (independent reviewer, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-3b3528bac`).
Date: 2026-09-01. Subject: P = 3b3528bacc13c65bc386dacff7e3ee6943605ca1 (tree 8154e9153a7871c316e6b729662df03b2a3b3ec8), S = 28138402baa8d4bc46098075d9c2b3febcb60c65, base fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85.
Verdict: REVISE (concurs with the Codex band C). Disposition: P1-1 and P1-2 were repaired by candidate C1' (lexical closure, compiled/imported projection gates, closed author-record schema); P2-1, P2-2, P2-3, P2-4, P3-1, P3-3 are repaired by candidate C1''; P3-2 is answered by the python_version replay command (the recorded Python version is verified evidence, not a host fact); P3-4 is documented in rust_struct_shape_v1; P3-5 stays a recommendation (the checker's own suite is not replayed to avoid self-certification). The grade is advisory and grants no authority.

Verbatim report follows (probe scripts it names lived under the session scratchpad and are not part of the repository).

---

# C1 Review — Independent Proof, Refinement and Authority Review

**Reviewer:** Opus 5 (independent reviewer; advisory only, grants no authority)
**Subject:** P = `3b3528bacc13c65bc386dacff7e3ee6943605ca1`
**Worktree:** `/tmp/zenodex-formal-core-review-p-3b3528bac` (clean detached, read-only review)
**Date:** 2026-09-01

---

## 0. Reconciliation with the Codex review (read this first)

| Codex finding | My independent result |
|---|---|
| **P1** — `#[cfg(any())]` decoy struct + macro-generated live struct fools the textual Rust struct scan | **CONFIRMED, and it is worse than stated.** I missed this in my first pass and have now reproduced it. It also defeats the **Python AST** scanner by the same mechanism. See P1-1. |
| **P2** — fabricated author replay record survives; toolchain fields unvalidated and not compared on fresh replay | **CONFIRMED — same survivor, found independently.** This was my top finding before I saw Codex's. I also show `comparable` is unvalidated and that the `REPLAY_RECORD_MACHINE_PATH` guard is provably vacuous. See P1-2. |

Two survivors of mine that Codex did not report: the **Unicode-homoglyph defeat of the promotion-token rule** (P2-1) and the **`noUnclassified_premise_is_necessary` docstring/conclusion mismatch** (P2-2). Two more of mine are evidence-scope gaps rather than bypasses (P2-3, P2-4).

I did not find Codex's P1 on my own. My Rust adversarial pass tested `#[cfg(feature=...)]` on a *field* and duplicate struct names, and concluded "not exploitable". That conclusion was wrong: I never tested a *dead* decoy declaration paired with a live declaration that is not lexically a struct. Recording that as a miss.

---

## 1. Grade

**REVISE.** I concur with Codex's band (C).

The evidence chain is genuinely well built: 20/20 pins verified on blob-id, mode, sha256 and size against S; single-parent artifact-only P; executing-tool binding demonstrably rejects a tampered core; claim ceiling constant under every mutation I ran; 15/15 topology and ceiling attacks rejected; pure functional core with zero I/O. That work is real and should not be re-done.

It cannot be accepted because two of the packet's load-bearing claims are false as implemented:

- **Claim 3** (structural Python AST + deterministic Rust struct scan proving `liability_domain`/`custody_principal` absent) is forgeable. The V1 terminal information-loss result — the packet's headline `supported_claim` — rests on this scan.
- **Claim 5** ("the packet's author record holds only deterministic comparable values") is false, and the guard written to enforce it can never fire.

---

## 2. Findings

### P0 — none.

No authority escalation, claim-ceiling promotion, packet/subject substitution, or pin forgery survived. Explicitly: **no finding at this severity.**

---

### P1-1 — Both structural scanners read *declarations*, not the *built artifact*; a dead decoy defeats them (Codex P1, confirmed and extended)

**Files/lines:** `tools/o008_formal_cycle_admission_v1.py:1121` (`_rust_struct_body`) and `tools/o008_formal_cycle_admission_v1.py:906` (`_top_level_class`). Supporting: `:489` (`_RUST_ATTR_PREFIX_RE`), `:1190` (deny_unknown_fields test), `:954` (`_top_level_assignments`, never consulted for rebinding).

**Exact statement.** `_rust_struct_body` finds struct bodies by `re.finditer(r"\bstruct\s+" + re.escape(name) + r"\b")` over stripped source and rejects only when there is more than one *literal* match. It has no model of conditional compilation or macro expansion. So an attacker puts the expected shape in a struct that never compiles, and emits the real one from a macro. `python_class_shape_v1` has the same defect in a different dialect: `_top_level_class` takes the `ClassDef` unconditionally and never checks whether the module rebinds that name afterwards.

**Reproduction (Rust)** — `scratchpad/rev/adv9.py`, run against the real pinned `zk/global_settlement_abi_v1/src/state.rs` with the genuine literal struct removed:

```rust
macro_rules! terminal_row_v1 { ($name:ident) => {
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct $name {
        pub obligation_id: String,  pub lane_id: LaneIdV1,
        pub claimant: String,       pub asset: String,
        pub amount_atoms: u128,     pub status: TerminalObligationStatusV1,
        pub liability_domain: String,          // <-- forbidden field, LIVE
    }
}; }
terminal_row_v1!(TerminalObligationV1);

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
#[cfg(any())]                                  // <-- never compiled
pub struct TerminalObligationV1 {
    pub obligation_id: String,
    pub lane_id: LaneIdV1,
    pub claimant: String,
    pub asset: String,
    pub amount_atoms: u128,
    pub status: TerminalObligationStatusV1,
}
```

Observed output:

```
scanner sees:
  line = 476  deny_unknown_fields = True
    ('obligation_id', 'String')
    ('lane_id', 'LaneIdV1')
    ('claimant', 'String')
    ('asset', 'String')
    ('amount_atoms', 'u128')
    ('status', 'TerminalObligationStatusV1')

matches the pinned constant TERMINAL_FIELDS_RUST_V1 : True
_check_rust_record                                  : PASS  <-- decoy admitted
but the LIVE (macro) struct carries 'liability_domain': True
literal 'struct TerminalObligationV1' occurrences   : 1     <-- no RUST_STRUCT_AMBIGUOUS
```

`#[cfg(any())]` is even captured *into* `attr_text` by `_RUST_ATTR_PREFIX_RE` and silently ignored, so the cfg gate is visible to the scanner and disregarded.

**Reproduction (Python)** — `scratchpad/rev/adv10.py`. The same class reaches `python_class_shape_v1`:

```python
@dataclass(frozen=True, slots=True)
class TerminalObligationV1:
    obligation_id: str
    lane_id: LaneIdV1
    claimant: str
    asset: str
    amount_atoms: int
    status: TerminalObligationStatusV1

    def to_canonical(self):
        return {"obligation_id": ..., "lane_id": ..., "claimant": ...,
                "asset": ..., "amount_atoms": ..., "status": ...}

# The name is rebound at import time; every runtime user gets the wider record.
TerminalObligationV1 = make_dataclass(
    "TerminalObligationV1",
    [("obligation_id", str), ("lane_id", "LaneIdV1"), ("claimant", str),
     ("asset", str), ("amount_atoms", int), ("status", "TerminalObligationStatusV1"),
     ("liability_domain", str)],
    frozen=True,
)
```

Observed output:

```
scanner sees fields : ['obligation_id', 'lane_id', 'claimant', 'asset', 'amount_atoms', 'status']
frozen              : True
canonical_keys      : ('obligation_id', 'lane_id', 'claimant', 'asset', 'amount_atoms', 'status')
_check_python_record: PASS  <-- decoy admitted, live record has liability_domain
```

**Impact.** `v1_information_loss` and `terminalProjection_hasNoUniversalDomainRecovery` are scoped to "the V1 terminal projection has no domain field". That scoping is established for the *committed text* only. A subject commit can satisfy the checker while shipping a wire type that carries the domain — inverting the packet's central result and its headline `supported_claim`.

**Required repair.** Bind the check to something the build produces, not to declaration text:

1. **Rust:** add a replay command running `cargo expand -p global_settlement_abi_v1 --lib` (or a `const _: () = assert!(…)` compile-time field-count/order assertion plus a serde golden-vector round-trip) and scan the expanded output. Minimum interim fix: reject any `#[cfg(...)]` in `attr_text` outside an allowlist, and reject any `macro_rules!` definition or invocation in the pinned file.
2. **Python:** after locating the `ClassDef`, reject if the class name is rebound anywhere at module top level (`_top_level_assignments` already computes exactly this), and reject `make_dataclass` / `type(...)` construction in the pinned module.
3. **Best:** add a replay command asserting the *runtime* `dataclasses.fields()` tuple and the Rust `serde_json` schema against the pinned constants. That closes text-vs-artifact permanently and is the only version I would call proven.

---

### P1-2 — `proof_replay.author_record` is unvalidated free text; the machine-path guard can never fire (Codex P2, confirmed independently)

**Files/lines:** `tools/o008_formal_cycle_admission_v1.py:1452-1454` (vacuous guard), `:1436` (`AUTHOR_RUN_KEYS_V1`), `:1447` (command_id already closed), `:1471-1476` (`toolchain` pass-through), `:1959` (`compare_author_record_v1` compares only `comparable`).

**Exact statement.**

```python
# :1452-1454
for key, value in run.items():
    if isinstance(value, str) and value.startswith("/"):
        _reject("REPLAY_RECORD_MACHINE_PATH", f"proof_replay.author_record.runs[{index}].{key}", value)
```

`AUTHOR_RUN_KEYS_V1` closes each run to exactly `{command_id, exit_code, comparable}`. The only top-level `str` is `command_id`, which line 1447 already constrains to the closed `REPLAY_COMMAND_IDS_V1`. The loop therefore inspects nothing reachable — **the guard is provably vacuous**. `comparable` is a nested value and is **never type-checked or content-checked at all**.

Line 1471-1476 is worse:

```python
if set(record) != {"status", "runs", "toolchain"} or not isinstance(runs, list):
    _reject(...)
...
return {"status": "EXECUTED", "runs": validated, "toolchain": record["toolchain"]}
```

`toolchain` need only be *present*; it is returned verbatim into the projection, and `compare_author_record_v1` compares only `comparable`. So `toolchain` is unverified **even under `--replay`**.

Because `check_projection_v1` derives the expected packet *from the packet's own author record*, these two fields are the entire free-text surface of an artifact whose thesis is "deterministic projection of S".

**Reproduction** — `scratchpad/rev/adv2.py` and `adv6.py`, end-to-end through `admit_packet_v1` against the real `SubjectSnapshotV1` at S with real executing-tool hashes:

```
machine path nested in comparable          admitted=True  applicable=True errors=[]
comparable is a list with a path           admitted=True  applicable=True errors=[]
   markdown_identical_to_committed=True       <-- invisible in the human companion
toolchain.lean = /home/trevormoc/.elan/...  admitted=True  errors=[]
toolchain gains an arbitrary key            admitted=True  errors=[]
toolchain replaced by a bare string         admitted=True  errors=[]
toolchain.lean version lies (9.9.9)         admitted=True  errors=[]
toolchain.solvers lies (z3 0.0.1)           admitted=True  errors=[]
```

Committed value for reference:
`{'esso_code_hash': '7f80c6216be85c827e8d1cc2fa08ee3107a74588', 'lean': '4.27.0', 'python': '3.12.3', 'solvers': {'cvc5': '1.1.2', 'z3': '4.15.4'}}`

The last two rows are the integrity failure: a packet is admitted with `ok:true`, exit 0, while its author record says `z3: 0.0.1` and its own `esso_evidence.solvers` says `z3: 4.15.4`. **Self-contradictory published evidence passes the gate.** Machine paths and credential-shaped strings in a committed doc also violate `tools/AGENTS.md` ("Never package secrets, local scratch, MCP configs, internal solver reports, browser state, or machine-specific paths") and `docs/AGENTS.md` ("avoid local paths, private tool state, solver scratch").

**Required repair.** Close both objects from constants already in the module:

- `toolchain`: closed key set `{lean, solvers, esso_code_hash}`; require `lean == LEAN_TOOLCHAIN_V1.rsplit("v",1)[1]`, `solvers == ESSO_SOLVERS_V1`, `esso_code_hash == ESSO_CODE_COMMIT_V1`. **Drop `python`** — it is a host fact nothing verifies, and removing it also fixes P3-2.
- `comparable`: closed per-`command_id` key set with typed values (the six shapes `_grade_lean` / `_grade_pytest` / `_grade_esso` already emit).
- Then recurse the machine-path/token scan over whole runs, or delete it as redundant once the shapes are closed.

---

### P2-1 — the forbidden-promotion-token rule is defeated by a Unicode homoglyph while the packet file stays pure ASCII

**File/line:** `tools/o008_formal_cycle_admission_v1.py:1686`, inside `check_nonclaims_v1` (`:1675`). Constant list at `:309` (`FORBIDDEN_PROMOTION_TOKENS_V1`).

**Exact statement.**

```python
# :1686
folded = " ".join(text.split()).lower()
hits = [token for token in FORBIDDEN_PROMOTION_TOKENS_V1 if token in folded]
```

This case-folds and whitespace-folds but does **not** normalize. `canonical_packet_bytes_v1` (`:772`) uses `ensure_ascii=True` then `.encode("ascii")`, so a non-ASCII character survives in the *decoded* string as a `\uXXXX` escape while the committed file remains pure ASCII bytes. The scan compares ASCII-hyphen tokens against a string carrying a different code point.

**Reproduction** — `scratchpad/rev/adv3.py`, full end-to-end `admit_packet_v1`, injecting the note into `author_record.runs[2].comparable.note`. Exact inputs and results:

| exact input string | admitted | errors | file is pure ASCII |
|---|---|---|---|
| `O-008 complete` (U+002D HYPHEN-MINUS) | **False** | `['PROMOTION_TOKEN_PRESENT']` | True |
| `O‑008 complete` (U+2011 NON-BREAKING HYPHEN) | **True** | `[]` | True |
| `O‐008 complete` (U+2010 HYPHEN) | **True** | `[]` | True |
| `ｏ-008 complete` (U+FF4F FULLWIDTH LATIN SMALL LETTER O) | **True** | `[]` | True |
| `production ready` (all ASCII) | **False** | `['PROMOTION_TOKEN_PRESENT']` | True |
| `production ready` (NBSP) | **False** | `['PROMOTION_TOKEN_PRESENT']` | True |

NBSP is **not** a bypass — Python's `str.split()` splits on Unicode whitespace, so whitespace folding already handles it. The gap is specifically un-normalized hyphen and letter forms. As committed bytes these appear as `O‑008 complete`, `O‐008 complete`, `ｏ-008 complete`.

**Blast radius.** Bounded to the P1-2 surface: `comparable` and `toolchain` are the only free-text landing zones, because every other packet string is pinned by `check_projection_v1` to a module constant (only `created_date` is otherwise free, and it is regex-constrained by `_DATE_RE`). But the rule is stated as covering the packet, and it does not.

**Required repair.** `unicodedata.normalize("NFKC", text)` before folding, and additionally reject any string in the packet outside a closed ASCII charset. Do not rely on a blocklist of code points.

---

### P2-2 — `noUnclassified_premise_is_necessary` does not state necessity

**File/line:** `lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean:261`. Packet binding: `lean_evidence.theorems[7]`, `statement_sha256 = 093e250f39dd9a436ceb4e4e85f2861d934b4d83934d6ad8c2401b0157a0e095`. Constant: `THEOREM_INVENTORY_V1[7]` at `tools/o008_formal_cycle_admission_v1.py:375+`.

**Exact statement as shipped:**

```lean
/-- The `noUnclassified` premise of
`exactAllocation_noUnclassified_implies_exactCurrentProfileRelation` cannot be
dropped: `overCollateralisedAllocation` is a well-formed exact allocation
witness whose hot unencumbered-custody bucket is four, not zero, and
`overCollateralised_isBacked_notExact` shows its state fails exact
current-profile custody. -/
theorem noUnclassified_premise_is_necessary :
    ¬ ∀ domain, overCollateralisedAllocation.unencumberedCustody domain = 0 := by
  intro allZero
  have hotUnclassified :
      overCollateralisedAllocation.unencumberedCustody .hot = 4 := rfl
  have hotZero := allZero .hot
  omega
```

The conclusion asserts only that one literal function is nonzero somewhere. It names no relation, no state, and no premise of the theorem it claims to justify. The necessity argument exists solely as docstring prose ("and `overCollateralised_isBacked_notExact` shows its state fails exact current-profile custody"); the conjunction is never formed as a theorem. The proof derives nothing about `ExactCurrentProfileRelation` at all — it is `rfl` plus `omega` on a literal.

This fails both CLAUDE.md **Test 2** (docstring alignment: the theorem's conclusion must match the English claim) and **Test 3** (the 5-second test).

**Required repair — verified to compile.** I appended the following to a copy of the file in the scratchpad and ran `lake env lean -DwarningAsError=true`, which returned **exit 0 with no output**:

```lean
theorem noUnclassified_premise_is_necessary :
    ¬ ∀ (s : State) (_ : ExactAllocationWitness s), ExactCurrentProfileRelation s := by
  intro universal
  exact overCollateralised_isBacked_notExact.2
    (universal overCollateralisedState overCollateralisedAllocation).2
```

This states the actual necessity claim: there exists a state with a well-formed exact allocation witness that fails the exact current-profile relation. Applying it changes `lean_evidence.theorems[7].statement_sha256`, so the packet must be rebuilt and re-cut at a new S/P pair.

**For the record**, `overCollateralised_isBacked_notExact` (line 229) **does** genuinely separate R1 from R3 — hot custody 10 against hot liability 6 satisfies `SameDomainLiabilitiesBacked` and refutes `ExactCurrentProfileCustody`, and its docstring states exactly that. That theorem is sound and its name matches its conclusion.

---

### P2-3 — `completion_scope` asserts Rust rejection behavior that nothing executes

**File/lines:** `tools/o008_formal_cycle_admission_v1.py:170-176` (`COMPLETION_SCOPE_V1[0]` and `[1]`).

**Exact statement.** The packet publishes:

- `"Python and Rust reject V1-state-visible same-control-domain claimant underbacking"`
- `"Python and Rust reject aggregate OPEN-terminal amounts above the same claimant's visible entitlements"`

The **Python** half is backed: `tests/formal/test_esso_global_claimant_custody_certificate_v1.py:254` (`test_runtime_rejects_aggregate_only_cross_domain_backing`) and `:271` (`test_runtime_rejects_reserve_masking_as_claimant_backing`) import `src.core.global_economic_state_effect_refinement_v1` and run in the replay set as `esso_gate` (18 tests).

The **Rust** half is not executed by anything. `REPLAY_COMMANDS_V1` contains no `cargo` invocation. `zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs` is source-pinned only. The restage gate states this itself at `tests/formal/test_esso_global_settlement_core_v1.py:120`:

> `# Enforced source pins: blueprint row, this table, and the file must agree.`
> `# Claim grade is source-pin evidence, never refinement evidence.`

No nonclaim carves this out. This compounds P1-1: the Rust side is neither executed nor structurally trustworthy.

**Reproduction:** `grep -n 'cargo\|rustc' tests/formal/test_esso_global_claimant_custody_certificate_v1.py tests/formal/test_esso_global_settlement_core_v1.py` — the only hits are `tool_versions` banner-string assertions, never an invocation.

**Required repair (the evidence already exists).** Add a replay command running `zk/global_settlement_abi_v1/tests/global_economic_state_effect_refinement.rs` (61 test functions; covers `claimant_relation_state` at line 262) with a pinned pass count; or reword `COMPLETION_SCOPE_V1[0..1]` to state that the Rust side is source-pinned and structurally checked but not executed, and add a matching nonclaim.

---

### P2-4 — ESSO replay never verifies that any query ran

**File/lines:** `tools/o008_formal_cycle_admission_v1.py:1886-1888` (`_grade_esso`, defined at `:1871`); `ESSO_QUERIES_V1` at `:339`.

**Exact statement.**

```python
# :1886-1888
verified = report.get("verdict") == "VERIFIED" and report.get("solvers_agreed") is True
if not verified or report.get("failed_queries") != 0 or report.get("inconclusive_queries") != 0:
    _reject("REPLAY_ESSO_VERDICT", obs.command_id, str(report.get("verdict")))
```

The ESSO report also carries `total_queries` and `passed_queries` (confirmed present in the real output: `total_queries: 3`). Neither is compared. A verification that ran **zero** queries satisfies `failed_queries == 0` and `inconclusive_queries == 0` and grades clean.

Separately, `ESSO_QUERIES_V1` — the three query names the packet publishes as evidence (`init_implies_inv`, `inductive_open_claim`, `inductive_drain_claim`) — is a bare module constant. It is not read from the model yaml (which has top-level keys `ir_version, meta, observables, types, state_vars, init, invariants, actions` and **no `queries` section**) and is never compared to the replay report.

**Reproduction** — `scratchpad/rev/adv8.py`, feeding `_grade_observation` a synthetic report:

```
report total_queries=0, passed_queries=0, failed_queries=0, inconclusive_queries=0
  -> graded: {'verdict': 'VERIFIED', 'fingerprint': 'e377059…', 'solvers': {'cvc5':'1.1.2','z3':'4.15.4'}}
     # accepted — ZERO queries graded VERIFIED
```

Residual risk in practice is low (5 pinned invariants + 2 pinned actions + a pinned `esso_code_hash` determine the 3 queries), but the packet states a value nothing checks.

**Required repair.** Assert `report["total_queries"] == report["passed_queries"] == len(ESSO_QUERIES_V1)` in `_grade_esso`.

---

### P3-1 — `_split_depth_zero_commas` treats `>` as a closing delimiter and silently drops fields

**File/line:** `tools/o008_formal_cycle_admission_v1.py:1146` (function at `:1141`).

```python
depth += {"(": 1, "[": 1, "<": 1, ")": -1, "]": -1, ">": -1}.get(char, 0)
```

`->` in a field type drives depth negative, so the following commas no longer split. Injecting `pub cb: fn(u8) -> u8,` yields `fields=['obligation_id','lane_id','cb']` — four fields silently swallowed into `cb`'s type string, with no reject (`scratchpad/rev/adv5.py`).

Not exploitable on its own: any `>` an attacker inserts lands inside a field's type string, so the parse can never coincide with `TERMINAL_FIELDS_RUST_V1`, and `_check_rust_record` rejects. Comments and strings are blanked, so no `>` survives there. The defect is that the scanner reports a wrong shape instead of `RUST_FIELD_UNPARSEABLE`.

**Repair:** track only `(` / `[`, or skip `>` when preceded by `-`.

### P3-2 — builder `--check --replay` is host-Python-patch-version sensitive

**File/line:** `tools/build_o008_formal_cycle_v1.py`, `_author_record`, `"python": sys.version.split()[0]`.

The committed packet pins `3.12.3`. A rebuild on 3.12.4 reports drift with byte-identical proofs, and the checker never validates the field. My `--check --replay` passed only because this host is Python 3.12.3. Subsumed by the P1-2 repair (drop `python` from the record).

### P3-3 — four disclosed-definitional theorems inside `theorem_count: 25`

`lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean:124` and `:136` (`Iff.rfl`), `:293` and `:363` (`rfl`). Each docstring honestly discloses the proof term and why ("The proof is `Iff.rfl` because neither R1 nor R2 reads `State.reserves`"), so this is not concealed padding. But `COMPLETION_SCOPE_V1` says "Lean **proves** … reserve independence", and per CLAUDE.md's report-both rule the honest figure is **21 substantive theorems, 25 total including 4 disclosed-definitional**.

The other 21 are real: both `exactAllocation_implies_*` derivations (`rw` + `omega` from partition equalities), the deposit/drain preservation family with genuine case analysis and explicit truncation-avoidance premises, three forward implications each paired with a minimized converse counterexample (`aggregateOnly_permits_crossDomainBacking`, `aggregateClaimants_permit_claimantSwap`, `reserveInclusiveBacking_permits_missingExactCustody`), and the erasure chain ending in `terminalProjection_hasNoUniversalDomainRecovery`, whose conclusion (`¬ ∃ recover, Function.LeftInverse recover eraseLiabilityDomain`) matches its name exactly.

### P3-4 — `deny_unknown_fields` is a literal substring test

**File/line:** `tools/o008_formal_cycle_admission_v1.py:1190` — `deny_unknown_fields="#[serde(deny_unknown_fields)]" in attr_text`.

Confirmed: `#[serde(deny_unknown_fields, rename_all = "camelCase")]` yields `deny=False` → reject, even though it is semantically equivalent. Fail-closed and therefore safe, but a benign serde-argument merge breaks the packet. Document the strictness as deliberate.

### P3-5 — the checker's own 136-test mutation matrix is not in the replay set

`tests/test_check_o008_formal_cycle_v1.py` (136 tests) is source-pinned with role `admission_gate_tests` but is never executed by `--replay`. There is a genuine circularity argument against including it, and the executing-tool hash check already binds the checker bytes. Raised as a recommendation, not a defect.

---

## 3. Verification record

### 3.1 Subject and topology

```
git status --porcelain                    -> empty (clean)
git rev-parse HEAD                        -> 3b3528bacc13c65bc386dacff7e3ee6943605ca1   (P)
git rev-parse HEAD^                       -> 28138402baa8d4bc46098075d9c2b3febcb60c65   (S)
git rev-parse HEAD^{tree}                 -> 8154e9153a7871c316e6b729662df03b2a3b3ec8
git rev-parse HEAD^^                      -> fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85   (base)
git cat-file -p HEAD                      -> exactly ONE parent line (= S)
```

`git diff-tree --no-commit-id --name-status -r HEAD^ HEAD`:

```
M	docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
M	docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
```

P is artifact-only, exactly as declared.

`git diff --stat HEAD^^ HEAD^` (S's write set) — matches the declared 8 paths:

```
 lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean    |  171 +-
 tests/evidence/test_hygiene/THV1-...-o008-formal-cycle-admission-v2.json |  421 ++++
 tests/formal/test_lean_global_claimant_custody_relation_v1.py |   40 +-
 tests/test_check_o008_formal_cycle_v1.py                   |  885 ++++++--
 tools/build_o008_formal_cycle_v1.py                        |  149 ++
 tools/check_o008_formal_cycle_v1.py                        |  452 ++---
 tools/o008_formal_cycle_admission_v1.py                    | 2125 ++++++++++++++++++++
 tools/o008_formal_cycle_shell_v1.py                        |  366 ++++
 8 files changed, 4138 insertions(+), 471 deletions(-)
```

Name-status: `M, A, M, M, A, M, A, A` — matches the declaration (A/M per path as briefed).

### 3.2 Toolchain

```
Python 3.12.3
pytest 9.0.3
ruff 0.15.13
mypy 1.20.2 (compiled: yes)
Lean (version 4.27.0, x86_64-unknown-linux-gnu, commit db93fe1608548721853390a10cd40580fe7d22ae, Release)
git version 2.55.0
ESSO 7f80c6216be85c827e8d1cc2fa08ee3107a74588
z3 4.15.4, cvc5 1.1.2
```

### 3.3 Commands run

| command | exit | key output |
|---|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD` | 0 | `ok:true`, `packet_admitted:true`, `current_applicable:true`, `proof_replay.status:"NOT_RUN"`, `errors:[]`; stdout sha256 `db266ea5711daef575fcb416efb1e85debe058b08e7f215656a2d7af5ece9f9d` |
| `check_o008_formal_cycle_v1.py --root $PWD --replay --python … --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO` | 0 | `proof_replay.status:"EXECUTED_PASS"`, 8 runs, `errors:[]`, no `REPLAY_AUTHOR_RECORD_DRIFT`; stdout sha256 `f045fb6009faf74db5ff9136f93c81077ed76e441984ea853cb99fe5d3fcbfb8` |
| `build_o008_formal_cycle_v1.py --root $PWD --subject-commit 28138402… --created-date 2026-09-01 --check --replay …` | 0 | `{"drift":[],"mode":"check","ok":true,"subject_commit":"28138402…"}`; stdout sha256 `a9efa4ad0957a9f34d481031aa11d430bea2a581a7f3be531edae10919b4e3a6` |
| `pytest -q tests/test_check_o008_formal_cycle_v1.py tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 0 | `142 passed in 46.35s` (136 + 6) |
| `PYTHONPATH=… ZENO_ESSO_PYTHON=… pytest -q tests/formal/test_esso_global_claimant_custody_certificate_v1.py` | 0 | `18 passed in 19.13s` |
| `cd lean-mathlib && lake env lean -DwarningAsError=true Proofs/GlobalClaimantCustodyRelationV1.lean` | 0 | empty stdout **and** empty stderr |
| `scan_lean_proof_placeholders_v1.py lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean --json` | 0 | `{"blocked": false, "match_count": 0, "matches": [], "axiom_check": true, "error": null}` |
| `ruff check` (core, shell, cli, builder, gate tests) | 0 | `All checks passed!` |
| `mypy --strict` (core, shell, cli, builder) | 0 | `Success: no issues found in 4 source files` |
| `check_test_hygiene_v1.py --base-ref 28138402… --json` | 0 | clean |
| `check_test_hygiene_v1.py --base-ref fd409ba6… --json` | 0 | selects `THV1-20260901-o008-formal-cycle-admission-v2` |

Replay run detail (from the `EXECUTED_PASS` report): `lean_version` → `4.27.0`; `lean_direct_check` → `stdout_sha256 e3b0c442…` (empty); `lean_axioms_probe` → `probe_sha256 a2aa2c92…`, `theorems_probed 25`; `lean_binding_gate` → `passed 6`; `esso_validate` → `ir_hash sha256:a4d1d07f6c9d9587e3848599ebdd9fdb0a4126d6c3c8f217b12249106e7b9dcf`; `esso_verify_multi` → `verdict VERIFIED`, `fingerprint e37705902eb04f48aee9ab1fac333396b80a317716aeb64f51ebdb72cb3fde82`, `solvers {cvc5 1.1.2, z3 4.15.4}`; `esso_gate` → `passed 18`; `prior_restage_gate` → `passed 136`. All eight `exit_code: 0`, all eight `comparable` values equal to the committed author record.

### 3.4 Hand-recomputed pins (as commanded)

```
git cat-file blob HEAD^:lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean | sha256sum
  -> 12c75fbe47896ec2308f010a33aa0a02260ad886971c4975cfaeebb269e6228c
     == packet source_pins[6].sha256                                    MATCH

git ls-tree HEAD^ -- lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean
  -> 100644 blob 67e2ec8514d87518f62ea308b2e225a401f79213
     == packet source_pins[6].mode / .git_blob                          MATCH

git cat-file blob HEAD^:tools/check_o008_formal_cycle_v1.py | sha256sum
  -> e8f131c750dc150f9fc176b2c07f258a6038a5c223de469ae77c24cc4e9307e6
     == packet source_pins[13].sha256                                   MATCH

git ls-tree HEAD^ -- tools/check_o008_formal_cycle_v1.py
  -> 100644 blob d41e1616c5418fabea4d8e61fdcd4d4fa6614478
     == packet source_pins[13].mode / .git_blob                         MATCH
```

**All 20 pins** were then verified programmatically against the S blobs on all four attributes (blob oid, mode, sha256, size): `pins checked: 20`, `MISMATCHES: NONE`.

All seven sha256 values supplied in the review brief reproduce exactly on the worktree files:

```
443a2d3c118dcf3ecbcc6a83ca706fb245528cd5aa960183b2f8b72e65961859  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
fa165c32257ba39c6223ea516055b62f65e665a30b3f299e626aa19c03d229aa  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
e8f131c750dc150f9fc176b2c07f258a6038a5c223de469ae77c24cc4e9307e6  tools/check_o008_formal_cycle_v1.py
5fcffbc760b1529a15974378ee1af4822bb56c4cf401daf5ee68103ff6401f26  tools/o008_formal_cycle_admission_v1.py
f4355f5636da2ef7c1cc26d69fcf4ee8fc71f55b551a3a475b754022b5a0478b  tools/o008_formal_cycle_shell_v1.py
0127d01b9739639dbc11bedf7ba4f53b5d589794ae6d94b2d4f6c502b40fa433  tools/build_o008_formal_cycle_v1.py
44a7c67142955ad3b7a803ab599d31ca8754d0f9cdd795588ea9745f58239fc4  tools/scan_lean_proof_placeholders_v1.py
```

### 3.5 Adversarial attempts rejected as designed (15/15)

| attack | reject code |
|---|---|
| P has two parents | `PACKET_PARENT_NOT_SUBJECT` |
| P's parent is not S | `PACKET_PARENT_NOT_SUBJECT` |
| P also touches a third path | `PACKET_ENVELOPE_DRIFT` |
| P deletes the markdown | `PACKET_ENVELOPE_DRIFT` |
| P not in HEAD history | `PACKET_NOT_IN_HEAD_HISTORY` |
| HEAD packet differs from P | `CURRENT_PACKET_DRIFT` |
| worktree packet differs from P | `WORKTREE_PACKET_DRIFT` |
| markdown at P is not the rendering | `MARKDOWN_PROJECTION_DRIFT` + `CURRENT_PACKET_DRIFT` |
| `value_movement_gates_closed` `0` → `False` (type confusion) | `VALUE_MOVEMENT_PROMOTION` |
| `formal_core_complete` `False` → `0` (type confusion) | `FORMAL_CORE_PROMOTION` |
| extra authority field in `claim_ceiling` | `CLAIM_STATUS_DRIFT` |
| `value_movement_gates_closed` `0` → `12` | `VALUE_MOVEMENT_PROMOTION` |
| lane status outside vocabulary (`COMPLETE`) | `LANE_STATUS_NOT_IN_VOCABULARY` |
| lane status changed within vocabulary | `LANE_MAP_DRIFT` |
| author record run with nonzero exit | `REPLAY_RECORD_EXIT_NONZERO` |
| author record runs out of order | `REPLAY_RECORD_SHAPE` |
| `NOT_RUN` record carrying `runs` | `REPLAY_RECORD_SHAPE` |
| author status `EXECUTED_PASS` (report vocabulary) | `REPLAY_RECORD_STATUS_INVALID` |

### 3.6 Positive properties verified

**Executing-tool binding — verified by construction.** A byte-appended copy of the core, run against the clean worktree:

```
ok= False exit= 1
errors= [('EXECUTING_CORE_DRIFT', 'tools/o008_formal_cycle_admission_v1.py')]
```

**Pure core — verified.** `tools/o008_formal_cycle_admission_v1.py` imports only `ast, functools, hashlib, json, re, collections.abc, dataclasses, typing, yaml` plus `tools.scan_lean_proof_placeholders_v1`. No `os`, `subprocess`, `open`, `time`, `datetime`, `random`, `environ`, `getenv`, network, or filesystem access anywhere in the module. Every effect lives in the shell.

**Author record cannot upgrade the report — verified.** Plain (non-`--replay`) run emits `"proof_replay":{"runs":[],"status":"NOT_RUN"}` despite the committed author record carrying `status: EXECUTED`. `render_report_v1` sources `proof_replay.status` from the fresh evaluation only.

**Claim ceiling is constant — verified.** `render_report_v1` emits `dict(CLAIM_CEILING_V1)` unconditionally; the reported ceiling was byte-identical across every mutation above, including on rejected reports.

**Lean inventory is ordered and statement-bound — verified.**

| mutation | effect |
|---|---|
| weaken `terminalProjection_hasNoUniversalDomainRecovery` to `True` | `theorems[24].statement_sha256` `80771422…` → `6dd041b9…` |
| rename `overCollateralised_isBacked_notExact` | caught by `THEOREM_INVENTORY_V1` name mismatch |
| flip `amount ≤ state.custody domain` to `state.custody domain ≥ amount` | `theorems[13].statement_sha256` `e702b067…` → `a229ef68…` |
| add a `private theorem` | `LEAN_PRIVATE_THEOREM_FORBIDDEN` |
| theorem inside a block comment | correctly invisible (no inventory change) |

**Rust scanner — held on every other axis tested.** Nested block comments, raw strings containing `}`, `#[cfg(feature=…)]`-gated *fields* (detected), lifetimes (`'de`, `'a`), appended fields (detected), duplicate literal struct names (`RUST_STRUCT_AMBIGUOUS`), `deny_unknown_fields` removed (fail-closed), attribute detached from the struct (fail-closed). Only P1-1 and P3-1 failed.

**Replay parsers — fail-closed.** `parse_pytest_summary_v1`: `"5 passed, 1 failed"` → `None`; `"1 error"` → `None`; `"6 skipped"` → `None`; `"6 passed, 1 xfailed"` → `None`; `""` → `None`; `"6 passed, 2 skipped"` → `6` (skips cannot inflate a pinned count, so a skipped test still drives the count below 6/18/136 and rejects). `parse_esso_json_v1` falls back to stderr only when stdout is blank.

**Test counts confirmed.** `tests/test_check_o008_formal_cycle_v1.py` → `136 tests collected`; `tests/formal/test_lean_global_claimant_custody_relation_v1.py` → `6 tests collected`; `tests/formal/test_esso_global_settlement_core_v1.py` → `136 tests collected`. Both files independently have 136 tests; `PRIOR_ESSO_GATE_EXPECTED_PASSED_V1 = 136` correctly refers to the latter. **No constant confusion.**

**Normative vocabulary matches the source of truth.** `required_sidecar.normative_partition` reproduces `docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md:172-175` verbatim: `controlled_atoms = claimant_entitlements + named_unencumbered_reserves + pending_registered_external_obligations`.

**ESSO mutant attribution present.** `tests/formal/test_esso_global_claimant_custody_certificate_v1.py:385-425` carries exact query + invariant attribution per mutant (e.g. `accept_without_global_root_binding` → `inductive_open_claim` / `inv_accept_requires_exact_bound_evidence`), satisfying handoff review duty 3.

### 3.7 Probe scripts

All in `/tmp/claude-1000/-home-trevormoc-Downloads-Autonomous-Tau-DEX/37cec583-0c57-4fc0-844c-9f17c86c9adf/scratchpad/rev/`:

| script | purpose |
|---|---|
| `adv1.py` | author-record validation surface |
| `adv2.py` | end-to-end admission bypass (machine path in `comparable`) |
| `adv3.py` | Unicode-homoglyph promotion-token defeat |
| `adv4.py` | Lean inventory statement binding |
| `adv5.py` | Rust scanner stress (9 constructs) |
| `adv6.py` | `toolchain` field validation |
| `adv7.py` | topology and claim-ceiling attacks |
| `adv8.py` | replay parsers and vacuous-ESSO grading |
| `adv9.py` | **cfg-decoy + macro Rust bypass (Codex P1 confirmation)** |
| `adv10.py` | **Python decoy-class bypass (extension of Codex P1)** |
| `Repair.lean` | verified P2-2 Lean repair (`lake env lean -DwarningAsError=true` exit 0) |
| `plain.out`, `replay.out`, `build.out`, `gates.txt` | captured checker/builder/gate outputs |

---

## 4. Nonclaims and residual risks

- **ACCEPT/REVISE here is advisory.** I certified nothing and flipped no gate. I edited no file in the repository or the review worktree; `git status --porcelain` is still empty. All probes ran in the session scratchpad. I wrote nothing under `/dev/shm`.
- I did **not** audit the Python or Rust refinement guards for arithmetic parity, checked-u128 behavior, pre/post-state enforcement, rejection precedence, or no-effect semantics (handoff review duty 4). P1-1 and P2-3 are the parts of that duty this packet touches.
- I did **not** review the twelve lane producers, `GlobalAccountingAllocationCertificateV1` mounting, route/epoch/RISC0 receipt binding, versioned journal admission, or commit-port enforcement. The packet correctly claims none of them and lists them under `verifier_authority_requires`.
- The ESSO and Lean results are **bounded-model** results: one asset, two control domains, two claimants, at most eight atoms per cell; natural-number atoms with no canonical bytes, cryptographic roots, finite-width overflow, runtime refinement, or authority. Both `claim_boundary` fields state this accurately.
- `_project_esso` reads `RECORDED_FINGERPRINT` via `constants.get(..., "")` with no format validation, unlike `RECORDED_IR_HASH` which is checked for the `sha256:` prefix and 64 hex chars. A missing constant would yield `""`, which replay would then reject on fingerprint drift. Fail-closed; noted, not ranked.
- `_canonical_keys` (`:927`) selects the first dict-returning `Return` in `ast.walk` order, not source order. Deterministic for a fixed AST, but it would select arbitrarily if `to_canonical` ever gained a second return statement.
- `read_executing_tools_v1` hashes the tool files on disk *after* import. A crafted stale `.pyc` whose mtime/size match is a theoretical TOCTOU gap I did not attempt.
- My P1-1 reproduction uses `#[cfg(any())]` and `make_dataclass`. I did **not** enumerate the full space of dead-code cfgs (`#[cfg(test)]`, `#[cfg(feature = "never")]`, dead `mod` blocks, `#[cfg(target_os = …)]`) or of Python decoy mechanisms (metaclass rewriting, `__init_subclass__`, decorator field injection, conditional class definition under `if TYPE_CHECKING`). **Treat the repair as needing a build-derived check, not a blocklist.**
- I did not attempt attacks requiring write access to the Git object store, a hostile `git` binary on `PATH`, or a compromised `yaml`/`hashlib`.
- Two files independently having exactly 136 tests is a coincidence I verified rather than assumed; if either count changes, `PRIOR_ESSO_GATE_EXPECTED_PASSED_V1` and the gate expectation must be re-derived separately.

---

## 5. User decisions — honored

| Decision | Status |
|---|---|
| **Reserves are the claimant-free term** | **Honored.** `RESERVE_INTERPRETATION_V1 = "NAMED_UNENCUMBERED_NO_CLAIMANT"`; `NORMATIVE_PARTITION_V1` reproduces the claim doc's lines 172-175 verbatim; Lean's R3 (`ExactCurrentProfileCustody`) excludes `State.reserves`, and reserve-inclusive backing survives only as the strictly weaker relation refuted by `reserveInclusiveBacking_permits_missingExactCustody`. |
| **Control-domain vocabulary in new code; V1 wire names byte-stable** | **Honored in intent; weakened in enforcement by P1-1.** `VOCABULARY_V1` is the six control-domain terms (`control_domain`, `controlled_location`, `controlling_principal`, `claimant_entitlement`, `unencumbered_reserve`, `pending_external_obligation`); `preserves_global_state_v1_wire_bytes: true`; `TERMINAL_FORBIDDEN_FIELDS_V1` blocks `control_domain` and `custody_domain` as well as `liability_domain` from the V1 type, so the new vocabulary cannot leak into the wire — but that blocklist is applied to a forgeable scan. |
| **O-008A proceeds unattested** | **Honored.** No attestation surface anywhere in the packet, checker, or write set. |
| **UP-01..UP-20 stay unresolved** | **Honored.** No `UP-` reference appears in S's or P's write set. |
| **Keep the handoff file names; bump the packet schema to v2** | **Honored.** Paths unchanged (`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` / `.md`); schemas `zenodex/o008-formal-cycle-evidence/v2` and `zenodex/o008-formal-cycle-admission-report/v2`. |
| **No fixture policy selection** | **Honored.** Every policy value is a module constant; `check_projection_v1` requires canonical byte equality between the committed packet and the constant-derived projection of S. |
| **Authority NONE** | **Honored and constant.** All seven authority fields `NONE`; `formal_core_complete: false`; `whole_value_movement_safe: false`; `0/12` value-movement gates; `o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`. Emitted from `CLAIM_CEILING_V1` in `render_report_v1` and unreachable from packet content — confirmed across every mutation I ran, including on rejected reports. |

The one substantive drift from the user's framing is **P2-3**: `completion_scope` claims Rust rejection behavior the packet does not execute. That is a wording-or-evidence gap, not a policy reversal.

---

## 6. For the next candidate

**Byte-changing repairs required:**

1. **P1-1** — both structural scanners. This is the one that needs *design*, not patching. A blocklist of cfg/macro forms is a stopgap; binding the check to `cargo expand` output, or to runtime `dataclasses.fields()` plus serde golden vectors executed in the replay set, is the version I would call proven.
2. **P1-2** — close `toolchain` and `comparable` from existing constants; drop `python`.
3. **P2-2** — replace the `noUnclassified_premise_is_necessary` statement with the verified stronger form.

**Few-line repairs:** P2-1 (NFKC + closed ASCII charset), P2-3 (add a `cargo test` replay command or reword + add a nonclaim), P2-4 (assert `total_queries == passed_queries == len(ESSO_QUERIES_V1)`).

**Low priority:** P3-1 (`>` depth), P3-4 (document the deny_unknown_fields strictness), P3-5 (consider adding the gate suite to replay).

Rebuilding after the P2-2 Lean edit re-derives `lean_evidence.theorems[7].statement_sha256`, so the packet must be re-cut at a new S/P pair and **this review's hash is then void**.
