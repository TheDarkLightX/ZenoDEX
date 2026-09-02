# Fable review P31 / C8-p12 — ZenoDEX Formal Functional Core Closure Campaign

| Field | Value |
| --- | --- |
| Subject (S31) | `048a3747ecd4a88c9672bd07d856a7fedac41c1a` "security: repair the Opus P29 review findings" |
| Subject parent | `2e6894f33a1ce6465d2eb8efa35ddee6be106ea5` (R26, the committed Opus P29 receipt) |
| Subject tree | `1b47bc838f34dfccd36af30ad3bae9a7dc20466f` |
| Artifact (P31) | `a4258d9891d1cd738f014c87c7eaa8de8cd6576a` "docs: freeze the O-008 formal-cycle packet at C8-p12" |
| Packet sha256 | `698430a234e1bcfec913bd3036d26631b67b27445b22808b9b89ca7e52cd7fe0` (recomputed from `git show a4258d989:docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`) |
| Branch | `codex/formal-core-fable-20260901` |
| Review worktree | `/tmp/zenodex-formal-core-fable-review-c8p12` (detached at P31; `git status --short` empty at start, after every restored probe, and at the end) |
| Reviewer | Fable 5.1, second independent reviewer. **Independence caveat:** the author is also a Fable 5.1 session; I share a model family with the author but no transcript, worktree, scratchpad, or notes. I did not read `/tmp/claude-1000`, and I did not touch the other reviewers' worktrees. |
| Date | 2026-09-02 |
| Authority granted | **NONE** (advisory review; claim ceiling unmoved; ACCEPT would be advisory in any case) |

**Verdict: REVISE — grade B-.** 1 P1, 1 P2, 1 P3, plus two observations.

Three of the four P29 findings are closed at the level they were stated (NEW-25
instance, NEW-23, NEW-22), and the outer-level NEW-24 probes F1–F5 are refused. The
mechanics are real: every new mutation killer kills, all 84 THV1 pins and all 48
packet pins match, the 29-command replay passes, and the claim ceiling is
byte-identical to P29 and P30. But the candidate reproduces the P29 P1 one level
out: S31 re-pins the closure digest in a tool that a hygiene packet shipped in S30
still pins at the old bytes, so the repository hygiene gate is red against the
series base the lead asked for, and the P31 packet itself binds that stale packet
in its `hygiene_selection`. And the NEW-24 repair is shallower than its own
comment says: `dataclasses.replace` re-runs the outer `__post_init__` only, so a
same-type forged nested policy or supply row is accepted into a "constructed"
post-state, while the repository already owns the deep snapshot idiom one level
up in the lane wrapper.

---

## 1. Environment and provenance

Toolchain: Python 3.12.3 (`/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`,
`PYTHONDONTWRITEBYTECODE=1`), Lean 4.27.0 via `lake env lean`, cargo/rustc 1.87.0
(`CARGO_TARGET_DIR=/tmp/zenodex-fable-review-c8p12-cargo`, `CARGO_INCREMENTAL=0`,
deleted at the end), ESSO via `/usr/bin/python3` with
`PYTHONPATH=/home/trevormoc/Downloads/ESSO` (z3 4.15.4, cvc5 1.1.2,
`esso_code_hash 7f80c6216be85c827e8d1cc2fa08ee3107a74588`).

Every Lean command (the packet replay, the three Lean gates, the NEW-22 mutation
compile, the derived-coverage experiment, and the builder regeneration) was
started only after `pgrep -x lean` and `pgrep -x lake` were both empty, and my
own Lean commands never overlapped. The shared-lock protocol
(`flock -w 7200 /tmp/zenodex-lean.lock <command>`) was announced by the lead
after my last Lean command had finished; no Lean command was run after the
announcement, so none of this review's Lean evidence was produced outside the
protocol in force at the time.

Commit-shape checks, all passing:

| Check | Result |
| --- | --- |
| `subject_commit` / `subject_parent` / `subject_tree` in packet vs `git rev-parse S31`, `S31^`, `S31^{tree}` | `048a3747e…` / `2e6894f33…` / `1b47bc838…`, all equal |
| P31 is a direct child of S31 | yes (`git rev-parse P31^` = S31) |
| P31 diff is artifact-only | yes: `M docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`, `M …/ZENODEX_O008_FORMAL_CYCLE_V1.md` |
| `packet_write_set` vs actual P31 diff | identical, both `M` |
| `packet_commit_parent` | `048a3747e…` = S31 |
| 48 `source_pins` sha256 recomputed from disk | 0 mismatches |
| 48 `source_pins` `git_blob` recomputed via `git hash-object` | 0 mismatches |
| 84 pins across the five new THV1 packets (12 + 13 + 41 + 7 + 11) | 0 mismatches |
| 589 distinct `killed_by` / `node_ids` across the five packets collect under pytest | all resolve (581 exact ids + 8 parametrised parents with 2–21 children each) |
| Packet-level diff P30 → P31 | only `subject_*`, `packet_commit_parent`, `source_pins` (47 → 48, the new `python_rust_bound_parity_gate` role) and `hygiene_selection` changed |

### Claim ceiling

Canonical-JSON sha256 of `claim_ceiling`:

| Packet | claim_ceiling sha256 |
| --- | --- |
| `e5f8cd423` (C8-p11, P29) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |
| `31e677feb` (C9a', P30) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |
| `a4258d989` (C8-p12, P31) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |

**Byte-identical to P30 (and P29). The ceiling did not move.** Every authority
field remains `NONE`, `formal_core_complete` false, `value_movement_gates_closed`
0 of 12, `o008_status` `OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.

---

## 2. Replays executed

All commands were run from the review worktree at P31 unless stated. Output
hashes are sha256 of the captured stdout (JSON) or of the full pytest/cargo log.

| # | Command | Exit | Result / output hash |
| --- | --- | --- | --- |
| 1 | `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit a4258d9891d1cd738f014c87c7eaa8de8cd6576a` | 0 | ok true, packet_admitted true, current_source_drift [], errors [], proof_replay **NOT_RUN**, runs 0; stdout `9c96032488fd6728b30ebe1d040dc5af2a42d9988c6fb14ef83371e16f3a71ce` |
| 2 | same `--replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO` | 0 | ok true, packet_admitted true, drift [], proof_replay **EXECUTED_PASS**, 29 runs, every exit 0, 11:56:09 → 12:05:29; stdout `37f7822926ea89ca1a7ea887b35b4e2e015c1266a64bc65dbb189c2c72116d00` |
| 3 | `"$PY" tools/build_o008_formal_cycle_v1.py --root "$PWD" --subject-commit 048a3747ecd4a88c9672bd07d856a7fedac41c1a --created-date 2026-09-02 --check --replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO --output-json docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json --output-md docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md` | 0 | `{"drift":[],"mode":"check","ok":true,"subject_commit":"048a3747e…"}`; 12:17:21 → 12:20:58; `git status --short` empty afterwards; regenerated JSON sha256 `698430a234e1bcfec913bd3036d26631b67b27445b22808b9b89ca7e52cd7fe0` = the committed packet |
| 4 | `cargo fmt --all -- --check` (zk/global_settlement_abi_v1) | 0 | empty output (`e3b0c442…`) |
| 5 | `cargo clippy --locked --all-targets -- -D warnings` | 0 | log `c82e6f19b0333b7748b8689d5671410ed1ed427427d4b354e276c2afe34f27fb` |
| 6 | `cargo test --locked` | 0 | 54 `test result: ok` blocks, 0 failed; log `74e78dacd4759be7335d462bac8385dd7b1501f826184db3b7af987fc342d296` |
| 7 | `tests/formal/test_lean_asset_transfer_refinement_v1.py` | 0 | **40 passed** (expected 40); log `21584e5a23a013a0fe84ad6210080455c62ddb8ce80dc03decd4f306ff119d48` |
| 8 | `tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 0 | 6 passed; log `3cc9e4707c2a6ba579cb9a23850a34ee0dc110ca2f5395d15e2c9943d0ebf6de` |
| 9 | `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | 0 | 6 passed; log `7761273fc9d8f6c8614a8f89485e103c6cb9d7ade83d4761acd03e3f68086377` |
| 10 | `tests/core/test_transition_resource_bound_totality_v1.py` | 0 | 9 passed; log `940f1d45832bb3c65182161f3a54ac141438ba079082f2a4ec0a00714d8ff5ec` |
| 11 | `tests/core/test_global_settlement_abi_v1_resource_bounds.py` | 0 | 17 passed; log `bf388be2372ba96f6a3478fa3c69375c616144510d19583c67839b60cf7f1aca` |
| 12 | `tests/core/test_global_settlement_abi_v1.py` | 0 | 75 passed; log `a1554eb769055754c205da3ecd45afe81899cacc13bb036abd8c334e1fa3ed1d` |
| 13 | `tests/test_check_o008_formal_cycle_v1.py` | 0 | **389 passed** (expected 389); log `dcc1a6855c5480d2999771edef62c978eff2841c33b51931edc2aa9c95984ead` |
| 14 | `tests/test_check_global_settlement_canonical_manifest_v1.py` | 0 | 8 passed; log `f40bddd4206cade5fbdc176c746d136c7fad050ead623cfff76a1d8c44ed488e` |
| 15 | `"$PY" tools/check_test_hygiene_v1.py --json` | 0 | ok true, 158 packets; stdout `e5403ebd16bf138328e6d70278511180dece515f8938da20cb9407d91bb0fdb6` |
| 16 | `"$PY" tools/check_test_hygiene_v1.py --base-ref 2e6894f33 --json` (parent of S31) | 0 | ok true, 14 changed paths, 6 critical, all covered; stdout `8539b9b3b703ddc8c91492fb443196841c3a6057b4f7d8c841fd2f2818def5ca` |
| 17 | `"$PY" tools/check_test_hygiene_v1.py --base-ref 42ccb6624 --json` (series base) | **1** | `error: THV1-20260902-global-settlement-v1-canonical-exact-admission-v2: source sha256 drift for tools/check_global_settlement_canonical_manifest_v1.py` — **see NEW-26** |
| 18 | same at P30 in a temporary worktree `/tmp/zenodex-fable-review-c8p12-p30` (removed afterwards) | 1 | `error: test sha256 drift for changed path tests/core/test_global_settlement_abi_v1_resource_bounds.py` (the Opus NEW-25 red, as expected) |
| 19 | `tools/check_test_hygiene_v1.py --changed-file M:src/core/global_settlement_types_v1.py --json` at P31 / at P30 | **1** / 0 | P31: the same `canonical-exact-admission-v2` source drift; P30: green. The staleness is introduced by S31. |

`tests/core/test_zusd_liquidation_partition.py` was excluded as instructed. The
replay's 29 commands ran in the recorded order with `transfer_refinement_gate` at
index 14 and the new author-record comparables (Lean 4.27.0, Python 3.12.3,
cargo/rustc 1.87.0, ESSO fingerprint `256b0dcb…`, verdict VERIFIED) matched.

---

## 3. Verdicts on the P29 findings

### NEW-25 (P1) — **CLOSED as an instance, NOT closed as a class**

The instance is closed: `THV1-20260901-global-settlement-v1-resource-bounds-v8`
pins the current bytes of `tests/core/test_global_settlement_abi_v1_resource_bounds.py`
(`16fbd5b07bbd…`, verified), the path is the 48th packet pin under the new
`python_rust_bound_parity_gate` role (`tools/o008_formal_cycle_admission_v1.py:126`,
`:176`, `:230`), `THV1-20260901-o008-formal-cycle-admission-v27` pins it, and the
repository gate against S31's parent is green (row 16).

The packet replay now sees this class for that path: after `sed -i '204s/rglob/glob/'`
on the parity test, `check_o008_formal_cycle_v1.py` (no replay) exits 1 with
`current_source_drift ["tests/core/test_global_settlement_abi_v1_resource_bounds.py"]`
(restored; tree clean).

But the class is not closed, and the candidate reproduces it one level out: see
**NEW-26 (P1)**. The "process change" (run the hygiene gate against the parent of
every source commit) is not in the subject, cannot be verified from it, and is
structurally blind to the new instance because a parent diff only selects packets
that claim paths changed in that one commit.

### NEW-23 (P2) — **CLOSED**

`tests/core/test_global_settlement_abi_v1_resource_bounds.py:204-205` now binds
`rust_files = sorted(crate_src.rglob("*.rs"))` and reads the scan from it; `:231`
asserts on `rust_files`. Reverting the scan:

```
$ sed -i '204s/rglob/glob/' tests/core/test_global_settlement_abi_v1_resource_bounds.py
$ "$PY" -m pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py::test_every_canonical_rust_bound_has_a_python_twin
1 failed   (assert len(rust_files) > len(list(crate_src.glob("*.rs"))))
```

Restored. The new resource-bounds-v8 mutation row "revert the Rust bound scan
from rglob to glob" is therefore a real killer.

### NEW-22 (P3) — **CLOSED, with a P3 residual**

`lean-mathlib/Proofs/AssetTransferRefinementV1.lean:948-956` proves exactly the
statement Opus proposed:

```lean
theorem rejectCode_ne_postStateResourceBoundExceeded
    (ctx : Context) (pre : TransferState) (cmd : Command) :
    rejectCode ctx pre cmd ≠ some .postStateResourceBoundExceeded
```

and the proof is sound: `rejectCode_eq_some_iff` (`:507`) yields
`¬ guardPasses … postStateResourceBoundExceeded`, which is `¬ True`, discharged
by `trivial`. Is it the right statement? Yes: it quantifies over every context,
pre-state, and command of the bounded model and says the twelfth code is outside
the image of `rejectCode`, which is precisely the licence the exemption needs.

The declared killer works. I gave the guard real content
(`:340` → `pre.policy.enabled = true`, `:356` → the matching `Decidable`
instance) and compiled the core file with `-DwarningAsError=true`: exit 1 with
exactly one error, at `:956:56` (the `trivial` argument of the new theorem).
Restored, tree clean.

Residual, filed as **NEW-28 (P3)**: the licence theorem sits outside the gate's
explicit claim surface, so it gets no `#print axioms` evidence, and the coverage
theorem still restates the exemption by constructor name instead of deriving it.

### NEW-24 (P3) — **CLOSED at the outer level, NOT closed one level down**

`src/core/asset_transfer_module_v1.py:313-315` re-snapshots all three inputs with
`dataclasses.replace(...)`, which re-runs each outer `__post_init__`. I re-ran the
five Opus probes plus scalar/tuple-subclass probes against the transition:

| Probe | Forged input (`object.__new__`, same exact type) | P29 outcome | P31 outcome |
| --- | --- | --- | --- |
| F1 | duplicate `(sender, USD)` rows | refused | refused (`must be canonically ordered and unique`) |
| F2 | a zero-amount row | refused | refused (`must omit zero balances`) |
| F3 | `("aaa","USD","custody",100)` + valid rows | **accepted, relabelled** | refused (`wrong custody domain`) |
| F4 | rows in non-canonical order | **accepted, canonicalised** | refused (`must be canonically ordered and unique`) |
| F5 | policies/supplies asset mismatch | refused | refused (`must cover the same assets`) |
| S1 | `module_release_id` a `str` subclass | — | refused (TypeError, `_require_root` exact-type) |
| S2 | `balances` a `tuple` subclass | — | refused (TypeError, `_require_tuple` exact-type) |
| S3 | context `subject_id` a `str` subclass | — | refused (TypeError) |
| S4/S5 | command `amount_atoms` an `int` subclass / a `bool` | — | refused (ValueError, `_require_atoms_u128` exact-type) |

So for scalar and tuple subclasses at the outer level `replace()` is equivalent to
the managed sibling's checks, because the `_require_*` helpers in
`src/core/global_settlement_types_v1.py:56-118` and `_require_ordered_objects`
(`:1357-1375`) are all `type(x) is …` exact. The declared killer works: deleting
`:313-315` makes `test_transfer_re_validates_same_type_forged_pre_state` fail
(restored). The direct-call BALANCE_OVERFLOW witness also works as a fold-totality
witness: deleting the arm at `:83-84` makes
`test_transfer_balance_overflow_is_a_defensive_arm_behind_input_re_validation`
fail because the rebuilt row raises in the `EconomicAmountV1` constructor
(restored).

What is not closed is the nested level, and the in-code claims about it are
false. Filed as **NEW-27 (P2)**.

---

## 4. THV1 packets, pins, and mutation killers

| Packet | Pins | Result | Rows | New rows vs predecessor |
| --- | --- | --- | --- | --- |
| `THV1-20260901-claimant-backing-guard-golden-v21.json` | 12 | all match | 13 | none (re-pins `tools/check_global_settlement_canonical_manifest_v1.py`) |
| `THV1-20260901-global-settlement-v1-resource-bounds-v8.json` | 13 | all match | 11 | +1 glob-revert (verified above) |
| `THV1-20260901-o008-formal-cycle-admission-v27.json` | 41 | all match | 103 | none (adds the parity-test pin, re-pins the admission module) |
| `THV1-20260902-o008-transfer-refinement-v2.json` | 7 | all match | 5 | +1 NEW-22 guard-content (verified above) |
| `THV1-20260902-o008-transition-resource-bound-totality-v5.json` | 11 | all match | 4 | +2 (delete arm; drop re-validation), −1 (old reach-the-arm row) — both verified above |

Every new mutation row was applied, its named test run, and the file restored
with `git status --short` empty afterwards. The closure digest re-pin
(`tools/check_global_settlement_canonical_manifest_v1.py:41`,
`22d1cfdc402b7b0cdd7b47bc3d9ccbc1fddc72ec1f4241a4f3457f6970d501f7`) is exercised
green by `tests/test_check_global_settlement_canonical_manifest_v1.py` (8 passed).

---

## 5. Findings

### NEW-26 (P1) — S31 leaves a shipped hygiene packet stale, the repository gate is red against the series base, and the P31 packet binds that stale packet as its own hygiene evidence

S31 re-pins the closure digest in `tools/check_global_settlement_canonical_manifest_v1.py:41`
(bytes `530314680012135a…` at P30 → `05390f0a2c2fdf17…` at S31). That file is a
source pin of `tests/evidence/test_hygiene/THV1-20260902-global-settlement-v1-canonical-exact-admission-v2.json`
(shipped in S30 `fe5a6de6f`, pinning `530314680012135a…`). S31 shipped
`claimant-backing-guard-golden-v21` for the new bytes but no
`canonical-exact-admission-v3`, so that packet is now stale under the repository
contract, whose selection at `tools/check_test_hygiene_v1.py:129-136` validates
**every** pin of a selected packet and raises on the first stale one.

Three consequences, each reproduced:

1. The repository gate against the series base is red at P31 (row 17), and it
   was red at P30 only for the NEW-25 path (row 18). The lead's acceptance
   condition for this candidate ("must be green now") fails. The gate against the
   parent (row 16) is green only because the path that selects the stale packet,
   `tests/core/test_global_settlement_canonical_admission_v1.py`, changed in S30
   and not in S31: a parent diff never selects that packet.
2. Marking the types module changed makes the gate red at P31 and green at P30
   (row 19), so the staleness is introduced by S31, not inherited.
3. The P31 packet's own `hygiene_selection` binds this stale packet for
   `src/core/global_settlement_types_v1.py` (row 9 of 45 in
   `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`). Of the four distinct packets
   the selection binds, three are current under all-pins semantics and
   `canonical-exact-admission-v2` is not. The packet-side selector
   (`tools/o008_formal_cycle_admission_v1.py:3194-3211`) compares only the one pin
   for the required path, and its docstring claims "for every changed path both
   select the same packet" as the repository gate. That claim is false in exactly
   this case: the repository gate would refuse the packet outright.

This is the NEW-25 shape again: a change lands, a machine-checked gate goes red,
and neither the candidate nor its packet replay notices, because the pinned
surface covers the changed path but not the other pins of the packets that
vouch for it. The author's process repair (gate against the parent) cannot see
it by construction.

**Reproduction** (clean worktree at P31):

```
$ "$PY" tools/check_test_hygiene_v1.py --base-ref 42ccb6624 --json ; echo $?
error: THV1-20260902-global-settlement-v1-canonical-exact-admission-v2: source sha256 drift for tools/check_global_settlement_canonical_manifest_v1.py
1
$ "$PY" tools/check_test_hygiene_v1.py --changed-file M:src/core/global_settlement_types_v1.py --json ; echo $?
error: THV1-20260902-global-settlement-v1-canonical-exact-admission-v2: source sha256 drift for tools/check_global_settlement_canonical_manifest_v1.py
1
$ git show 31e677feb:tools/check_global_settlement_canonical_manifest_v1.py | sha256sum   # 530314680012135a…  = the v2 pin
$ sha256sum tools/check_global_settlement_canonical_manifest_v1.py                       # 05390f0a2c2fdf17…
```

**Author acknowledgement (received after this finding was filed).** The lead
relayed an author's note that describes the same mechanism (the S30 packet is
selected only for a path changed at S30, so the S31 post-commit gate against
S31^ cannot see it) and announces a repair in the next candidate: `cea-v3` plus a
chain gate against the campaign base. That matches my analysis and does not
change the grade: the candidate under review is P31 as frozen. Two points for the
repair. First, `cea-v3` and a series-base gate close consequences 1 and 2 above
but not consequence 3: as long as `_select_hygiene_packets` binds a packet by a
single pin, the O-008 packet can still admit a hygiene packet the repository
contract rejects, and the docstring's equivalence claim stays false. Second, the
campaign-root base `21fa295a4` is already red on a pre-existing uncovered
workflow path (O-2), so the chain gate should use the series base `42ccb6624`
or first cover that path; otherwise the new gate is red on arrival and proves
nothing about the next candidate.

**Repair (minimal):** ship
`THV1-20260902-global-settlement-v1-canonical-exact-admission-v3.json` pinning the
tool at `05390f0a2c2fdf173ce0e83e7647d342e7bd26ba33b47a6aece3a5c7957605c2`; make
`_select_hygiene_packets` treat a candidate packet as stale when **any** of its
pins disagrees with the subject tree (read the non-required paths from the
subject commit, mirroring `_validate_current_packet`), so the packet replay sees
this class; and replace the parent-only process gate with the series-base run
(`--base-ref 42ccb6624`, or the chain root) before every packet build. Then
rebuild P. Note the documented base (`--base-ref origin/main`,
`docs/testing/TEST_HYGIENE_CONTRACT_V1.md:127`) has no merge base with this
branch, so the series base is the only meaningful whole-chain run.

### NEW-27 (P2) — `replace()` re-validation is shallow: nested policy and supply forgeries are accepted, the fold is still reachable from a forged state, and the code claims otherwise

`dataclasses.replace(pre_state)` re-runs `AssetTransferStateV1.__post_init__`
only. Nested rows are passed through by reference; their own `__post_init__` is
never re-run. The outer check at `src/core/asset_transfer_types_v1.py:78-113`
reads row attributes but never reconstructs rows, and the accept path carries
`pre_state.policies` and `pre_state.supplies` into the post-state unchanged
(`src/core/asset_transfer_module_v1.py:249-254`). Balances are safe only because
`_post_balances` rebuilds every balance row (`:93-96`).

Probes (same-type `object.__new__` forgeries of the nested rows, valid template
otherwise, valid transfer of 10 USD sender → rich):

| Probe | Forged nested row | Outcome |
| --- | --- | --- |
| N1 | policy `fee_owner=123` (int), fee 0 | **ACCEPTED**; post-state carries `AssetTransferPolicyV1(asset='USD', fee_owner=123, …)`, journal emitted with a state root over it |
| N2 | policy `enabled=1` (int) | **ACCEPTED**; post-state carries `enabled=1` |
| N2b | policy `transfer_fee_atoms=-5` | raised (`fee conservation fee_charged_atoms must be a non-negative integer`) — caught late, by the effect row |
| N3 | EUR supply `2**200` (beyond u128), command in USD | **ACCEPTED**; post-state carries the out-of-ABI supply row |
| N3b | EUR supply `True` | **ACCEPTED** |
| N7 | rich row `MAX_ATOMS_V1 - 5` + USD supply `2**130` | `AssetTransferRejectedV1(BALANCE_OVERFLOW)` — the fold ran and the arm fired from a forged state |
| N8/N9 | balance row with a `str`-subclass owner / negative amount | raised at post-state rebuild (safe) |

N1–N3b are silent acceptances of the exact class NEW-24 was about, one level
down. N7 falsifies the test docstring at
`tests/core/test_transition_resource_bound_totality_v1.py:248-251` ("a state
forged past `__post_init__` (object.__new__) is refused by the transition's
entry re-validation before any fold runs") and the packet claim in
`THV1-20260902-o008-transition-resource-bound-totality-v5.json` ("forged states
raise"). The comment at `src/core/asset_transfer_module_v1.py:308-312`
("Re-run every construction invariant through the dataclass constructors,
mirroring the managed sibling") and the commit message are inaccurate: the
managed sibling reconstructs every nested policy, balance, and supply row
(`src/core/managed_asset_lifecycle_module_v1.py:306-379`), and the repository
already owns the deep idiom for this very type in the lane wrapper,
`_snapshot_asset_transfer_state_v1` (`src/core/asset_transfer_lane_module_v1.py:114-139`,
built on `_snapshot_dataclass_tuple_v1` in
`src/core/global_economic_refinement_snapshot_v1.py:74-83`, which `replace()`s
each element). Verified: the lane entry
`transition_asset_transfer_lane_module_v1` refuses N1 with
`TypeError: asset transfer policy fee owner must be a string`, whether N1 is
wrapped in a constructed or a forged `AssetTransferLaneModuleInputV1`.

Bounded honestly, as in P29: reachable only with in-process arbitrary object
construction; the only `AssetTransferStateV1` constructor site under `src/` is
the post-state at `asset_transfer_module_v1.py:249`, there is no
constructor-bypassing deserializer, and the lane wrapper's own snapshot stops
the nested class before it reaches the core. The exposure is defense-in-depth at
the core transition. The severity is P2 rather than P3 because the candidate
asserts a closure it does not have, in the code comment, the test docstring, the
packet claim scope, and the commit message — the same elevation Opus applied to
NEW-23.

**Reproduction** (clean worktree at P31, `PYTHONPATH=.`):

```python
from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import *
from src.core.global_settlement_types_v1 import AssetSupplyV1, EconomicAmountV1
def forge(t, template=None, **ov):
    f = object.__new__(t)
    for fld in t.__dataclass_fields__:
        object.__setattr__(f, fld, ov[fld] if fld in ov else getattr(template, fld))
    return f
root = "0x" + "11" * 32
template = AssetTransferStateV1(root, (AssetTransferPolicyV1("USD", "sender", 0, True),),
    (EconomicAmountV1("rich", "USD", "accounts", 90), EconomicAmountV1("sender", "USD", "accounts", 10)),
    (AssetSupplyV1("USD", 100),))
ctx = AssetTransferContextV1("zenodex", root, root, 1, root, root, "sender", root)
cmd = AssetTransferCommandV1(ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "sender", "rich", 10, 0)
policy = forge(AssetTransferPolicyV1, None, asset="USD", fee_owner=123, transfer_fee_atoms=0, enabled=True)
r = transition_asset_transfer_v1(ctx, forge(AssetTransferStateV1, template, policies=(policy,)), cmd)
print(type(r).__name__, r.post_state.policies)   # AssetTransferAcceptedV1 (… fee_owner=123 …)
```

**Repair (minimal):** replace the three shallow calls at `:313-315` with the deep
snapshot the repository already owns — move `_snapshot_asset_transfer_state_v1`
(and the `_require_exact_dataclass_scalars_v1` checks for context and command)
from the lane module into the core module or into
`global_economic_refinement_snapshot_v1.py` to avoid a lane → core import cycle;
add N1 and N3 as refusal cases next to F3/F4 in
`test_transfer_re_validates_same_type_forged_pre_state`; reword the comment, the
test docstring, the totality-v5 claim scope, and the commit message to say what
is actually refused; re-pin every THV1 packet that pins the module and the test
(totality → v6, transfer-refinement → v3, resource-bounds → v9) and rebuild P.
Optionally, as Opus's narrowest variant, also stop hardcoding the custody domain
at `:94`.

### NEW-28 (P3) — the licence theorem is outside the declared claim surface, and the coverage exemption is restated rather than derived

`tests/formal/test_lean_asset_transfer_refinement_v1.py:74-110` is the
hand-maintained `CORE_CLAIMS` surface: "Every name is a `theorem` in the named
module and is passed to `#print axioms`; nothing else is claimed to be checked."
`rejectCode_ne_postStateResourceBoundExceeded` is not in it (nor in the corpus
or the tool: `grep -c rejectCode_ne tests/data/asset_transfer_refinement_v1.json`
= 0). So the theorem the challenge docstring now cites as its machine-checked
licence has no axiom evidence and is not on the claim surface the packet calls
exact (handoff duty 2). The gate stays green because
`test_claim_surface_is_explicit_and_clean` (`:460-475`) only checks that listed
claims exist.

Separately, `AssetTransferRefinementV1Challenge.lean:219-224` still exempts the
twelfth code by name (`c ≠ .postStateResourceBoundExceeded →`). The exemption
should be derived: coverage over the emittable image needs no hand-written
exemption and cannot silently keep exempting a code that a future edit makes
reachable. This form compiles in my worktree against the P31 oleans with
`-DwarningAsError=true` (exit 0; scratch file removed; sha256
`2f3c2615869b4278fb31949320c90336c43cfb6b3cfee931ae47705e88c007ed`):

```lean
theorem report_vectors_cover_every_emittable_code :
    ∀ c : RejectCode, (∃ ctx pre cmd, rejectCode ctx pre cmd = some c) → c.code ∈ vectorLabels := by
  intro c ⟨ctx, pre, cmd, h⟩
  rw [vectorLabels_eq]
  cases c <;> first
    | exact absurd h (rejectCode_ne_postStateResourceBoundExceeded ctx pre cmd)
    | decide
```

**Repair (minimal):** add `"rejectCode_ne_postStateResourceBoundExceeded"` to
`CORE_CLAIMS` (the axioms test and the claim-surface test then cover it), and
either replace `report_vectors_cover_every_code` with the emittable-image form
above (updating `CHALLENGE_CLAIMS` at `:121-133`) or keep both with the old one
derived from the new one. Re-pin transfer-refinement (→ v3) and rebuild P.

### Observations (not graded)

- **O-1, direct-call witness width.** The fold witness at
  `tests/core/test_transition_resource_bound_totality_v1.py:270` passes
  `deltas={"rich": MAX_ATOMS_V1}`, a delta above `MAX_DELTA_ATOMS_V1` that
  `_transfer_deltas` can never hand the fold (the i128 width guard fires first).
  The docstring discloses "an oversized delta", so this is honest, but an
  in-width witness exists and would be sharper: rich = 2^127 + 1 with supply
  2^127 + 11 and `deltas={"rich": MAX_DELTA_ATOMS_V1}` returns `BALANCE_OVERFLOW`
  (verified). Through the transition with valid inputs the arm remains
  unreachable (balances ≤ supply ≤ MAX_ATOMS_V1), so the arm is genuinely
  defensive.
- **O-2, whole-chain gate context.** `--base-ref 21fa295a4` (the campaign root) is
  red at P31 on `uncovered critical path: M:.github/workflows/release-integrity.yml`,
  a pre-existing gap unrelated to this candidate; `--base-ref origin/main` and
  `--base-ref main` cannot run at all (no merge base). The series base
  `42ccb6624` is therefore the only whole-chain run that isolates this
  candidate, and it is red for the S31-introduced reason in NEW-26.
- **O-3, process claim.** "The chain runs the repository hygiene gate against the
  parent of every source commit before a packet is built" is not in the subject
  and cannot be verified from it; NEW-26 shows it is insufficient even if
  followed.

---

## 6. Builder regeneration

```
$ "$PY" tools/build_o008_formal_cycle_v1.py --root "$PWD" \
    --subject-commit 048a3747ecd4a88c9672bd07d856a7fedac41c1a \
    --created-date 2026-09-02 --check --replay \
    --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO \
    --output-json docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json \
    --output-md docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
exit 0
{"drift":[],"mode":"check","ok":true,"subject_commit":"048a3747ecd4a88c9672bd07d856a7fedac41c1a"}
```

`git status --short` immediately after the regeneration was **empty**, and the
regenerated JSON hashes to `698430a234e1bcfec913bd3036d26631b67b27445b22808b9b89ca7e52cd7fe0`,
the committed packet. The artifact is reproducible from S31 alone, including the
29-command replay record and the author record. The regeneration ran 12:17:21 →
12:20:58 with warm oleans and cargo artifacts, after waiting for an idle Lean.

Note that the builder's `--check` compares the regenerated packet against the
committed one and its replay re-executes the pinned gates; neither runs the
repository hygiene contract, which is why NEW-26 is invisible to both (the
packet's nonclaim at `tools/o008_formal_cycle_admission_v1.py:510-511` says so
explicitly).

---

## 7. Authority statement

This review grants no authority. Authority remains NONE across production,
release, settlement, verifier, migration, publication, and value movement. The
claim ceiling is byte-identical to the P29 and P30 packets and must stay there.
ACCEPT would be advisory in any case; this review returns REVISE. A finding
causes a new child candidate and invalidates this hash review.

Cleanup: the temporary P30 worktree `/tmp/zenodex-fable-review-c8p12-p30` and the
cargo target dir `/tmp/zenodex-fable-review-c8p12-cargo` were removed; captured
logs remain under `/tmp/zenodex-formal-core-fable-review-c8p12-out/`.
