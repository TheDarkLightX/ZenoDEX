# Opus review P31 / C8-p12 — ZenoDEX Formal Functional Core Closure Campaign

| Field | Value |
| --- | --- |
| Subject (S31) | `048a3747ecd4a88c9672bd07d856a7fedac41c1a` "security: repair the Opus P29 review findings" |
| Subject parent | `2e6894f33a1ce6465d2eb8efa35ddee6be106ea5` (R26, committed Opus C8-p11 receipt) |
| Subject tree | `1b47bc838f34dfccd36af30ad3bae9a7dc20466f` |
| Artifact (P31) | `a4258d9891d1cd738f014c87c7eaa8de8cd6576a` "docs: freeze the O-008 formal-cycle packet at C8-p12" |
| Packet sha256 | `698430a234e1bcfec913bd3036d26631b67b27445b22808b9b89ca7e52cd7fe0` |
| Branch | `codex/formal-core-fable-20260901` |
| Review worktree | `/tmp/zenodex-formal-core-opus-c8p12` (detached; `git status --short` empty at start and after every probe) |
| Reviewer | Opus 5 (independent proof / refinement / authority reviewer) |
| Date | 2026-09-02 |
| Authority granted | **NONE** (advisory review; claim ceiling unmoved) |

**Verdict: REVISE — grade B-.** 1 P1, 2 P2, 2 P3.

Three of the four P29 findings are materially repaired, and two of the repairs
are the strongest work in this candidate: NEW-23 is closed exactly as
prescribed and I re-ran the probe that previously survived, and the NEW-22 Lean
theorem is a genuine derivation whose declared mutation I confirmed kills. But
the headline P1 recurs one file over. The candidate closed the specific stale
hygiene pin that made the repository gate red at P29 and then made the same gate
red again, at the same base ref, by re-pinning a constant in a tool that an
older evidence packet still claims. The process change the candidate advertises
— run the repository hygiene gate against the parent of every source commit — is
precisely the process that cannot see this, because a per-commit base only
re-validates packets selected by *that* commit's changed paths.

I also found, and demonstrated end to end, that the gate the candidate newly
pinned into the O-008 packet is never executed by the packet replay: it can go
red while `check_o008_formal_cycle_v1.py --replay` reports `EXECUTED_PASS` with
`current_source_drift []`.

---

## 1. Environment and provenance

Worktree HEAD equals P31; `git status --short` was empty before any probe and
empty again after every probe was restored. `external/ESSO` and the eight
`lean-mathlib/.lake/packages` symlinks were in place.

Toolchain: Python `/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`,
`PYTHONDONTWRITEBYTECODE=1`, `CARGO_TARGET_DIR=/tmp/zenodex-opus-c8p12-cargo`,
`CARGO_INCREMENTAL=0`, ESSO via `/usr/bin/python3` with
`PYTHONPATH=/home/trevormoc/Downloads/ESSO`. Fresh replay observed Lean 4.27.0,
z3 4.15.4, cvc5 1.1.2.

Commit-shape checks, all passing:

| Check | Result |
| --- | --- |
| `subject_parent` in packet vs `git rev-parse S31^` | `2e6894f33…` = `2e6894f33…` |
| `subject_tree` in packet vs `git rev-parse S31^{tree}` | `1b47bc838…` = `1b47bc838…` |
| P31 is a direct child of S31 | yes (`git rev-parse HEAD^` = S31) |
| P31 diff is artifact-only | yes, exactly `ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` |
| `packet_write_set` vs actual P31 diff | identical, both `M` |
| 48 `source_pins` sha256 recomputed from disk | 0 mismatches |
| 48 `source_pins` `git_blob` recomputed via `git hash-object` | 0 mismatches |
| `executing_tools` hashes vs pinned tool hashes | 4 of 4 identical |

The 48th pin is the new one:
`tests/core/test_global_settlement_abi_v1_resource_bounds.py`, role
`python_rust_bound_parity_gate`.

### Claim ceiling

Canonical-JSON sha256 of `claim_ceiling`, computed over five packets:

| Packet | claim_ceiling sha256 |
| --- | --- |
| `1dd572ba1` (C8-p10) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |
| `8d86d6248` (C9a, P28) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |
| `e5f8cd423` (C8-p11, P29) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |
| `31e677feb` (C9a', P30) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |
| `a4258d989` (C8-p12, P31) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |

**Byte-identical to P30 and every prior packet. The ceiling did not move.**
Every authority field remains `NONE`, `formal_core_complete` false,
`value_movement_gates_closed` 0 of 12, `o008_status`
`OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.

---

## 2. Replays executed

```
$ "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" \
    --packet-commit a4258d9891d1cd738f014c87c7eaa8de8cd6576a
exit 0 — ok true, packet_admitted true, current_source_drift [], errors [],
         proof_replay.status NOT_RUN, runs 0
```

```
$ "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" \
    --packet-commit a4258d9891d1cd738f014c87c7eaa8de8cd6576a --replay \
    --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO
exit 0 — ok true, packet_admitted true, current_source_drift [], errors [],
         proof_replay.status EXECUTED_PASS, runs 29, every command exit 0
```

Direct gate runs:

| Command | Result |
| --- | --- |
| `cargo fmt --all -- --check` (zk/global_settlement_abi_v1) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0 (12 + 15 + 1 passed) |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` | 40 passed (expected 40) |
| `tests/core/test_transition_resource_bound_totality_v1.py` | 9 passed (was 8) |
| `tests/core/test_global_settlement_abi_v1_resource_bounds.py` | 17 passed |
| `tests/core/test_global_settlement_abi_v1.py` | 75 passed |
| `tests/test_check_o008_formal_cycle_v1.py` | 389 passed (expected 389) |
| `tests/test_check_global_settlement_canonical_manifest_v1.py` | 8 passed |
| `tools/check_test_hygiene_v1.py --json` | exit 0, ok true |
| `tools/check_test_hygiene_v1.py --base-ref 2e6894f33 --json` | exit 0, ok true |
| `tools/check_test_hygiene_v1.py --base-ref 42ccb6624 --json` | **exit 1 — see NEW-26** |
| `tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 6 passed |
| `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | 6 passed |
| `tools/build_o008_formal_cycle_v1.py … --check --replay` | see §6 |

`tests/core/test_zusd_liquidation_partition.py` has a pre-existing unrelated
collection error and was excluded, as instructed.

Every Lean command I issued ran strictly serially, each preceded by a wait on
`pgrep -x lean` and `pgrep -x lake`.

---

## 3. Verdicts on the P29 findings

### NEW-25 (P1) — **PARTIAL**

The pinning half is real and I verified it bites.
`THV1-20260901-global-settlement-v1-resource-bounds-v8.json` pins the repaired
bytes; `tools/o008_formal_cycle_admission_v1.py:126` adds
`PARITY_GATE_PATH_V1`, `:176` registers the role in `SOURCE_PIN_ROLES_V1`, and
`:230` adds it to `THV1_REQUIRED_PIN_PATHS_V1`. The packet carries 48 pins, and
the path appears both in `source_pins` and in the 45-row `hygiene_selection`
table (covered by `…admission-v27`).

*Drift probe, as requested.* Appending one comment line to the parity test in my
worktree:

```
$ printf '\n# opus drift probe\n' >> tests/core/test_global_settlement_abi_v1_resource_bounds.py
$ "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit a4258d989…
exit 1 — ok false,
         current_source_drift ["tests/core/test_global_settlement_abi_v1_resource_bounds.py"]
```

Restored. So the class the P29 finding named — an unpinned change to that file —
is now visible to the packet.

*The repository gate, however, is still red at the base the finding named.*

| Base ref | Result |
| --- | --- |
| static (no base) | exit 0, ok true |
| `2e6894f33` (parent of S31) | exit 0, ok true |
| `42ccb6624` (the C9a receipt, red at P29/P30) | **exit 1** |

The error is different from P29's, and it is a regression introduced by S31.
Filed as **NEW-26 (P1)** below.

### NEW-23 (P2) — **CLOSED**

`tests/core/test_global_settlement_abi_v1_resource_bounds.py:204` now binds the
scan to a named list and `:231` asserts on that list:

```python
rust_files = sorted(crate_src.rglob("*.rs"))
rust_source = "\n".join(rust_file.read_text(encoding="utf-8") for rust_file in rust_files)
...
assert len(rust_files) > len(list(crate_src.glob("*.rs")))
```

Re-running the exact P29 probe:

```
$ sed -i '204s/rglob/glob/' tests/core/test_global_settlement_abi_v1_resource_bounds.py
$ "$PY" -m pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py
E       AssertionError: assert 88 > 88
FAILED …::test_every_canonical_rust_bound_has_a_python_twin
1 failed, 16 passed in 0.72s
```

Restored. The revert now fails, the comment at `:227-230` matches the code, and
the declared mutation row in `…resource-bounds-v8.json` ("revert the Rust bound
scan from rglob to glob") is genuinely killed by the named test.

### NEW-22 (P3) — **CLOSED, with one residual**

**Is it the right statement?** Yes.
`lean-mathlib/Proofs/AssetTransferRefinementV1.lean:952-956` states exactly the
ground the exemption rests on — `rejectCode ctx pre cmd ≠ some
.postStateResourceBoundExceeded` — and the proof is a real derivation, not a
projection. `rejectCode_eq_some_iff` (`:507`) characterises a returned code as
"its guard fails and every lower-rank guard passes"; `.mp h |>.1` is
`¬ guardPasses … postStateResourceBoundExceeded`, and since that guard is
definitionally `True` (`:340`), applying `trivial` closes the goal. It passes
the "return h" test: nothing in the hypothesis restates the conclusion.

**Would giving the guard real content be caught?** Yes, as declared. I replaced
`:340` and its `Decidable` arm at `:356` with `cmd.amountAtoms ≠ 0`:

```
$ "$PY" -m pytest -q "tests/formal/test_lean_asset_transfer_refinement_v1.py::test_lean_target_compiles_without_warnings"
E   Some required targets logged failures:
E   - Proofs.AssetTransferRefinementV1
2 errors in 9.30s
```

Restored. `THV1-20260902-o008-transfer-refinement-v2.json`'s new mutation row is
therefore honest.

**Should the exemption be derived rather than restated?** The residual is
narrower and sharper than that. The challenge docstring
(`AssetTransferRefinementV1Challenge.lean:213-217`) now cites the theorem by
name, which is the right editorial move, but the theorem was **not added to
`CORE_CLAIMS`** in `tests/formal/test_lean_asset_transfer_refinement_v1.py` —
unlike its exact sibling `balanceOverflow_unreachable`, which is in the list.
So it is not `#print axioms`-checked and its existence is not pinned. Filed as
**NEW-29 (P3)**, with a probe showing the licence can be removed silently.

### NEW-24 (P3) — **PARTIAL**

**F1–F5 all closed.** With `context = replace(context)`, `pre_state =
replace(pre_state)`, `command = replace(command)` at
`src/core/asset_transfer_module_v1.py:313-315`, every P29 probe is now refused
before any fold runs:

| Probe | P29 outcome | P31 outcome |
| --- | --- | --- |
| F1 duplicate `(sender, USD)` rows | refused (incidentally, at post-state construction) | `ValueError: … must be canonically ordered and unique` |
| F2 zero-amount row | refused (incidentally) | `ValueError: … must omit zero balances` |
| F3 `("aaa","USD","custody",100)` row | **ACCEPTED**, row relabelled to `accounts` | `ValueError: … wrong custody domain` |
| F4 non-canonical row order | **ACCEPTED**, silently canonicalised | `ValueError: … must be canonically ordered and unique` |
| F5 policies/supplies asset mismatch | refused (incidentally) | `ValueError: … must cover the same assets` |

Top-level subclass forgeries are refused too, which answers two of the three
equivalence questions:

| Probe | Outcome |
| --- | --- |
| `module_release_id` a `str` subclass | `TypeError: … must be a string` (`_require_root` uses `type(...) is not str`) |
| `balances` a `tuple` subclass | `TypeError: … must be a tuple` (`_require_tuple` uses `type(...) is not tuple`) |
| context `writer_epoch` an `int` subclass | `ValueError: … must be a non-negative integer` |
| command `amount_atoms` an `int` subclass | `ValueError: … must be a non-negative integer` |

**The third question — forged sub-objects — is where the answer is no.**
`replace()` re-runs only the top-level `__post_init__`.
`_require_ordered_objects` (`src/core/global_settlement_types_v1.py:1357`)
checks each row's *type* but never reconstructs it, so a row built with
`object.__new__(EconomicAmountV1)` passes through with its own
`__post_init__` never run. Filed as **NEW-28 (P2)**, with an accepted,
value-destroying witness.

**Is the direct-call witness honest?** Yes. The old test reached the
`BALANCE_OVERFLOW` arm through a forged state that the entry re-validation now
refuses, so the witness had to move. The replacement asserts both halves — the
forged state raises, and `_post_balances(template, asset="USD",
deltas={"rich": MAX_ATOMS_V1})` returns the typed reject — and the docstring
says plainly that the arm is "checked-arithmetic totality", not reachability. I
confirmed the mutation row moved correctly: deleting lines 83-84 (the
`post_atoms > MAX_ATOMS_V1` arm) fails
`test_transfer_balance_overflow_is_a_defensive_arm_behind_input_re_validation`.
One honest caveat worth keeping in the docstring: a delta of `MAX_ATOMS_V1` is
not producible by `_prepare_transfer` for that template, so the test proves the
helper is total, not that the code is reachable through the public API.

---

## 4. THV1 packets, pins, and mutation killers

| Packet | Pins | sha256 result | node ids | mutations |
| --- | --- | --- | --- | --- |
| `THV1-20260901-global-settlement-v1-resource-bounds-v8` | 13 | all match | 94 | 11 (+1) |
| `THV1-20260902-o008-transfer-refinement-v2` | 7 | all match | 28 | 5 (+1) |
| `THV1-20260902-o008-transition-resource-bound-totality-v5` | 11 | all match | 10 | 4 (+2, −1) |
| `THV1-20260901-o008-formal-cycle-admission-v27` | 41 | all match | 428 | 103 (+0) |
| `THV1-20260901-claimant-backing-guard-golden-v21` | 12 | all match | 48 | 13 (+0) |

All 589 distinct node ids collect under pytest (631 tests after
parametrisation), `--collect-only` exit 0. All five packets carry
`risk_class: critical`.

**Every mutation added in this round actually kills.** Applied, ran the named
test, restored; `git status --short` empty after each:

| Declared mutation | Named killer | Result |
| --- | --- | --- |
| revert the Rust bound scan from rglob to glob | `…resource_bounds.py::test_every_canonical_rust_bound_has_a_python_twin` | **FAILED** ✓ |
| give the twelfth code's guard real content | `…test_lean_asset_transfer_refinement_v1.py::test_lean_target_compiles_without_warnings` | **ERRORED** ✓ |
| delete the transfer BALANCE_OVERFLOW arm of the balance fold | `…::test_transfer_balance_overflow_is_a_defensive_arm_behind_input_re_validation` | **FAILED** ✓ |
| drop the entry re-validation | `…::test_transfer_re_validates_same_type_forged_pre_state` | **FAILED** ✓ |

The one removed row (`…is_a_defensive_guard_with_a_forgery_witness`) is removed
because the test it named was renamed and rewritten; the replacement row points
at the new name. That bookkeeping is correct.

**Closure digest re-pin.**
`tools/check_global_settlement_canonical_manifest_v1.py:41` moves
`9d761af4…` → `22d1cfdc402b7b0cdd7b47bc3d9ccbc1fddc72ec1f4241a4f3457f6970d501f7`.
The digest is genuinely derived — `_source_closure_sha256` (`:402`) hashes the
relative path and file digest of every file in `defining_paths ∪ call_paths ∪
{manifest, dispatcher}` — and `check_repository` (`:443-447`) recomputes and
compares it. `tests/test_check_global_settlement_canonical_manifest_v1.py`
passes 8/8, including
`test_repository_canonical_manifest_source_closure_passes`. The move is
consistent with the only closure member S31 changed,
`src/core/asset_transfer_module_v1.py`.

---

## 5. Findings

### NEW-26 (P1) — the repository hygiene gate is still red at the base the P29 P1 named, now for a reason this candidate introduced

```
$ "$PY" tools/check_test_hygiene_v1.py --base-ref 42ccb6624 --json ; echo $?
error: THV1-20260902-global-settlement-v1-canonical-exact-admission-v2: source sha256 drift for tools/check_global_settlement_canonical_manifest_v1.py
1
```

S31 changed `tools/check_global_settlement_canonical_manifest_v1.py:41` (the
closure digest re-pin) and shipped
`THV1-20260901-claimant-backing-guard-golden-v21.json` re-pinning those bytes.
But `THV1-20260902-global-settlement-v1-canonical-exact-admission-v2.json`,
created one commit earlier in S30, also pins that tool, at the pre-S31 bytes,
and no `v3` was shipped.

| Artifact | sha256 of `tools/check_global_settlement_canonical_manifest_v1.py` |
| --- | --- |
| at `42ccb6624` | `0fc715c3e1d57bd04b1c401865a981eb8f3d7233d39c58e3de809858b1fb6a79` |
| at `fe5a6de6f` / `2e6894f33` (S30 / P30) | `530314680012135a078cc7285b0c45b84dd64ae7f8e93282d050cbffac329ba5` |
| `…canonical-exact-admission-v2.json` pin | `530314680012135a078cc7285b0c45b84dd64ae7f8e93282d050cbffac329ba5` |
| at P31 | `05390f0a2c2fdf173ce0e83e7647d342e7bd26ba33b47a6aece3a5c7957605c2` |
| `…claimant-backing-guard-golden-v21.json` pin | `05390f0a2c2fdf173ce0e83e7647d342e7bd26ba33b47a6aece3a5c7957605c2` |

The v2 packet's pin matched exactly at P30, so this specific error did not exist
there: it is a regression from S31, not a survivor.

**Mechanism, and why the advertised process change cannot catch it.**
`_select_packet` (`tools/check_test_hygiene_v1.py:107`) picks, for each changed
critical path, the newest packet whose pin for *that path* is current — and then
calls `_validate_current_packet` (`:60`), which validates **every** pin in the
selected packet. Enumerating all 17 critical changed paths under base
`42ccb6624`, exactly one fails:

```
FAIL tests/core/test_global_settlement_canonical_admission_v1.py
     -> THV1-20260902-global-settlement-v1-canonical-exact-admission-v2:
        source sha256 drift for tools/check_global_settlement_canonical_manifest_v1.py
```

That path was changed in S30, not S31. Under base `2e6894f33` (the parent of
S31) it is not in the changed set at all, so the v2 packet is never selected and
the gate is green. Running the gate "against the parent of every source commit"
therefore structurally cannot see a packet that a *previous* commit's path
selects. Only a campaign-level base ref does.

**Repair (minimal):** ship
`THV1-20260902-global-settlement-v1-canonical-exact-admission-v3.json`, a copy
of v2 with the tool's current bytes `05390f0a…` (the evidence directory is
append-only — `_reject_packet_rewrites` at `:181` — so v2 must not be edited).
Reverse-lexicographic selection puts `v3` ahead of `v2`, so it will be chosen.

**Repair (durable, and the point of the finding):** make the chain run
`check_test_hygiene_v1.py` against the campaign base ref — the receipt commit
the candidate is repairing — not only against each source commit's parent. As it
stands, the candidate built to close "a gate goes red and the packet stays
green" reproduced that shape for the third consecutive generation
(NEW-19 → NEW-25 → NEW-26).

### NEW-27 (P2) — the newly pinned parity gate is never executed by the packet replay

`tools/o008_formal_cycle_admission_v1.py` gives
`tests/core/test_global_settlement_abi_v1_resource_bounds.py` the role
`python_rust_bound_parity_gate` (`:176`) and requires a THV1 pin for it
(`:230`), but adds **no entry to `REPLAY_COMMANDS_V1` (`:1274`)**. Compare the
C8-p11 treatment of the transfer gate, which got both a role (`:175`) and a
replay command (`:1413`).

Nine pinned roles end in `_gate`. Eight map to a replay command id; this one is
the only exception:

| Pinned role | Replay command id |
| --- | --- |
| `lean_source_binding_compilation_and_axiom_gate` | `lean_binding_gate` |
| `allocation_certificate_lean_binding_gate` | `lean_certificate_binding_gate` |
| `esso_replay_mutation_and_v1_information_loss_gate` | `esso_gate` |
| `allocation_certificate_esso_replay_gate` | `esso_certificate_gate` |
| `prior_model_semantic_restage_gate` | `prior_restage_gate` |
| `transfer_refinement_replay_gate` | `transfer_refinement_gate` |
| `python_runtime_projection_gate` | `python_projection_gate` |
| `rust_compiled_projection_gate` | `rust_projection_gate` |
| `python_rust_bound_parity_gate` | **none** |

Consequence: the pin binds only the test file's own bytes. Anything else that
reddens the gate is invisible. **Reproduction** (clean worktree at P31):

```
$ printf '\npub const MAX_OPUS_PROBE_ROWS_V1: usize = 7;\n' \
    >> zk/global_settlement_abi_v1/src/economic_command_authentication/witness.rs
$ "$PY" -m pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py
FAILED …::test_every_canonical_rust_bound_has_a_python_twin
1 failed, 16 passed
$ "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit a4258d989… --replay \
    --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO
exit 0 — ok true, packet_admitted true, current_source_drift [],
         proof_replay.status EXECUTED_PASS, runs 29, every command exit 0
```

Restored; tree clean. A Rust bound with no Python twin, declared in a crate file
the packet does not pin, leaves the packet fully green through a real replay.

In fairness the packet's `claim_scope` is worded carefully — "a change to it is
visible to the packet replay" — and a nonclaim already discloses that most crate
`.rs` files are compiled unpinned. The defect is that the role is named a *gate*
and joined the pinned surface without joining the replay, which is exactly the
pattern C8-p11 established for the transfer gate.

**Repair:** add a `python_parity_gate` entry to `REPLAY_COMMANDS_V1` running
`pytest -q -p no:cacheprovider tests/core/test_global_settlement_abi_v1_resource_bounds.py`
with a pinned expected pass count of 17, mirroring
`TRANSFER_REFINEMENT_GATE_EXPECTED_PASSED_V1` (`:125`), and rebuild the packet
so the replay becomes 30 commands. The totality suite
(`tests/core/test_transition_resource_bound_totality_v1.py`), which carries the
NEW-24 killers, is outside the replay for the same reason and is worth the same
treatment.

### NEW-28 (P2) — `replace()` is not the managed sibling's re-validation, the comment says it is, and a forged nested row is accepted with value destroyed

`src/core/asset_transfer_module_v1.py:309-312` says the entry re-validation is
"mirroring the managed sibling". It is not.
`managed_asset_lifecycle_module_v1._snapshot_state` (`:361-374`) reconstructs
**every row** through `_snapshot_policy` / `_snapshot_balance` /
`_snapshot_supply`, each of which re-runs that row's `__post_init__`.
`dataclasses.replace(pre_state)` re-runs only `AssetTransferStateV1.__post_init__`,
which type-checks rows via `_require_ordered_objects` but never reconstructs
them.

**Witness — accepted, with 89 atoms destroyed.** A forged
`EconomicAmountV1` whose `amount_atoms` is `True` (a `bool`, not an `int`) has
`type(row) is EconomicAmountV1` exactly true, so it survives the row type check;
the state's `__post_init__` only compares `custody_domain`, tests
`amount_atoms == 0`, and sums into `totals`, none of which reject it:

```
pre-state balance sum: 11   declared supply: 100
result: AssetTransferAcceptedV1
post balances: [('rich', 'USD', 'accounts', 11)]
post balance sum: 11        supply still: 100
post_state is reconstructible as a valid AssetTransferStateV1: yes
```

Template balances were `rich: 90`, `sender: 10`; the transfer moved 10 from
sender to rich. The accepted post-state is well-formed and constructible, and
89 atoms are simply gone. The same forged row is refused by the managed sibling:

```
managed _snapshot_balance(bool amount):     REFUSED TypeError: managed asset balance amount must be an exact integer
managed _snapshot_balance(negative amount): REFUSED ValueError: economic amount atoms must be a non-negative integer
```

A forged row with `amount_atoms = -1000` is likewise not refused; it is absorbed
into the fold and returns `INSUFFICIENT_BALANCE` (a no-op, so harmless, but the
input was never rejected as malformed). A forged row with a non-ASCII `owner` is
caught only incidentally, at post-state construction inside `_post_balances`
(`:92`) — the same accidental mechanism P29 already flagged.

Reachability is bounded exactly as in P29: this needs in-process arbitrary
object construction, and no constructor-bypassing deserializer for
`EconomicAmountV1` exists on any path under `src/`. It is defence in depth.

**Accuracy note, in the candidate's favour.** The sibling picture is mixed:
`managed_asset_lifecycle_state_v2._snapshot_state_v2` also reconstructs per row,
but `asset_transfer_types_v2._snapshot_asset_transfer_state_v2` is shallow, like
this repair. So the depth chosen matches the transfer family and not the managed
family. The defect is that the comment names the managed sibling as the model
when the code follows the other one.

**Repair, in increasing cost:** correct the comment to say what the
re-validation does and does not cover (one line, honest, and it would have been
caught by a self-review against the sibling); or add
`_snapshot_balance`-equivalent per-row reconstruction so the claim becomes true;
or, narrowest for the value-destruction witness alone, have
`_require_ordered_objects` assert `type(getattr(item, field))` for the scalar
fields it reads.

### NEW-29 (P3) — the new unreachability theorem is outside the pinned claim surface, so the licence can be deleted silently

`rejectCode_ne_postStateResourceBoundExceeded`
(`lean-mathlib/Proofs/AssetTransferRefinementV1.lean:952`) is cited by name in
the coverage exemption's docstring
(`AssetTransferRefinementV1Challenge.lean:216`), but it was not added to
`CORE_CLAIMS` in `tests/formal/test_lean_asset_transfer_refinement_v1.py` —
which S31 did not touch at all. Its exact sibling `balanceOverflow_unreachable`
*is* in that list, so the omission is an inconsistency rather than a policy.

Consequence: the theorem is neither `#print axioms`-checked
(`test_all_named_claims_depend_only_on_standard_lean_axioms`) nor
existence-pinned (`test_claim_surface_is_explicit_and_clean`). **Reproduction:**
delete lines 948-957 *and* give the guard real content at `:340` / `:356` with
`cmd.amountAtoms ≠ 0` — a condition already implied by the lower-rank
`zeroAmount` guard, so the model's behaviour is unchanged and nothing else
breaks:

```
$ "$PY" -m pytest -q tests/formal/test_lean_asset_transfer_refinement_v1.py
40 passed in 26.01s
```

with the challenge docstring still citing a theorem that no longer exists.
Restored; tree clean.

**Repair (minimal):** add `"rejectCode_ne_postStateResourceBoundExceeded"` to
`CORE_CLAIMS`. That alone makes both probes red and costs no change to the
expected pass count of 40. **Stronger, and worth considering:** restate
`report_vectors_cover_every_code` so the exemption is *derived* from
reachability rather than from a constructor name, e.g. quantifying over
`(∃ ctx pre cmd, rejectCode ctx pre cmd = some c) → c.code ∈ vectorLabels`.
Then a guard that gains real content cannot keep an exemption it no longer
deserves, regardless of which theorems survive.

### NEW-30 (P3) — the hygiene selector's "newest packet" is lexicographic, and an in-code claim that it agrees with the builder is false

`tools/o008_formal_cycle_admission_v1.py:3195-3202` documents the builder's rule
and asserts an agreement:

> Packets are ordered by lineage version (the trailing `-vN` compared
> numerically, so `v10` outranks `v9`) … **The repository hygiene gate iterates
> lexicographically and also skips stale packets, so for every changed path both
> select the same packet**; for an unchanged path any matching packet carries the
> same pin.

The last clause is the flaw. `check_test_hygiene_v1._select_packet` does not
merely read the chosen packet's pin for the changed path — it then calls
`_validate_current_packet` (`tools/check_test_hygiene_v1.py:60`) on **every**
pin of that packet. So picking an older equally-matching packet is not harmless.

**Reproduction** (clean worktree at P31, no file modified):

```
$ "$PY" tools/check_test_hygiene_v1.py \
    --changed-file "M:src/core/global_economic_state_effect_refinement_v1.py" --json ; echo $?
error: THV1-20260901-o008-formal-cycle-admission-v9: source sha256 drift for tools/check_o008_formal_cycle_v1.py
1
```

51 packets pin the current bytes of that path. The builder picks `…-v27`
(numeric); the gate reaches `…-v9` first (reversed-lexicographic, `"v9" > "v27"`)
and then fails on v9's unrelated stale pins. The two tools select different
packets for the same path, which is exactly what the docstring says cannot
happen. The same disagreement holds for 16 of the packet's 45
`hygiene_selection` rows.

Bounded honestly: this fires only when a path is *reported* changed while its
current bytes still equal an older packet's pin — a revert, a byte-identical
round trip, or an explicit `--changed-file` as above. Under `--base-ref` with a
genuinely edited file, no old packet matches and both tools agree.

It matters here because it is the same root cause as NEW-26: whole-packet
validation on selection turns every historical packet into a landmine once any
file it pins moves elsewhere. NEW-26 is that mechanism firing today; this is the
mechanism plus a wrong ordering that can aim it at an older packet.

**Repair:** order by `hygiene_lineage_key_v1` in `_select_packet` too, so the
gate and the builder share one notion of "newest"; and either restrict
`_validate_current_packet` to the pins relevant to the selected path or accept
that shipping a new lineage version is mandatory for *every* packet that pins a
changed file, not only the newest one.

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
regenerated packet hashes to `698430a234e1bcfec913bd3036d26631b67b27445b22808b9b89ca7e52cd7fe0`,
the committed value. The builder rewrote both packet files from the subject
commit and produced bytes identical to the committed P31 artifact, including
the 29-command replay record and the author record. The artifact is
reproducible from S31 alone, and the committed packet is exactly the projection
the builder computes.

---

## 7. What I did not re-grade

The C9a findings repaired in S30/P30 were out of scope here and I did not
re-grade them; NEW-26 touches the P30 evidence packet only as the holder of a
now-stale pin, not as a semantic finding against that work. I sampled rather
than exhaustively re-applied the 136 inherited mutation rows across the five
packets: I verified all four rows added in this round and confirmed all 589
declared node ids collect. NEW-30 is pre-existing shared infrastructure, not
introduced by this candidate; I report it because it compounds NEW-26 and
because the in-code claim it falsifies sits in a file this candidate edits.

## 8. Authority statement

This review grants no authority. Authority remains NONE across production,
release, settlement, verifier, migration, publication, and value movement. The
claim ceiling is byte-identical to the P27, P28, P29, and P30 packets and must
stay there. ACCEPT would be advisory in any case; this review returns REVISE.

---

## 9. Addendum — author acknowledgement and Lean serialization (post-review)

**NEW-26 was independently acknowledged by the author after this review closed.**
The author's account of the mechanism matches my trace in §5 point for point: the
`…canonical-exact-admission-v2` packet was shipped at S30 pinning the manifest
checker at its S30 bytes; S31 re-pinned the closure digest again; and the
post-commit gate at base `S31^` cannot see it because that packet is selected
only for `tests/core/test_global_settlement_canonical_admission_v1.py`, a path
changed at S30. The repair is planned for the next candidate as a
`…canonical-exact-admission-v3` packet plus a chain gate against the campaign
base ref, which is the durable repair this report asked for.

**The grade does not move.** Prior knowledge of a red gate is not a mitigation
of it. The frozen candidate C8-p12 still ships with
`check_test_hygiene_v1.py --base-ref 42ccb6624` exiting 1, and nothing in the
packet discloses it: `THV1-20260901-o008-formal-cycle-admission-v27`'s
`claim_scope` presents "the chain runs the repository hygiene gate against the
parent of every source commit before a packet is built" as the NEW-25 mitigation
without recording that the campaign-base gate is red under it. A disclosed red
would have been a different finding; an undisclosed one at the base the P29 P1
named is the P1 as filed. NEW-25 remains PARTIAL and NEW-26 remains P1.

**Lean serialization.** The protocol has moved to a shared
`flock -w 7200 /tmp/zenodex-lean.lock` for every Lean-bearing command. No Lean
work remains in this review, so nothing here needs re-running under the lock.
For the record, the detector I used was the exact-executable form the protocol
still endorses for inspection — `pgrep -x lean` and `pgrep -x lake`, never a
`pgrep -f` pattern that could match my own shell — and it did not misfire: every
Lean-bearing run in §2 and §3 completed cleanly (40, 6, and 6 passed; two
replays EXECUTED_PASS at 29 runs; the builder byte-identical), with no SIGBUS or
olean corruption observed at any point.
