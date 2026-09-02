# Opus independent review — candidate C9a

**Subject** `S28 = 431b5679df3f48d638d69343d98ed8d150eb1648` ("security: land C9a receipt admission for the asset-transfer fragment")
**Artifact** `P28 = 8d86d62489503320d9c1a6c53a558427d8b3f131` ("docs: freeze the O-008 formal-cycle packet at C9a")
**Branch** `codex/formal-core-fable-20260901`
**Review worktree** `/tmp/zenodex-formal-core-opus-c9a` (detached at P28)
**Reviewer** independent Opus; authority NONE; the claim ceiling does not move.

---

## Verdict

**Grade: C+**

The candidate is well-constructed and its evidence artifacts are genuine — every pin,
node id and mutation killer in the THV1 packet is real, the mint-path analysis behind
it is correct, and the containment story (registry `NO_PRODUCER`, zero consumers,
byte-identical claim ceiling) holds exactly as stated. But the central property the
candidate exists to establish is false as implemented. I reached a
`VerifiedLaneAllocationFragmentV1` whose fragment contradicts what the receipt proved,
using only public constructors and one overridden property on an ordinary subclass —
no `object.__new__`, no `object.__setattr__`, and with a genuine witness minted through
the real receipt-verification path. That falsifies the packet invariant
`C9A-JOURNAL-ROOT-EQUALITY-BINDS-ACCEPTED-TO-PROOF` and the claim_scope sentence
"one journal-root equality binds the caller's accepted value to the proof".

It is not lower than C+ because the surface is genuinely inert (nothing in `src/` or
`tools/` consumes the witness), the Rust twin already implements the missing guard,
and the fix is small, localised, and verified non-breaking. It is not higher because
the headline binding is the whole point of the candidate, and three of its five reject
codes carry no behavioural evidence at all.

---

## Replay results

| Gate | Result |
|---|---|
| `check_o008_formal_cycle_v1.py` (no replay) | exit 0, `ok: true`, `packet_admitted: true`, `current_source_drift: []`, `errors: []`, stderr empty, `proof_replay.status = NOT_RUN` |
| `check_o008_formal_cycle_v1.py --replay` | REPLAY_RESULT_PLACEHOLDER |
| `cargo test --release` (`zk/global_settlement_abi_v1`) | **527 passed, 0 failed**, no `error`/`FAILED`/`panicked` lines |
| `pytest tests/core tests/formal tests/test_check_o008_formal_cycle_v1.py` | PYTEST_RESULT_PLACEHOLDER |
| `pytest tests/core/test_asset_transfer_receipt_admission_v1.py` | 8 passed |
| Lean gates | driven serially by the checker's `--replay` (`lean_direct_check`, `lean_axioms_probe`, `lean_binding_gate`, `lean_certificate_direct_check`, `lean_certificate_axioms_probe`, `lean_certificate_binding_gate`) |

`tests/core/test_zusd_liquidation_partition.py` fails to *collect* on
`ModuleNotFoundError: generated.liquity_v1_sp_offset_redistribution_bounded`. That
directory is absent from the fable worktree as well — a pre-existing gitignored-artifact
gap, unrelated to C9a. It is excluded from the run above.

### THV1 packet integrity

* All 4 `source_pins` and the 1 `test_pins` sha256 match the worktree bytes at P28.
* All 8 pinned node ids exist and pass.
* `claim_ceiling` is **byte-identical** to the C8-p10 packet; the only changed
  top-level keys are `subject_commit`, `subject_parent`, `subject_tree`,
  `packet_commit_parent`, `hygiene_selection`.
* All 7 declared mutation killers verified by actually applying the mutation and
  running the named test:

| Mutation | Named test | Result |
|---|---|---|
| drop the journal-root equality | `test_foreign_accepted_value_is_rejected_at_the_journal_root` | KILLED |
| construct the witness outside the verifier | `test_witness_token_is_verifier_only` | KILLED |
| bypass the witness type gate | `test_admission_requires_the_module_witness_type` | KILLED |
| vary the statement root (object.__new__) | `test_forged_statement_root_is_rejected_behind_the_journal_binding` | KILLED |
| swallow/transform a producer reject | `test_producer_rejects_pass_through_unchanged` | KILLED |
| grow or reorder the reject family | `test_witness_reject_family_is_closed_and_ordered` | KILLED |
| mutate an input on a rejected admission | `test_witness_reject_is_a_no_op_value` | KILLED |

---

## The six claimed properties, adversarially

### 1. Admission only through the witness — **holds structurally**

`asset_transfer_receipt_admission_v1.py:138` gates with exact `type(witness) is not`,
not `isinstance`, so subclass and duck-typed witnesses are refused. I confirmed the
mint path is real: `verify_asset_transfer_lane_module_receipt_v1` snapshots and
revalidates the candidate, recomputes the structural release-route binding and compares
binding roots, then `_recompute_asset_transfer_lane_module_accepted_v1` re-runs the
deterministic transition from the input and raises unless the supplied acceptance equals
the recomputation; `_verify_rebound_module_receipt_v1` then requires
`ReceiptKindV1.SUCCINCT`, resolves the release, requires
`ReleaseStatusV1.ACTIVE_NEW and accepts_new_objects`, and feeds
`canonical_global_bytes_v1(expected.module_journal)` — the **recomputed** journal, not
the supplied one — to the verifier port as `expected_journal_bytes`. The witness is
mintable nowhere else.

Also verified: `copy.copy`, `copy.deepcopy` and `pickle` round-trips of
`VerifiedLaneAllocationFragmentV1` are all refused (`AttributeError: ... is immutable` —
the `__setattr__` guard blocks state restore), and the token gate rejects a foreign
token. `object.__new__` forgery of the output witness itself succeeds, but that is the
campaign's long-declared residual and applies equally to the pre-existing
`VerifiedLaneModuleTransitionV1`, so it is not a new gap. It does matter for calibration:
**Finding 1 below needs no such primitive**, which is exactly what makes it a real defect
rather than a restatement of the residual.

### 2. The journal-root equality is load-bearing — **FALSIFIED (Finding 1)**

The chain the packet relies on is real *for exact-typed values*: `journal_root` is a
computed property (`global_economic_proof_v1.py`) hashing the closed 13-field canonical
under `lane-module-transition-journal-v1`, and it re-validates on every access. That
preimage contains `private_port_root` and `receipt_root`;
`AssetTransferLaneModuleAcceptedV1.__post_init__` requires
`module_journal.private_port_root == private_port.port_root` (`:224`) and
`module_journal.receipt_root == _receipt_root(statement_root, journal, port, effects)`
(`:235`); and `port_root` hashes a canonical that includes `post_state`, whose canonical
includes `custody`. So one hash equality does pin the custody rows — **provided the port
is the exact class**. It is not required to be. See Finding 1.

### 3. Statement and occurrence checks are defensive double-binding — **holds; wording accurate**

Both are genuinely redundant given check 2. `command_occurrence_id` is a direct field of
the 13-field journal preimage. `statement_root` is not a journal field, but
`receipt_root = H(statement_root, pre, post, effect_plan_root, private_port_root,
terminal_obligations_root)` is, and `__post_init__` enforces that equality, so varying
the statement while holding the journal fixed requires a preimage. The candidate's own
test demonstrates this honestly: it reaches `WITNESS_STATEMENT_ROOT_DRIFT` only via
`object.__new__`, and its docstring says so in as many words. The module docstring's
"both derive from the journal" is slightly loose for `statement_root` (it is *bound by*
the journal, not computable *from* it), but the claim it supports — defensive, not
load-bearing — is correct. No overclaim here.

### 4. Producer pass-through untouched; rejects are values; token and immutability hold — **holds, with a caveat**

`src/core/global_accounting_lane_producers_v1.py` is byte-identical
(sha256 `26be354b…`, unchanged from the C8 packet's pin), so "untouched" is literally
true; the P28 doc diff only re-attributes that file's evidence row to the new packet.
All eleven producer codes and their message table are unchanged, every witness reject is
a returned value, and the no-op property is real (I confirmed
`test_witness_reject_is_a_no_op_value` kills an injected `object.__setattr__` on the
witness placed *before* the reject return). Caveat: pass-through is exercised for exactly
one of the eleven producer codes (`LANE_DISABLED`); the packet's boundary point "eleven
producer codes untouched" is satisfied by the file hash, not by behaviour through the
admission.

Note also that `ACCEPTED_INVALID` is declared in the Python enum and message table and
listed as check 0 in the producer docstring, but **no Python code path emits it** — the
docstring calls it unreachable-by-construction. That is pre-existing C8 scope and
honestly documented, but it is the code that would have named Finding 1's input class.

### 5. The accept path mints a real witness; the forged test is honestly labelled — **holds**

`_admission_fixture` runs the full ABI chain: real profile, real occurrence, real module
input, `transition_asset_transfer_lane_module_v1`, real release-route binding, and
`verify_asset_transfer_lane_module_receipt_v1`. The only stub is
`_RecordingReceiptVerifier`, which stands in for the injected cryptographic verifier
*port* — the campaign's established pattern, and the packet's nonclaims already say the
succinct-receipt check is inherited and adds no cryptographic claim here. "No forgery on
the accept path" is accurate. The forged-statement test names `object.__new__` in its own
docstring; that is honest labelling.

### 6. Registry stays NO_PRODUCER; ceiling byte-identical; authority NONE — **holds**

`LANE_ALLOCATION_PRODUCER_REGISTRY_V1[ASSET_TRANSFER] = (NO_PRODUCER, …)` is unchanged,
and the certificate checker rejects a `RECEIPT_BACKED` fragment for that lane at
`PRODUCER_KIND_DRIFT`. Grepping `src/` and `tools/` for
`asset_transfer_receipt_admission_v1`, `VerifiedLaneAllocationFragmentV1` and
`verify_asset_transfer_fragment_receipt_v1` returns hits **only inside the new module
itself** — no acceptance path consumes the witness. Claim ceiling verified byte-identical.
This containment is what keeps Finding 1 off the live path.

---

## Findings

### F1 — HIGH — A `VerifiedLaneAllocationFragmentV1` can be minted whose fragment contradicts the receipt

**Falsifies:** packet invariant `C9A-JOURNAL-ROOT-EQUALITY-BINDS-ACCEPTED-TO-PROOF`;
claim_scope "one journal-root equality binds the caller's accepted value to the proof";
and, in substance, `C9A-FRAGMENT-ADMITTED-ONLY-THROUGH-MODULE-WITNESS` (the witness is
required, but the admitted fragment is not what the witness proved).

**Capability required:** ordinary Python subclassing and public constructors. No
`object.__new__`, no `object.__setattr__`, no validation bypass. The witness is genuine.

**Root cause.** Two exact-type gates are missing:

* `src/core/asset_transfer_lane_module_v1.py:214`
  `if not isinstance(self.private_port, AssetLanePrivatePortV1):`
* `src/core/asset_lane_projection_v1.py:208` and `:210`
  `if not isinstance(self.pre_state/post_state, AssetLaneStateProjectionV1):`

combined with `port_root` being an ordinary overridable property
(`src/core/asset_lane_projection_v1.py:220`). Everywhere else the campaign uses the exact
form — `produce_asset_transfer_fragment_v1` gates all four of its arguments with
`type(x) is not T`, and the receipt candidates use `type(value) is not expected_type`.
These three are the outliers.

Because `__post_init__` compares `module_journal.private_port_root` against the port's
**reported** `port_root` rather than a root recomputed from the port's content, a subclass
that overrides `port_root` to return the genuine value carries arbitrary custody rows
through every check. The admission never revalidates `accepted`, and
`produce_asset_transfer_fragment_v1` reads
`accepted.private_port.post_state.custody` directly (`:310` for the coverage fold, `:337`
for the emitted `controlled_locations`).

**Reproduction** (`/tmp/zenodex-opus-c9a-poc2.py`, run with `PYTHONPATH=.` from the
review worktree). A single overridden property; the substituted projection is itself
fully valid, constructed by `dataclasses.replace`:

```python
class SpoofedPort(AssetLanePrivatePortV1):
    @property
    def port_root(self) -> str:
        return real_port.port_root          # the genuine, receipt-proved root

stolen_post = replace(real_port.post_state,
                      custody=(EconomicAmountV1(owner="attacker", asset="USD",
                                                custody_domain="vault", amount_atoms=100),))
evil_accepted = AssetTransferLaneModuleAcceptedV1(   # public ctor; __post_init__ runs in full
    statement_root=accepted.statement_root, post_state=accepted.post_state,
    effects=accepted.effects, module_journal=accepted.module_journal,
    private_port=SpoofedPort(..., post_state=stolen_post, ...))
```

Observed:

```
receipt-proved custody: (EconomicAmountV1(owner='custodian', ..., amount_atoms=100),)
admission result: VerifiedLaneAllocationFragmentV1
  ADMITTED with controlled_locations =
      (ControlledLocationRowV1(asset='USD', controlling_principal='attacker',
                               control_domain='vault', amount_atoms=100),)
  honest admission  controlled_locations =
      (ControlledLocationRowV1(asset='USD', controlling_principal='custodian',
                               control_domain='vault', amount_atoms=100),)
  same journal root / receipt digest?    = True
```

100 USD atoms of custody are reassigned from `custodian` to `attacker` inside a witness
stamped with the genuine `module_journal_root`, `receipt_digest` and `expected_image_id`.
A second variant (`/tmp/zenodex-opus-c9a-poc.py`) shows the same result on the stock
fixture using an additional `__post_init__` override to escape supply conservation.

**The Rust twin is already immune, so this is also a language divergence.**
`zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs:125` compares
`self.module_journal.private_port_root != self.private_port.port_root()?` where
`port_root()` is an inherent method on a concrete struct — no dynamic dispatch, no
subclassing — and the Rust producer calls `accepted.validate()` as check 0 and emits
`ACCEPTED_INVALID`. The same conceptual input is refused in Rust and admitted in Python.

**Verified fix.** Changing the three gates to the exact-type form refuses the PoC
(`TypeError: asset lane port post-state is invalid`) and leaves
`tests/core/test_asset_transfer_receipt_admission_v1.py`,
`tests/core/test_global_accounting_lane_producers_v1.py` and
`tests/core/test_global_settlement_abi_v1.py` green — **113 passed**. Note that merely
adding an `ACCEPTED_INVALID`-style revalidation in the admission does **not** close it:
re-running `__post_init__` re-runs the same `isinstance` gate and the spoofed port passes
again. The gate itself, or a recomputation of `port_root` from an exactly-typed snapshot,
is the fix.

### F2 — MEDIUM — `claimant_entitlements` are wholly caller-chosen and this is not a declared nonclaim

No subclassing and no forgery needed: with a genuine witness and a genuine `accepted`,
the caller picks claimant identities and splits freely. `produce_asset_transfer_fragment_v1`
keys its coverage fold on `(asset, control_domain)` (`:319-326`) — the **claimant is not in
the key** — so any claimant string and any partition of the per-key total is admitted:

```
claimant='custodian'      -> ADMITTED
claimant='attacker'       -> ADMITTED
claimant='anyone-at-all'  -> ADMITTED
99/1 split                -> ADMITTED (attacker 99, custodian 1)
```

The producer's own docstring is accurate (it claims coverage, not claimant correctness),
but C9a's stated purpose is to remove caller trust, and the minted witness carries these
unproven rows inside a value whose name asserts receipt-verification. The packet's
`nonclaims` list does not mention it. Either bind the claimant rows or add the nonclaim
before C9b consumes this witness.

### F3 — MEDIUM — Three of the five witness reject codes have zero behavioural evidence

Deleting each check outright leaves all 8 tests green:

| Deleted check | Suite result |
|---|---|
| `WITNESS_KIND_DRIFT` | 8 passed (SURVIVED) |
| `WITNESS_OCCURRENCE_DRIFT` | 8 passed (SURVIVED) |
| `WITNESS_BINDING_ROOT_DRIFT` | 8 passed (SURVIVED) |

Only `WITNESS_JOURNAL_ROOT_DRIFT` and `WITNESS_STATEMENT_ROOT_DRIFT` are exercised by
behaviour; `test_witness_reject_family_is_closed_and_ordered` asserts the enum listing
only. Since nothing outside this file imports the module, that file is the whole coverage
surface. The packet's boundary dimension "exact five closed witness codes in check order"
overstates what the evidence establishes.

### F4 — LOW — Check (4) is structurally unreachable but is not labelled defensive

`asset_transfer_receipt_admission_v1.py:174` compares `produced.binding_root` against
`accepted.module_journal.receipt_root`, and the producer assigns
`binding_root=journal.receipt_root` from that same journal
(`global_accounting_lane_producers_v1.py:350`). No caller-supplied input can make them
differ; I confirmed it fires only when the *producer* is mutated to emit a different
root. As producer-drift protection it is worth keeping, but the module docstring marks
checks (1) and (3) "defensive" while presenting (4) as a load-bearing binding, and the
packet's claim_scope lists it as a distinct binding step and ties the failure mode "a
fragment binds a receipt root the witness never certified" to it. It binds nothing to the
witness — the witness carries no receipt-root field; check 2 is the only witness binding.
Label it as (1) and (3) are labelled.

### F5 — INFO — Stale forward references and no Rust twin

* Both producer docstrings still say "C9a **will** take the witness" in the future tense
  (`global_accounting_lane_producers_v1.py:12, 226`;
  `zk/.../global_accounting_lane_producers.rs:227`) after C9a has landed.
* There is no Rust twin of the admission wrapper, so the two surfaces have diverged:
  Python callers can go through the admission, Rust callers still take the raw accepted
  value. The packet claims no parity, so this is not an overclaim — but it should be an
  explicit open gap for C9b.

---

## What I could not falsify

* No path to a `VerifiedLaneAllocationFragmentV1` through `copy`, `deepcopy`, `pickle`,
  or a foreign construction token.
* No construction-legal way to vary `statement_root` while holding the journal fixed
  (the `receipt_root` preimage pins it) — the candidate's own claim here is sound.
* No way to defeat the mint path: the recomputation, the structural rebinding, the
  `ACTIVE_NEW` release requirement and the recomputed-journal-bytes argument to the
  verifier port are all genuinely enforced.
* No drift in the claim ceiling, the registry, or the producer file.

---

## Recommendation

**REJECT_PENDING_REPAIR.** The candidate's structure is right and most of it is
well-evidenced; the defect is narrow and the repair is three tokens plus tests. Before
re-cut:

1. Change the three `isinstance` gates to exact `type(...) is not` (F1) and add a
   negative test that a subclassed private port reporting a spoofed `port_root` is
   refused. Consider whether the same audit is owed to the other `isinstance` gates on
   this path.
2. Add behavioural tests for `WITNESS_KIND_DRIFT`, `WITNESS_OCCURRENCE_DRIFT` and
   `WITNESS_BINDING_ROOT_DRIFT`, or state in the packet that they are defensive and
   unreachable from a minted witness (F3, F4).
3. Add the nonclaim that `claimant_entitlements` remain caller-chosen and are covered
   only per `(asset, control_domain)` (F2).
4. Fix the future-tense producer docstrings and record the missing Rust twin as an open
   gap (F5).
5. Re-cut S/P and re-pin the THV1 packet.

Authority remains NONE; the claim ceiling did not move and must not move on this
candidate.
