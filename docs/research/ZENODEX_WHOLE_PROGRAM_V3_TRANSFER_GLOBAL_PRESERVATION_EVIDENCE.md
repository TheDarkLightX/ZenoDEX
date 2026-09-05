# Restricted transfer-to-global accounting preservation

Date: 2026-09-05. Status: **PROVED for the stated mathematical lift; TESTED on
three Python transfer controls; runtime refinement and publication remain open.**

The reviewed baseline is `7b2467067c8c978e9eca19ddd33a24ce0740560d` plus the two
new files below. Concurrent receipt, coordinator and route candidates are outside
this proof subject. No existing theorem, gate, production source, guest ABI,
image or generated manifest was changed by this packet.

## Derived result

`AssetTransferGlobalPreservationV1.step` calls the existing
`AssetTransferRefinementV1.transition`. Acceptance materializes its post-balance
function into the existing V2 mathematical global state; rejection returns the
entire input state. The global accounting frame changes only balance rows.
Supply, custody, reserves, claimant liabilities, terminal rows, roots, replay,
Oracle, height, profile and outbox fields remain equal to the input fields.

The universally quantified result has these explicit premises:

- `Represents`: the complete global balance list is the materialization of one
  local asset over an explicit finite principal list; the sole global supply
  row equals that local asset and its supply.
- `RoleCoverage`: sender, recipient and fee owner each occur exactly once in
  that list. Fee owner may equal sender or recipient. Coverage is not inferred
  from conserved totals or from a receipt.
- The existing V2 `OwnedMatchesSupply` predicate holds before the step. Exact
  per-asset/domain custody-to-claim partition and claimant/terminal backing are
  separate initial premises when their preservation is claimed.

`step_account_totals` derives preservation from the existing local
`accepted_conserves_total` theorem. `step_owned_supply` then derives the existing
V2 owned-supply equality for every asset. Physical ownership accounting is
exactly V2's balances + custody + reserves; claimant and terminal amounts are
not added to that quantity. Neither theorem takes a desired postcondition or a
postcondition-bearing `Verified` witness as a premise.

`step_frame`, `step_exact_allocation` and `step_claimant_backing` preserve the
entire relevant tables, their per-asset/domain exact partition, and the existing
claimant-addressed open-terminal coverage predicate. This partition is a scoped
mathematical predicate, not the full lane allocation certificate.

`step_rejection_is_noop` proves complete modeled state equality and an empty
local effect plan on rejection. `step_changes_only_for_context_subject` proves
that any change by this lift requires `command.sender = context.subjectId`.
It splits the actual transfer verdict and uses rejection purity and the existing
accepted guard. Authenticating the context for the exact command remains an
external obligation. `run_preserves_accounting` proves preservation by induction
over arbitrary finite input lists under explicit step-by-step principal coverage.

## Nonvacuity and negative evidence

The nonempty control has accounts `(100, 10, 5)`, custody `10`, claimant liability
`10`, an open terminal obligation for that exact claimant/asset/domain of `10`,
and supply `125`. Thus physical owned supply is `115 + 10 = 125`, with liability
atoms counted separately. Sending `30` with fee `2` produces `(68, 40, 7)`.
The sender-fee-owner alias produces `(70, 40, 5)` and recipient alias produces
`(68, 42, 5)`. These three Lean results match the existing Python transition on
the corresponding valid local states with supply `125`.

A mixed trace contains an unauthorized rejection followed by two accepted
transfers; its final accounts are `(36, 70, 9)`. The arbitrary-trace theorem is
also instantiated on this nonempty trace.

The retained controls demonstrate these distinct failures:

| Change | Required observation |
| --- | --- |
| Omit the fee owner from the principal enumeration | Observed account total loses two atoms; universal conservation without coverage is false. |
| Add one account credit | Owned supply becomes `126` against supply `125`. |
| Substitute Mallory for Alice in the claimant row | Aggregate custody-to-claim partition remains exact; Alice's open terminal obligation becomes uncovered. |
| Treat Mallory's context as Alice's authorized command | The assertion of acceptance is kernel-decided false. |
| Erase claimant rows only inside `step` | The unchanged-frame theorem and nonempty allocation control fail. |
| Replace the context subject only in `step`'s transfer call | The lift's authority theorem and the concrete unauthorized trace control fail. |

The last two are implementation-only semantic mutants. The test asserts that
every byte from `theorem step_frame` onward is unchanged, then requires compiler
errors within the named obligation and control source spans. This preserves the
theorem statements and rejects a parser-failure-only mutation result. Earlier
all-source mutation evidence remains historical inside the retained archive.

## Exact source and checker evidence

| Subject | SHA-256 |
| --- | --- |
| `lean-mathlib/Proofs/AssetTransferGlobalPreservationV1.lean` | `350d22ed8796f9c847913f7b5a03f079ec33b484de1786fe3e95158c514aec7f` |
| `tests/formal/test_lean_asset_transfer_global_preservation_v1.py` | `831c33bc69be18ecbde270d1fb33f8685220b1840722f421be24433d196634a2` |
| Imported `AssetTransferRefinementV1.lean` | `2d9ed7beb6feb47b67afa63a40d1203bcca9004b49ba978b9927edded6a04932` |
| Imported `GlobalEconomicStateRefinementV2.lean` | `c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1` |
| Transitive `GlobalSettlementCoreV2.lean` | `2ce254367dc8e8299f82f8a93e09c1d470f3a218ed01af7efb766946a34255a4` |

All Lean compilation and theorem qualification ran remotely with affinity to
two CPU cores. The checker was the existing pinned Lean `4.27.0`, binary SHA-256
`8fadc3ed92cc9decb94c96ee9c0876e91e03a3a5e69138f32114f02789e2766c`.
This proof adds no Mathlib imports or dependencies. It reuses the configured
project environment; the existing Mathlib pin remains unchanged.

```bash
cd lean-mathlib
lake build Proofs.AssetTransferGlobalPreservationV1
lake env lean -DwarningAsError=true Proofs/AssetTransferGlobalPreservationV1.lean
cd ..
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_global_preservation_v1.py
```

The final gate passed **12 tests in 21.39 seconds**. Its 13 captured subprocess
commands include focused build, warning-as-error compilation, all 25 declared
theorem axiom audits, the repository placeholder scanner, three Python/Lean
controls, four kernel-decided false statements and two implementation mutants.
The actual axiom output contains only `propext` and `Quot.sound`; several
concrete controls use no axioms. Declaration counts identify the audit surface,
not independent whole-program obligations or completion progress.

Local Ruff passed. The local placeholder companion test passed, with the other
11 tests deliberately left to the remote configured checker. There was no heavy
local proof build and no additional remote instance or GPU allocation for this packet.

The final retained bundle is `zenodex-v3-transfer-global-evidence06.tar.gz`,
98,597 bytes, SHA-256
`b241226b1246923c4bcd6fdb7ff1aebd953e68864ad82d63ac335fbec8f81aa4`.
It contains the exact source subject, checker runner, receipt, all actual
stdout/stderr, exact negative probe files, source/hash mappings, and previous
passing evidence. Its final receipt SHA-256 is
`6d985d91f7f680fb3d886182c5eb3d5a73b39cf1c475c8e9ef817f5b63437b07`;
the command ledger SHA-256 is
`74243a13f4c6aead33829994f6fa96c869d65f141a8b16bbfd75138471011664`.
The exact axiom output SHA-256 is
`e20788c8b9ae7308f381432a69d5343fc7924f84dfae634dde60b72f04ac1f6f`.

## Remaining obligations

This advances the restricted mathematical construction portion of W09. It does
not close full V2 `Verified` construction, W04 allocation certificate derivation,
all twelve lanes, any complete cross-lane economic route, or production safety.

The lift retains zero balance rows and does not prove canonical sparse
serialization, unique global keys, principal-enumeration provenance, row/byte
ceilings, Rust finite-width implementation refinement, or global admitted-state
preservation. Its general state space is algebraic `Int`; actual input
admission and finite-width constraints remain separate premises and obligations.
The three concrete Python comparisons are bounded controls, not a universal
runtime refinement proof.

Static roots, height, replay and outbox make this an accounting projection, not
a valid global publication transition. Exact-command authentication, policy
provenance, source snapshot authenticity, claimant ownership, receipt checking,
effect/journal binding, restart authorization and actual datastore refinement
remain outside this theorem. No settlement, publication, migration, writer,
release or production authority is created.

The next constructive bridge must connect canonical admitted runtime rows and
the actual coordinator/effect transition to these explicit representation and
frame premises, while deriving the remaining lifecycle, replay, root and
publication obligations. Existing V2 theorem statements and historical evidence
remain intact for that work.
