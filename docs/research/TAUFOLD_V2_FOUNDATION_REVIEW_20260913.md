# Review of the delivered TauFold V2 foundation

Status: useful execution and proof-admission work; transport repair required.
No economic authority or V3 completion claim. TauFold's six release milestones
are separate from ZenoDEX V3's workstreams and capability denominator.

## Reviewed subject and fresh evidence

The delivered `zkvm/v2/evidence/manifest.json` has SHA-256
`45398260cab179ae82571fcf779b34cbea7941c643821c96c27c1da82bfaa396`.
All 86 inventoried files matched before copying the review subject. Twelve
external ZenoDEX, ZenoFCIS and Orbit file pins also matched their current source.
ZenoDEX HEAD was `fbcfc7a04067d5f00bbb05ef1a568ec347093d67`.

Fresh replay passed eight core test groups, 8,480 Python arithmetic vectors,
the Z3 translation/accounting obligations and semantic mutants, and generated
Rust source equality. The supplied Rust-vector, native-Tau, browser and genuine
receipt reports remain historical evidence for this review. The measured V2
executable was absent from the inspected build locations; its location has
been requested so the three receipts can be replayed without a guest rebuild.
Expected verifier digest:
`48208e3bf30f4328862efbb4d37b38141bb1ceab00cc5f9c15eab46fa6185278`.

Root Astra reviewed the independent oracle and host integration. A separate
Astra reviewer inspected the U256 core, generated transition, guest, native
verifier, canonical statement and ZenoDEX adapter. No additional blocker was
found in that scoped V2 source review; this is not universal Rust refinement.

## Confirmed transport regression and repair candidate

The newly delivered `zkvm/adapters/python/taufold_adapters/process.py` differs
from the earlier reviewed handoff. Its SHA-256 is
`eb31b722f80b5cda0bec056a256a7b3f80273f4d3373473a9e07bb07eed68019`.
`_exchange` checks time before waiting, then can return a result observed after
the deadline. A real child and deterministic clock reproduced acceptance at
61 seconds against a 60-second deadline. This falsifies the deadline contract;
it does not demonstrate acceptance of an invalid cryptographic proof.

The [retained regression](taufold_verifier_handoff_20260913/probe_v2_transport_deadline.py)
exits 1 against the delivered source and 0 against the isolated
[repair candidate](taufold_verifier_handoff_20260913/v2-deadline-repair.patch).
That patch rechecks time after polling and after observing exit. An ordinary
exchange still succeeds. Repaired source digest:
`124e1042529515d296decad8a9bc37f8852e0f06bdb85e27f2bca461e78b0dd8`.
The TauFold owner's working tree was not edited. Apply/review there and rerun
the hostile-process and real-receipt gates before claiming M1 passes again.

```bash
python3 -B probe_v2_transport_deadline.py --source "$TAUFOLD_ROOT" --report deadline.json
```

## Integration conditions that remain open

1. Bind each account/policy to its asset denomination and units in authenticated
   host state. The state commitment binds deployment/account/policy/sequence;
   asset and epoch elsewhere in the statement do not establish that relation.
   Authenticate the current predecessor, epoch and operation-specific authority.
2. Retain exact individual reservations: command, maximum amount, destination,
   recipient and terminal outcome. An aggregate `reserved` amount cannot prove
   which request may finalize or cancel. Preserve denial and no-effect behavior.
3. Qualify the existing Spot semantics through a complete V2 economic route and
   publisher. The inspected V1 pipeline accepts only `asset_transfer`; V2 custody
   dispatch supports transfer and managed-asset lifecycle. Neither supplies a
   qualified swap route. A real `SwapIntent` class and guard receipt alone do
   not establish executable amount limits, pool/asset accounting or settlement.
4. Define the admitted receipt kinds explicitly. The current native verifier
   accepts every non-Fake receipt kind supported by its RISC Zero context;
   supplied receipts cover succinct proofs. The Python method name alone does
   not establish a succinct-only contract or qualification of other kinds.

Reuse the existing publisher and verifier contracts. The TauFold guard supplies
an additional admission predicate; its account effect cannot substitute for the
full economic pre/post state, exact effects, replay record and atomic commit.
ZenoFCIS catalog/vault/UI work remains with the TauFold agent. The current V3
margin receipt/current-store acceptance remains a separate outstanding task.

No new proof build, Rust/native-Tau execution, browser replay or deployment ran
in this review. The inherited ZenoDEX claims-registry missing-file failure is
unchanged. Assessment is `NOT_RESCORED`; no lane or value-safety gate closes.
