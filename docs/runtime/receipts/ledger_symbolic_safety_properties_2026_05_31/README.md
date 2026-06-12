# ZenoLedger Symbolic Safety Properties Receipt

Date: 2026-05-31

This receipt records bounded property-based disaster-witness checks for three
ZenoLedger finality-adjacent Python surfaces:

- `zeno_ledger_bonded_slashing_v0`
- `zeno_ledger_anti_equivocation_v0`
- `zeno_ledger_dynamic_peers_v0`

These checks are boundary-discovery evidence. They are not a proof of consensus
correctness.

## Properties Added

- Bonded slashing, 160 generated cases:
  accepted slash receipts satisfy `1 <= slash_amount <= available_bond`,
  `burn_amount + treasury_amount == slash_amount`, the updated bond entry
  records exactly the new slashed total, and the receipt revalidates against the
  pre-registry, evidence, and policy.
- Checkpoint anti-equivocation, 160 generated cases:
  conflicting checkpoints for the same `(chain_id, height)` are rejected, while
  an exact duplicate checkpoint is accepted.
- Dynamic peer admission, 160 generated cases:
  accepted admissions preserve the peer-count cap, bind to the peer-check report,
  deduplicate canonical URLs, and admit only candidate URLs absent from the
  current set.
- Dynamic peer teeth regression:
  a peer-check report over a different URL set is rejected.

## Commands

```bash
python3 -m pytest -q \
  tests/integration/test_zeno_ledger_symbolic_safety_properties.py
```

Result:

```text
4 passed in 2.90s
```

Focused existing-surface check:

```bash
python3 -m pytest -q \
  tests/integration/test_zeno_ledger_bonded_slashing_v0.py \
  tests/integration/test_zeno_ledger_anti_equivocation_v0.py \
  tests/integration/test_zeno_ledger_dynamic_peer_exchange_v0.py::test_dynamic_peer_admission_is_hash_bound \
  tests/integration/test_zeno_ledger_symbolic_safety_properties.py
```

Result:

```text
25 passed in 2.67s
```

## Existing Harness Note

The full `test_zeno_ledger_dynamic_peer_exchange_v0.py` file still contains an
HTTP route test that builds a public-testnet bundle. In this environment that
fixture failed before reaching dynamic-peer logic because the generated feature
suite rejected `proof_mining_core`. The pure dynamic-peer admission test and the
new symbolic dynamic-peer property both passed.
