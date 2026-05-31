# ZenoDEX Trust-Minimization Target

The target is to make ZenoDEX settlement validation independent of the operator
host for every admitted transition family. The host is treated as adversarial:
it may compute the wrong state, omit proof inputs, emit malformed metadata, or
run inside a perfectly hardened container and still lie about execution.

Docker is useful for packaging, reproducibility, and sandboxing. It is not a
correctness boundary. Correctness comes from deterministic replay, zkVM receipt
verification, governed verifier profiles, and fail-closed admission.

## Target Rule

```text
AcceptTransition(t) :=
  DeterministicReplayAccepts(t)
  or ValidZkReceiptAccepts(t, allowed_profile)
```

If a transition family is outside both replay and proof coverage, a
proof-required profile must reject it before settlement.

For light clients, the stronger target is:

```text
AcceptCheckpoint(c) :=
  FinalityQuorumAccepts(c)
  and ProofMetadataAdmitted(c)
  and VerifierReportAccepts(c)
  and JournalBindsHeaderRoots(c)
```

This removes host execution trust only for surfaces whose profile is closed. It
does not remove data-availability, finality, verifier-binary, cryptographic, or
guest-image assumptions.

## Why RISC0 Is Still Opt-In

RISC0 is opt-in today because the current guest is scoped. It covers the spot v1
successful path for create-pool, swap-exact-in, add-liquidity,
remove-liquidity, faucet mint, and one liquidity-cycle block. The repo still
records open gaps for UPBA batch clearing, oracle critical actions, zUSD,
perps, proof-market rewards, recursive aggregation, and production light-client
finality.

Making proof mandatory before those gaps close would either reject valid
ZenoDEX actions or tempt the system to trust host-projected booleans for
unsupported paths. The safer rule is profile-specific proof requirement:
covered operations can be proof-required, uncovered operations must be replayed
or rejected.

## Lower-Than-Uniswap Trust Target

For this repo, "lower than an Ethereum smart-contract AMM baseline" means a
settlement observer should not need to trust an operator host, RPC server, or
single execution environment for application transition correctness. The path
to that claim is:

1. Every value-moving transition is either deterministically replayed by
   validators or covered by a real zkVM guest.
2. Every proof-required block binds the proof journal to the ledger header,
   pre-state root, post-state root, transaction commitment, nonce roots, and
   accepted receipts root.
3. The verifier registry admits only governed proof kinds, verifier IDs, guest
   image IDs, and toolchain lock hashes.
4. Unsupported operations fail closed under proof-required profiles.
5. Light-client checkpoints compose proof verification with finality/quorum
   verification.
6. Full nodes retain replay as an audit path until recursive block or epoch
   proofs cover the full admitted surface.

The current status is `frontier_open`, recorded in
`docs/ZENODEX_TRUST_MINIMIZATION_TARGET_V0.json`. The checker rejects any
attempt to flip the target to achieved while required surfaces remain open.

## Local Gate

```bash
python3 tools/check_zenodex_trust_minimization_target.py --pretty
pytest -q tests/test_check_zenodex_trust_minimization_target.py
```

The gate is deliberately conservative. It allows the scoped RISC0 spot claim,
requires open gaps to point at the proof coverage matrix, and requires non-claims
that prevent host-independent or lower-than-Uniswap language from being promoted
before the proof/replay frontier closes.
