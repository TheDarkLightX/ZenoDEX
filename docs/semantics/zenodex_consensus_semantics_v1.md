# ZenoDEX Consensus Semantics Contract v1

This is the semantic front door for consensus, proof, guest, and differential
work. Load this before changing a consensus transition, proof guest, runtime
authority path, or evidence claim.

## Authority Order

1. The live consensus authority path defines current semantics.
2. Proof guests, Rust ports, Tau mirrors, ESSO models, and differential harnesses
   must refine the live semantics, or their claim must be scoped to the layer
   actually tested.
3. Core transition semantics and transaction-envelope semantics are separate.
4. Replay, authorization, sender binding, and transaction uniqueness normally
   belong to the envelope unless the operation contract says they are part of
   the core transition.
5. A differential may claim `live_equivalent` only when it drives the live
   admission path and the core transition. A modeled envelope supports only
   `modeled_envelope_equivalent`.

Practical rule for agents: preserve live semantics. If a guest or proof wrapper
disagrees with the live authority, fix the wrapper or scope the claim. Ask the
user only when two live authority paths conflict or this contract has no entry.

## Claim Levels

- `core_equivalent`: the guest or port matches the Python core transition under
  already-admitted inputs.
- `modeled_envelope_equivalent`: the guest or port matches Python under a
  harness-modeled envelope. This is useful evidence, but it is not a live
  admission claim.
- `live_equivalent`: the guest or port matches the actual live transaction
  admission path plus the core transition.

Only `live_equivalent` may be described as production 1:1 equivalence.

## Perps-NP DepositCollateral

Operation: `perps_np.deposit_collateral`

Core semantics:

- `deposit(0)` is valid account join / account creation behavior.
- `amount_e8 >= 0` is allowed.
- A negative amount is rejected.
- Core deposit does not consume or advance the account nonce.
- Core deposit credits collateral and `net_deposited_e8` by exactly `amount_e8`.

Envelope semantics:

- Sender authorization is checked before core execution.
- Replay protection is the transaction/admission layer's responsibility.
- Duplicate transaction envelopes reject before core mutation.

Guest and proof obligations:

- `collateral_binding` is witness or envelope data unless a live-path binding
  proves otherwise.
- Guest post-snapshot equality against Python core is a `core_equivalent` claim.
- Guest equality under a hand-modeled nonce/replay wrapper would be only a
  `modeled_envelope_equivalent` claim.
- P0-3b CLOSED (2026-06-06): the differential delegates the nonce decision to the
  live replay authority `src/core/replay_guard.py`::admit (strict-sequential), and
  the guest (`zk/state_proof_risc0/shared/src/surfaces.rs`) was fixed from a weaker
  MONOTONE nonce (which accepted gap nonces the chain rejects) to the same
  strict-sequential rule. The claim is therefore `live_equivalent`, scoped to that
  replay authority. Production replay is enforced at the tau-node `tx_sequence`
  layer (`src/integration/perps_wallet_api.py`:2764 / 2885-2889), modeled in Python
  by replay_guard.admit; see the contract `envelope.chain_replay_layer`.

The executable BDD front door for this entry is:

- `docs/semantics/perps_np_deposit_collateral.feature`
- `config/semantics/zenodex_consensus_contract_v1.json`
- `tests/semantics/test_zenodex_consensus_bdd.py`
