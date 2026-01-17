# Proof Mining (Verified Computation Rewards)

This document defines **proof mining** for ZenoDex: a mechanism to (1) bootstrap token distribution and (2) harden
correctness by paying for **verifiable** computation rather than trusting operators.

The key principle is MPRD-style:

> **Anyone may propose. Only a proof-carrying decision executes.**

## 1) What “proof mining” is (and is not)

- **Is:** rewarding actors who produce *publicly verifiable* evidence that a specific ZenoDex transition is valid.
- **Is not:** “paying nodes for uptime” (not objectively verifiable without extra infrastructure).
- **Is not:** a promise of price appreciation; it’s a security + liveness mechanism for computation.

## 2) Roles

- **Proposer / Block producer:** packages intents/batches and publishes commitments (`merkle_root`, `state_hash`).
- **Prover (proof miner):** produces a *validity proof* (or a bounded proof-carrying bundle) for a specific batch/state
  transition.
- **Verifier (full node):** checks proofs (fail-closed) and rejects blocks that claim invalid transitions.
- **Light client:** verifies commitments + proofs without replaying execution.

## 3) Objects and commitments (what gets hashed)

We make every “thing that matters” content-addressed.

### 3.1 Canonical inputs
- `rules_bytes`: the active Tau rules text (already committed by Tau Testnet `state_hash`).
- `accounts_hash`: canonical hash of balances + sequence numbers (already committed by `state_hash`).
- `dex_state_before_bytes`: canonical JSON snapshot (ZenoDex-specific).
- `batch_bytes`: canonical encoding of DEX intents to apply (swaps, LP add/remove, etc.).
- `witness_bytes`: external-computation witnesses required by the rules (hi/lo limbs, computed outputs, etc.).

### 3.2 Canonical outputs
- `dex_state_after_bytes`: canonical JSON snapshot after applying the batch.

### 3.3 Commitment hashes
Define:
```text
dex_hash_before = SHA256(domain_sep || dex_state_before_bytes)
batch_hash      = H(batch_bytes)
witness_hash    = H(witness_bytes)
dex_hash_after  = SHA256(domain_sep || dex_state_after_bytes)
```

Define a single **proposal hash** binding the whole transition:
```text
proposal_hash = H(chain_id || prev_state_hash || batch_hash || witness_hash || dex_hash_after)
```

This makes replay and equivocation detectable: a proof is only “for” one specific before/after pair.

## 4) Proof artifact (what a miner produces)

There are two useful phases:

### Phase A (receipt mining): proof of decision + binding
The prover produces a **decision bundle** (MPRD-style) that is verifiable and fail-closed:
- commits to `proposal_hash`
- commits to `policy_hash` / `policy_epoch` / `registry_root` (what rules/gates were enforced)
- includes anti-replay nonce binding
- optionally includes a ZK receipt proving in-guest evaluation of the gate + binding

This phase provides strong auditability and prevents “operator discretion”, but full nodes still re-execute DEX math to
enforce validity of the transition.

### Phase B (validity mining): proof of transition validity
The prover provides a proof that the **DEX transition is valid**, and that it binds to `proposal_hash`. In practice:
- a Risc0 receipt proving: “given committed `rules_bytes`, `dex_hash_before`, `batch_hash`, and witnesses, the resulting
  `dex_hash_after` is the correct application of the rules.”

This phase enables light clients to verify correctness without replay.

## 5) How it fits Tau Testnet Alpha (today)

Tau Testnet Alpha already commits to:
- `merkle_root` over transactions
- `state_hash` which commits to rules + accounts hash (+ optional DEX hash)
- optional DEX snapshots published under `dex_state:<dex_hash>`

Proof mining plugs in by treating the proof bundle/receipt as **a transaction**:
- include the bundle (or its hash + fetch locator) in the block’s tx list → committed by `merkle_root`
- keep `dex_hash_after` committed in `state_hash`
- publish the bundle in DHT (proposed key): `mprd_bundle:<bundle_hash>`

This yields a simple verifiable chain:
`merkle_root` commits to the proof, and `state_hash` commits to the resulting state.

## 6) Reward rule (what gets paid, and when)

The reward must be **objective, bounded, and non-gameable**.

### 6.0 No-minting default for ZenoDex
ZenoDex can do proof mining **without protocol minting** by paying provers from a pre-funded reward pool (treasury
balance). This keeps total supply fixed; distribution is a controlled spend.

Operationally:
- A “reward pool” address/account is funded at genesis or via fee routing.
- A proof that is valid and unique authorizes a transfer **from the pool** to the prover.
- When the pool is empty, rewards stop (but proofs may still be required for validity).

The bounded model spec `src/kernels/dex/proof_mining_manager_v1.yaml` captures this conservation rule explicitly:
`total_paid + reward_pool_balance == initial_pool`.

### 6.1 “First valid proof wins” (race model)
- For a given `proposal_hash`, the **first** valid proof included in the canonical chain wins the reward.
- Subsequent proofs for the same `proposal_hash` are valid-but-unrewarded.

This creates an open market for provers without paying duplicates.

### 6.2 Deterministic emission schedule
Define a deterministic per-epoch reward:
```text
reward(epoch) = base_reward * decay(epoch)
```
Examples:
- step halving every `H` epochs (simple, bounded), or
- exponential decay `reward = floor(base_reward * r^epoch)` (Zeno-style, bounded).

### 6.3 Reward transaction semantics
On acceptance of a proof:
- mint `reward(epoch)` to the prover’s address, or
- pay from a dedicated reward pool balance.

In either case, the rule should be expressed as **pure state transition constraints**:
“if and only if proof is valid and unique, then minted amount equals the schedule.”

## 7) Fail-closed verification (how to avoid “trust me bro”)

Proof verification must be fail-closed:
- missing bundle → no reward (and optionally block invalid if proofs are mandatory)
- invalid receipt → reject
- unknown image id / policy hash not authorized → reject
- wrong binding (proposal_hash doesn’t match committed hashes) → reject

### Tau-specific nuance (MPRD pattern)
Tau is excellent at combining **boolean rails** and bounded arithmetic, but not at verifying cryptographic receipts.
So the standard split is:
- **Host/verifier** checks crypto and structure (signatures, Risc0 receipt validity, hash matches).
- Host produces boolean signals (`proof_ok`, `binding_ok`, `policy_ok`, `nonce_ok`).
- **Tau rules** combine those signals to authorize minting and to enforce caps/one-hot/anti-replay structure.

This matches the “host computes, Tau validates” design used throughout this repo.

In ZenoDex’s no-minting default, the Tau side authorizes a **treasury-style payout** (pool → prover) rather than minting.
Reference gate spec: `src/tau_specs/proof_mining_reward_32_v1.tau`.

## 8) Sybil/spam considerations

Proof generation is expensive, but verification still has a cost. Common mitigations:
- limit proofs per block (DoS cap)
- require a fee for proof submissions (covers verification)
- require nonces / one-proof-per-proposal uniqueness
- keep the verifier allowlist strict (signed image manifests / authorized policy registry roots)

## 9) Implementation checklist (concrete next steps)

1) Define canonical `dex_state` JSON schema + hashing (align with Tau Testnet `dex_state:<hash>`).
2) Define canonical `batch_bytes` and `witness_bytes` encodings.
3) Define the proof bundle transaction format and a DHT key for fetching it.
4) Implement verifier logic (Phase A first): bundle verification + binding checks + reward mint rule.
5) Upgrade toward Phase B: validity proofs over DEX transitions (light-client grade).

## Appendix: Minimal module interfaces (what to build)

### `proof_mining_manager` (consensus-critical)
Purpose: enforce one-reward-per-proposal and determine reward amounts.

For the “no minting” variant, it must at least track:
- `reward_pool_balance` (remaining rewards budget)
- `total_paid` (accounting)
- a **claimed set** keyed by `proposal_hash` (or a safe surrogate in bounded models)
- `epoch` (or block height proxy) if rewards decay over time

Reference model spec (bounded surrogate for the claimed set):
- `src/kernels/dex/proof_mining_manager_v1.yaml`
- Action `submit_proof(proposal_slot, prover_id, proof_ok, binding_ok, policy_ok, nonce_ok)` emits:
  - `reward_amount` (the spend amount)
  - `reward_kind = TreasuryTransfer`
  - `paid = true`

### `ledger / token transfer` (already exists in chain runtime)
Purpose: apply the actual transfer from the reward pool to the prover.

On Tau Testnet Alpha, “accounts/balances” already exist as consensus state; proof mining integrates by authorizing a
deterministic transfer from a designated pool address.

### MPRD bundle verification (host)
Purpose: verify cryptographic receipts/proofs and bind them to the proposal hash.

This is intentionally host-side (not Tau):
- verify Risc0 receipt / image id allowlist
- verify bundle binds to `proposal_hash`
- output boolean flags consumed by the rules (`proof_ok`, `binding_ok`, `policy_ok`, `nonce_ok`, plus `unique_ok` if the
  claimed-set check is implemented host-side)
