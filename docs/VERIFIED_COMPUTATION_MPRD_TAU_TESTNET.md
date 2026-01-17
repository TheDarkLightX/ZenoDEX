# Verified Computation Plan: ZenoDex + Tau Testnet Alpha + MPRD Receipts

This document answers: **how can a user know a node computed ZenoDex correctly?** It proposes a concrete integration
path that turns “an operator ran some code” into “anyone can verify the transition from public commitments”.

The core idea is the MPRD invariant:

> **Models Propose, Rules Decide, Execution only with a valid receipt.**

## 0) What Tau Testnet Alpha already provides (useful primitives)

Tau Testnet Alpha (`external/tau-testnet`) is a hybrid node:
- Python does networking/storage and “extralogical” work (e.g., signature checks).
- Tau rules are intended to be the arbiter of validity, executed via Docker.
- Tau execution is currently gated by a dev switch (`TAU_FORCE_TEST`), so you must treat “proof of execution” as
  something the protocol should enforce, not something you assume.

The testnet already has commitment plumbing that ZenoDex can reuse:
- Block headers commit to a transaction `merkle_root` and a `state_hash` (`external/tau-testnet/block.py`).
- `state_hash` commits to:
  - the rules bytes,
  - a canonical accounts hash, and
  - optionally a DEX snapshot hash (`external/tau-testnet/poa/state.py`, `external/tau-testnet/chain_state.py`).
- Nodes can publish and fetch snapshots via DHT keys:
  - `tau_state:<state_hash>` → JSON payload containing `rules`, `accounts_hash`, optional `dex_hash`
  - `dex_state:<dex_hash>` → the DEX snapshot JSON (`external/tau-testnet/chain_state.py`).

These commitments let you check *integrity of what was claimed*, but do not, by themselves, prove that the DEX snapshot
is the correct result of applying the transactions under the rules.

## 1) The gap: integrity vs validity

Without additional structure, a block producer could publish a DEX snapshot that is internally well-formed and matches
the committed hashes, but is not the correct result of executing the batch.

There are only three ways out:
1) **Re-execution** (full nodes replay every batch deterministically).
2) **Fraud proofs** (anyone can post a compact counterexample that proves a bad transition).
3) **Validity proofs** (a succinct ZK proof that the transition is valid).

MPRD is designed to supply (2) and (3) patterns, with a fail-closed receipt/journal and optional Risc0 ZK proofs.

## 2) Target property (what users should be able to verify)

For every block that claims a DEX update, an independent verifier should be able to check:
- The block header is valid (PoA signature / header hash / merkle root).
- The committed `state_hash` matches the published rules + accounts snapshot (+ dex hash, if present).
- The committed `dex_hash` matches the published DEX snapshot bytes.
- The DEX update is **valid** under the agreed policy/rules *or* is rejectable by a compact proof.

## 3) Proposed integration: “DEX updates are proof-carrying decisions”

### 3.1 Canonical objects and hashes

Define canonical, content-addressed objects (bytes → hash):
- `rules_bytes`: Tau rules text (already committed via `state_hash`)
- `accounts_snapshot`: balances + sequences (already committed via `accounts_hash`)
- `dex_snapshot_bytes`: canonical JSON (already supported; testnet uses a domain separator + sha256)
- `batch_bytes`: canonical encoding of the DEX-relevant intent set (swap/add/remove/etc.)
- `witness_bytes`: any external-computation witnesses needed for validation (hi/lo limbs, computed outputs, etc.)

Define a **proposal id**:
```text
proposal_hash = H(chain_id || prev_state_hash || batch_hash || witness_hash || dex_hash_after)
```
This binds the decision to the exact before/after commitments and the exact batch/witness.

### 3.2 MPRD decision bundle (receipt / proof)

For each proposal, MPRD produces a *decision bundle*:
- `policy_hash`, `policy_epoch`, `registry_root` (what policy was used, and was it authorized?)
- `nonce` / anti-replay binding
- `proposal_hash` (binds to before/after state + batch + witness)
- allow/deny result + bounded trace
- optionally a **Risc0 receipt** proving the decision and commitments (MPRD “B-Full” style)

This is the object that third parties verify instead of trusting the operator.

### 3.3 What gets committed on-chain / in block data

Minimal, compatible with Tau Testnet Alpha’s existing header:
- Include the decision bundle (or its hash + fetch locator) in the block’s transaction list, so it is committed by the
  header `merkle_root`.
- Keep using the header `state_hash` to commit to rules + accounts + `dex_hash`.
- Publish `dex_state:<dex_hash>` in the DHT (already supported).
- Publish the decision bundle in the DHT under a new key (proposed):
  - `mprd_bundle:<bundle_hash>` → bytes of the bundle (receipt + journal)

This yields a verifiable chain of commitments:
`merkle_root` commits to `bundle_hash`, and `state_hash` commits to `dex_hash`.

## 4) Verification algorithms (what a verifier does)

### 4.1 Full node verifier (no ZK required, but can use it)

Given a new block:
1) Verify the block signature (PoA) and header hash.
2) Verify `merkle_root` matches the tx list, and extract the referenced `bundle_hash`.
3) Fetch `tau_state:<state_hash>` and confirm it matches the header commitment (rules + accounts hash + dex hash).
4) Fetch `dex_state:<dex_hash>` and confirm its hash matches.
5) Fetch `mprd_bundle:<bundle_hash>` and verify:
   - the policy is authorized at `(policy_epoch, registry_root)` (allowlist / manifest verification),
   - the bundle binds to `proposal_hash`,
   - `proposal_hash` binds to `(prev_state_hash, batch_hash, witness_hash, dex_hash_after)`,
   - anti-replay/nonce checks.
6) Either:
   - re-execute the DEX batch deterministically (kernel interpreter / Rust kernel) and confirm the resulting
     `dex_hash_after`, **or**
   - verify the included ZK receipt that attests the validity of the batch transition.

If any step fails, reject the block.

### 4.2 Light client verifier (the reason to use ZK receipts)

A light client cannot replay execution, so it needs succinct verification:
1) Verify PoA header signature and `state_hash`.
2) Fetch the decision bundle and verify the Risc0 receipt against an allowlisted image id (from a signed manifest).
3) Verify the receipt/journal binds to the committed `dex_hash_after` and prior `state_hash` context.
4) Optionally fetch `dex_state:<dex_hash>` and check it matches the committed hash (data availability).

This makes “correctness” checkable without trusting any RPC, beyond data availability.

## 5) What gets proven vs what stays “re-executed”

There are two sensible deployment phases:

### Phase A (fast path): prove *decision and commitment binding*
- ZK proves the gate/policy decision and that the bundle binds to the committed hashes.
- Full nodes still re-execute DEX math to enforce validity.
- Light clients gain strong auditability (“this is the policy that was applied”), but still rely on honest full nodes to
  reject invalid DEX transitions.

### Phase B (strong): prove *DEX transition validity*
- ZK proves that the DEX transition is valid under the published policy and witnesses, and binds to `dex_hash_after`.
- Full nodes verify receipts instead of replaying (optional).
- Light clients can verify validity without replay.

MPRD already contains guest patterns that can execute bounded policy evaluation and selection in-guest; the question is
how much of the DEX step validation to embed in the guest (compiled Tau checks, kernel interpreter, or both).

## 6) Concrete next steps for ZenoDex integration on Tau Testnet Alpha

1) **Fix the “truth object”**: define the canonical DEX snapshot schema and hashing (align with testnet’s
   `dex_state:<sha256>` and domain separation).
2) **Define batch encoding + witness format**: a stable encoding that verifiers can hash and (in Phase B) the guest can
   validate.
3) **Add a bundle carrier**: represent the MPRD decision bundle as a transaction type committed in `merkle_root`.
4) **Make verification fail-closed**: update node acceptance rules so “missing bundle / invalid receipt / mismatched hash”
   rejects the block (this also neutralizes “TAU_FORCE_TEST” bypass paths).
5) **Choose Phase A vs Phase B** and implement incrementally.

## 6.1) Proof mining (bootstrap distribution + verification)
If you want early participation rewards that also harden correctness, use **proof mining**:
reward provers who supply valid MPRD bundles / receipts that bind to the committed before/after state.
See `docs/PROOF_MINING.md`.

## 7) Why this answers “how do I know the computer ran it correctly?”

Because the network accepts a DEX update only if:
- the update is committed to by hashes in the block header, and
- the update is accompanied by a verifiable decision bundle (and eventually a validity proof),

…a dishonest operator cannot convince independent verifiers that an invalid transition is valid. The operator’s compute
becomes an optimization, not a trust assumption.
