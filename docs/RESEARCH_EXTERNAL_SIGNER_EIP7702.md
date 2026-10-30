# Research: external signing, EIP-7702 delegation and withdrawal effect safety

**Date:** 2026-10-30.
**Status:** research-only, not installed as a release gate or wallet adapter.
**Inspected main:** 8436c8403342869519154eecb5eee89fddbd991e.
**Crucible pilot:** private draft TheDarkLightX/Zeno-Crucible PR #47 (maintainer access required).
**Sibling FCIS proposal:** TheDarkLightX/ZenoFCIS draft PR #172.

## Actual ZenoDEX scope (do not imply Ethereum support)

This repository already implements abstract production key-management admission in:

- docs/PRODUCTION_KEY_MANAGEMENT_V0_SPEC.md
- docs/PRODUCTION_KEY_MANAGEMENT_RUNBOOK.md
- src/integration/production_key_management_v0.py
- tools/check_production_key_management_spec.py
- formal/property/production_key_management_v0.json

It also documents self-custody limitations in docs/SEC_CRYPTO_INTERFACE_CONTROLS.md and host-independent settlement obligations in docs/ZENODEX_TRUST_MINIMIZATION_TARGET.md.

The reviewed production action names include treasury spend, DAO grant, signer rotation and emergency controls. They do **not** currently include an explicit EIP-7702 code-delegation action. This PR does **not** assert that ZenoDEX has a live EIP-7702 wallet, Ethereum custody bridge or exploitable signer. First audit real deployed adapter coverage. This is a prospective security model for any future Ethereum EOA/bridge integration, alongside a general test of existing privileged-operation signing containment.

## Two distinct failure classes

**Effect order:** The DAO-style path exposes an external callback before accounting state changes, letting a reentrant call reuse an old entitlement. In an FCIS-style design the pure state transition is only part of the solution; the shell must commit the correct debit before an attacker-controlled callback, or use an independently verified atomic settlement protocol. A controlled failure of the later send must not silently erase or duplicate an obligation.

**Authority bypass:** EIP-7702 permits persistent delegation of an EOA's executable code by a valid signature over chain ID, delegate address and nonce. The authorization can be submitted by a relayer. The authorization-list processing persists even when the outer transaction's execution subsequently reverts. An attacker who can make an unrestricted signing service sign such a tuple can obtain control without learning the private key. Signer integrity and approval semantics therefore matter separately from on-chain signature validity.

Protocol: https://eips.ethereum.org/EIPS/eip-7702 . The reported October 29 Binance intrusion motivates threat modeling but does not prove a ZenoDEX vulnerability or establish the whole intrusion chain.

## Proposed trust diagram

~~~text
User wallet (self-custody) ───────► chain
    | external to ZenoDEX's private-key custody assurances
    |
ZenoDEX privileged action proposal (untrusted service may propose)
    |
    v
Pure packet/policy validation + independently enforced quorum
    |
    v
Nominal admission for one exact action/nonce/chain/payload
    |
    v
Exclusive signer API (HSM/MPC/hardware; structured policy enforcement)
    |
    v
Signature -> chain-specific verifier -> observed on-chain outcome
    |
    +---- reject/unknown/recovery -> no further signing on stale authorization
~~~

**Central requirement:** a valid signer output from the managed custody boundary must imply a policy-approved action. Checking this property in Python alone is insufficient if a lower-level service can call the HSM to sign arbitrary digests.

## Proposed action classification and controls

The existing production_key_management_v0 model is not silently reinterpreted. Before supporting delegated Ethereum accounts, propose an explicit reviewed action taxonomy for:

1. Ethereum EOA delegation install/replace/clear, each treated as a **critical governance-changing operation** (not an ordinary withdrawal or UI click).
2. Managed custody withdrawals, ERC-20 approvals/permits and cross-chain movement, each with independent intent/limit rules.
3. Delegated code upgrade, proxy administration and any ability to change execution behavior, including upgrades that leave the first-level code hash unchanged.
4. Emergency response: pause *local* signing, inventory and revoke delegations on-chain where controllable, rotate signing credentials and reconcile lingering approvals. Pause is not on-chain revocation.

No new action names are added to executable ACTIONS_V0 by this PR.

### Proposed typed packet (research contract, not production ABI)

~~~text
ExternalAuthorizationIntent {
  action_kind, environment, network_id, chain_id,
  account_identity, principal_identity, deployment_instance,
  reviewed_policy_id, nonce, expected_account_state,
  value_bounds, allowed_targets, effect_identity,
  eip7702_delegate_address?, reviewed_behavior_dependencies?,
  expiry_policy?, custodian_quorum_receipt?,
  exact_protocol_signing_preimage
}
~~~

Every field is proposed application policy; **EIP-7702 does not cryptographically sign most of these fields**. The signer must constrain exactly what it emits, and reviewers must not equate a local receipt with enforceable Ethereum authority. Prefer contract-account custody with independently enforced on-chain quorum if the system cannot control a single EOA signing path.

### P0 research invariants and adversarial probes

| ID | Desired property | Required negative probe |
| --- | --- | --- |
| ZD-AUTH-01 | Every managed-custody signature was authorized by a policy enforced at the actual signer. | Compromised upstream submits a syntactically valid but forbidden 7702 delegation. |
| ZD-AUTH-02 | Raw arbitrary-digest signing cannot bypass production packet admission. | Alternate RPC, debug/test API, or MPC path signs unaudited bytes. |
| ZD-AUTH-03 | Delegation is separately privileged and deny-by-default pending reviewed support. | Reclassify 7702 tuple as a routine transfer or wallet connect. |
| ZD-AUTH-04 | Managed custody rejects unintended chain ID 0, cross-chain replay, mismatched account and stale nonce. | Relay a signature to another network or at another nonce. |
| ZD-AUTH-05 | The reviewed delegate implementation, proxy/storage dependency graph and upgrade owner are explicitly controlled. | Upgrade behind constant outer code hash; changed delegate before execution. |
| ZD-AUTH-06 | Authorization cannot be inferred solely from ECDSA validity or an upstream "approved" Boolean. | Rehash forged receipt, change principal, bypass quorum. |
| ZD-AUTH-07 | Reverted outer EIP-7702 execution prompts **on-chain delegation state reconciliation**, not assumed rollback. | Failed transaction followed by an accepted delegated call. |
| ZD-AUTH-08 | Compromise recovery includes outstanding signed authorizations and new deposits to a delegated address. | Pause locally but leave old signed tuple/delegation live. |
| ZD-AUTH-09 | Withdrawal/settlement preserves entitlement and asset conservation across callbacks, retries and unknown outcomes. | DAO-like send-before-debit nested withdrawal and lost reply. |
| ZD-AUTH-10 | Self-custodial user-key risks remain separate from protocol-owned treasury controls. | User submits own unrestricted 7702 signature; app falsely claims ability to prevent it. |
| ZD-AUTH-11 | Concurrent nonce changes, policy rotations and signer restarts cannot silently broaden authorization. | Nonce bundle, re-ordered requests, delayed signatures, stale policy. |
| ZD-AUTH-12 | Independent receipts and implementation-refinement evidence are mandatory before security claims or launch. | Forge a Crucible result and attempt to bypass a real handler. |

For **compromised upstream service** the goal is signature refusal at the unbypassable signer. For **compromised original EOA key**, no off-chain ZenoDEX policy can prevent that holder from issuing valid EIP-7702 authorizations. Keep these two cases separate; the latter may demand contract custody, key rotation, migration or explicit residual-risk acceptance.

## Research procedure and adoption gates

The reproducible Crucible pilot in PR #47 checks 96 bounded combinations of nonce, chain ID, delegate, code identity, signer mode and revert status, plus a DAO-style one-unit withdrawal ordering toy. It shows how a policy-gated signer and raw signing bypass differ. This is **not** a test of actual ZenoDEX modules.

Next steps, in dependency order:

1. Inventory all real ZenoDEX value-moving and privileged-signature paths, including API, UI, worker, external wallet and deployment profiles. Report "not implemented" where appropriate, not "safe".
2. Human-review an actual proposed EIP-7702 policy or explicitly forbid all such authorizations in production. Define control boundaries for platform keys versus users' independent wallets.
3. Extend Crucible with independent oracles, finite-state/adversarial schedule search, repeated nonces, failed outer transactions, changes behind proxies and deliberately corrupted signer adapters.
4. Exercise src/integration/production_key_management_v0.py and the real signer integration against the new profile; qualify the actual raw-signature surface. Maintain existing distinct-custodian, timelock, hardware/MPC and transparency policies.
5. Test full live chain-specific transaction encoding against official EIP-7702 vectors and real Ethereum clients in an isolated network; do not infer protocol conformance from the pilot.
6. Check cancellation, refund, unknown outcomes and reentrancy at the exact shell/economic settlement boundary.
7. Record source pins, independent counterexamples, negative memory, human meaning signoff and precise nonclaims. Only a separate reviewed implementation PR may add a runtime gate.

The machine-readable **advisory** packet is formal/property/authority_delegation_research_v0.json. It is *not* imported by the production key-management property checker.

## Explicit nonclaims

- No live EIP-7702 surface in ZenoDEX was proven by this research review.
- An immutable pure core does not protect against signatures created outside its guarded execution path.
- HSM/MPC storage-class metadata does not independently prove the signer enforces the policy.
- EIP-7702 authorizations do not bind an arbitrary expiration, application policy receipt or delegate code hash.
- A reviewed code hash at signing time does not constrain proxy-selected implementation later.
- A test pass in Crucible is neither a deployment certificate nor a proof of key security.

**No change to execution, settlement, custody, UI authorization or release gates in this PR.**
