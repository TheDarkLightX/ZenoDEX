# Production Key Management Runbook

This runbook describes the operator ceremony for production ZenoDEX and
ZenoLedger privileged actions. It records public identifiers, evidence hashes,
approval receipts, and transparency log roots. It must never record private
keys, wallet exports, recovery shares, hardware unlock material, or mnemonic
words.

## Scope

The production key-management system protects privileged actions that can affect
network configuration, validator sets, verifier registries, oracle reporter
registries, release artifacts, treasury movement, and emergency controls.

Runtime admission is handled by:

```text
src/integration/production_key_management_v0.py
src/integration/zeno_ledger_production_key_gates_v0.py
tools/check_production_key_management_config.py
```

The operational rule is:

```text
production_sensitive_action -> accepted production key-management receipt
```

Each accepted receipt must bind the action packet hash, policy hash, accepted
key IDs, accepted custodian IDs, threshold, timelock status when required, and
transparency log hash when required.

## Key Ceremony

Run the ceremony offline or on a dedicated ceremony machine with screen
recording disabled and network access limited to public documentation lookup.
Record only public outputs.

1. Open a ceremony ticket with the action scope, target environment, required
   roles, expected custodians, and planned transparency log destination.
2. Confirm that all participants understand that private signing material and
   recovery shares are never pasted into chat, tickets, repository files, build
   logs, or test fixtures.
3. Generate or register public keys using the approved hardware wallet, HSM, or
   MPC/TSS signing backend.
4. Record each public key descriptor with:
   - `key_id`
   - public key or account address
   - role
   - storage class
   - custodian ID
   - creation time
   - activation time
   - expiry time
   - status
   - non-secret custody policy hash when applicable
5. Build the production key-management config.
6. Run:

```bash
python3 tools/check_production_key_management_config.py \
  --config <config-json> \
  --policy-model formal/property/production_key_management_v0.json
```

7. Publish the config hash, signer inventory hash, and ceremony record hash to
   the transparency log.
8. Store the signed ceremony record in the release evidence archive.

## Signer Inventory

The signer inventory is a public-control document. It lists who can approve
which class of action without exposing signing material.

Required fields per signer:

```text
key_id
role
custodian_id
environment
storage_class
public_key_or_address
status
valid_from
valid_until
revocation_log_position
custody_policy_hash
```

Allowed production storage classes are hardware wallet, HSM, and MPC/TSS for
actions that require non-software custody. Software signing keys are limited to
local-demo and public-testnet scopes unless a future policy explicitly allows a
lower-risk action class.

## Role Assignment

Assign signers to the narrowest role that can perform their duty.

| Role | Scope |
| --- | --- |
| `treasury` | Protocol treasury spend and DAO treasury grant packets. |
| `config` | Public network config update and emergency unpause packets. |
| `validator` | Validator set update packets. |
| `verifier` | Verifier registry update packets. |
| `oracle` | Oracle reporter registry update packets. |
| `release` | Release artifact publish packets. |
| `emergency` | Emergency pause packets only. |

Emergency keys are scoped to pause. Unpause uses the `config` role.

## Hardware Wallet And HSM Storage

Hardware wallet and HSM custodians must keep signing material outside the repo
and outside ordinary server filesystems.

Operational requirements:

- register only public keys or account addresses in config;
- record the device or HSM policy hash, never the unlock material;
- require a human confirmation screen for high-value actions when the device
  supports it;
- keep firmware and vendor policy evidence in the ceremony archive;
- rotate keys when a custodian leaves, a device is lost, or the HSM policy
  changes;
- revoke the old key before relying on a replacement quorum.

The runtime checker treats hardware and HSM custody as non-software custody
metadata. Vendor correctness remains external evidence.

## MPC/TSS Custody Procedure

MPC/TSS is a live signing custody class when it exposes one ordinary public key
or account address and produces verifiable signatures over the canonical packet
hash.

Required public metadata:

```text
mpc_policy_hash
participant_count
threshold
participant_custodian_ids
rotation_policy_hash
recovery_policy_hash
signing_transcript_hash
```

The MPC/TSS backend must not bypass role quorum, distinct custodian quorum,
timelock, action scope, environment separation, or transparency publication.
The final signature is still verified as a normal signature over the packet
hash.

## Shamir Secret Sharing Backup And Recovery Ceremony

Shamir Secret Sharing is a backup and recovery mechanism. It is recovery
metadata only and cannot appear as a counted live signer.

Ceremony requirements:

1. Generate shares offline under the custodian-approved recovery policy.
2. Store shares with separate custodians and separate physical or institutional
   controls.
3. Record only the recovery policy hash, threshold, share custodian IDs, and
   sealed-evidence hashes.
4. Run a recovery drill on test material before production activation.
5. If recovery reconstructs a signing key, treat the reconstructed key as
   compromised after use and rotate to a newly generated production key.

The config checker rejects recovery-only Shamir entries as active signers.

## Backup And Recovery

Maintain three backup classes:

- public config backup: signer registry, policy model, revocation log, action
  policies, transparency log references;
- custody evidence backup: non-secret hardware, HSM, and MPC policy hashes;
- recovery metadata backup: Shamir recovery policy hash and sealed-evidence
  hashes.

Backup review cadence:

```text
monthly public config restore test
quarterly signer inventory reconciliation
quarterly recovery metadata availability check
annual full testnet recovery drill
```

Production recovery must create a new action packet and a new production
key-management admission receipt. Recovery status alone never authorizes a
privileged action.

## Rotation Cadence

Default rotation cadence:

```text
release keys: every major release or 180 days
treasury keys: every 180 days
config keys: every 180 days
validator keys: every validator-set epoch or 180 days
verifier keys: every verifier-registry epoch or 180 days
oracle keys: every reporter-registry epoch or 180 days
emergency keys: every 90 days
```

Rotate immediately after custodian departure, custody device loss, suspected
exposure, MPC participant change, HSM policy change, or failed revocation drill.

Before applying rotation, run the config checker and confirm that every affected
role keeps at least one future valid quorum.

## Revocation Drill

Run a revocation drill at least quarterly.

1. Select a testnet key or a production key scheduled for replacement.
2. Add the key to the revocation log.
3. Confirm that the key cannot be active.
4. Confirm that revoked key IDs remain in revocation history.
5. Confirm that all affected actions still have a valid future quorum.
6. Publish the revocation log hash.
7. Archive the checker output and transparency log reference.

Command:

```bash
python3 tools/check_production_key_management_config.py \
  --config <rotated-config-json> \
  --policy-model formal/property/production_key_management_v0.json
```

## Emergency Pause Drill

Emergency pause is the only production action that emergency keys may approve.

Drill steps:

1. Build an `emergency_pause` packet against a testnet or rehearsal environment.
2. Collect signatures from the required emergency custodians.
3. Build the admission receipt.
4. Verify the receipt with the runtime admission library.
5. Publish the drill receipt hash to the rehearsal transparency log.
6. Confirm that the same emergency key set cannot authorize `emergency_unpause`
   or treasury movement.

The expected result is that pause is accepted when policy is satisfied, while
unpause routes through the `config` role.

## Unpause Governance

Unpause requires the `config` role and follows the ordinary transparency and
timelock requirements for configuration actions.

Required evidence:

- incident summary hash;
- remediation plan hash;
- affected range or release hash;
- config-role admission receipt;
- transparency log hash;
- post-unpause monitoring plan hash.

An emergency pause receipt is evidence of the pause action only.

## Transparency Log Publication

Publish a transparency log entry for every high-value production action that
requires publication under the action policy.

The log entry should include:

```text
action
environment
packet_hash
policy_hash
receipt_hash
accepted_key_ids
accepted_custodian_ids
timelock_evidence_hash
config_hash
release_or_registry_hash
timestamp
```

The log must record public hashes and public identifiers only.

## Incident Response

Use this decision tree:

```text
suspected key exposure
  -> revoke key
  -> rotate affected role
  -> run config checker
  -> publish revocation log hash
  -> assess impacted action receipts

lost hardware device
  -> revoke device key
  -> rotate role if quorum margin is reduced
  -> update signer inventory
  -> archive custody incident hash

MPC/TSS participant failure
  -> disable participant
  -> rotate MPC policy if threshold or participant set changed
  -> publish new MPC policy hash
  -> run config checker

unauthorized privileged action attempt
  -> preserve packet and signature evidence
  -> verify rejection reason
  -> check transparency log for conflicting entries
  -> rotate keys if signer behavior is suspicious

active protocol risk
  -> use emergency pause when policy is satisfied
  -> investigate under incident ticket
  -> unpause only through config-role governance
```

Incident artifacts should be hash-addressed and stored in the release evidence
archive. Do not attach private signing material or recovery shares.

## Testnet Versus Production Separation

Testnet and production keys must remain separate.

Rules:

- production packets reject testnet keys;
- testnet keys use testnet environment labels;
- production keys must not sign public-testnet rehearsal packets;
- testnet evidence may demonstrate procedures, but production activation
  requires production-role descriptors and production-environment receipts;
- local-demo keys must never appear in production config.

The separation property is checked by the runtime admission library, config
checker, property model, and Lean proof surface.

## Evidence Checklist

Before claiming production key-management readiness, archive:

- property checker output;
- ESSO or equivalent finite-model output;
- Lean receipt;
- runtime admission test output;
- config checker output;
- ZenoLedger production gate test output;
- release gate output;
- signer inventory hash;
- revocation log hash;
- transparency log root;
- this runbook hash.
