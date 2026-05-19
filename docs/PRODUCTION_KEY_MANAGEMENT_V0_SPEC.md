# Production Key Management V0 Spec

Status: specification, bounded property checker, and abstract Lean proof surface.

This document turns production key management into implementable work for
ZenoDEX and ZenoLedger. It is intentionally scoped to admission policy and
operator evidence. It does not store private keys, choose a wallet vendor, or
claim legal custody closure.

## Goal

Production key management must ensure:

```text
AdmittedPrivilegedAction
  -> role_authorized
  -> threshold_quorum
  -> distinct_custodian_quorum
  -> no_revoked_or_expired_signers
  -> production_keys_only
  -> transparency_receipt_bound
```

Privileged production actions are accepted only when the correct role-specific
quorum signs a bounded, hash-stable action packet. No single private key or
single custodian can move treasury funds, alter production network authority,
change oracle/verifier authority, rotate signers, or unpause the system.

## Current Artifacts

- Property model: `formal/property/production_key_management_v0.json`
- Deterministic bounded checker: `tools/check_production_key_management_spec.py`
- Test wrapper: `tests/test_production_key_management_spec.py`
- ESSO-ready spec surface: `formal/esso/production_key_management_v0.esso.yaml`
- Lean proof surface: `lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean`
- Proof receipt: `lean-mathlib/proof_receipts/zeno_ledger_production_key_management_v0.md`

ESSO is not installed in this runner. The ESSO file is therefore an auditable
handoff artifact. The executable local evidence is the deterministic property
checker and the Lean file.

## Scope

Included:

- signer roles and action classes;
- production/testnet key separation;
- threshold and distinct-custodian quorum;
- revoked and expired key rejection;
- hardware, HSM, or MPC-backed signing requirement for high-value actions;
- Shamir Secret Sharing backup and recovery ceremony requirements;
- timelock requirement for governance-changing actions;
- break-glass scope restriction;
- transparency receipts;
- deterministic property tests;
- abstract proof of the admission shape.

Excluded:

- cryptographic signature soundness;
- HSM, hardware wallet, MPC, or vendor correctness;
- Shamir share-generation or share-reconstruction correctness;
- legal custody analysis;
- social identity verification;
- user wallet security;
- exchange listing custody requirements;
- chain-specific Tau Net wallet UX.

## Roles

| Role | Purpose | Must Authorize |
|---|---|---|
| `treasury` | protocol funds, DAO grants, reserves | treasury spends and grants |
| `config` | production network config and signer policy | network configs, unpause, key rotation, revocation |
| `validator` | validator set and operational consensus authority | validator-set updates, routine heartbeat |
| `oracle` | oracle reporter/source registry | oracle reporter registry updates |
| `verifier` | verifier/proof registry | verifier registry updates |
| `release` | release artifacts and deployment evidence | production release publishing |
| `emergency` | fast pause only | emergency pause |

Role separation is mandatory. A signer may hold more than one real-world role
only if the production governance process explicitly records the overlap and the
distinct-custodian invariant still holds for every action.

## Action Policies

The canonical v0 policies live in:

```text
formal/property/production_key_management_v0.json
```

Important defaults:

| Action | Role | Threshold | Distinct Custodians | Non-Software Custody | Timelock |
|---|---:|---:|---:|---:|---:|
| `protocol_treasury_spend` | `treasury` | 3 | 3 | yes | yes |
| `dao_treasury_grant` | `treasury` | 3 | 3 | yes | yes |
| `public_network_config_update` | `config` | 2 | 2 | yes | yes |
| `validator_set_update` | `validator` | 2 | 2 | yes | yes |
| `oracle_reporter_registry_update` | `oracle` | 2 | 2 | yes | yes |
| `verifier_registry_update` | `verifier` | 2 | 2 | yes | yes |
| `release_artifact_publish` | `release` | 2 | 2 | yes | no |
| `emergency_pause` | `emergency` | 2 | 2 | yes | no |
| `emergency_unpause` | `config` | 3 | 3 | yes | yes |
| `key_revocation` | `config` | 2 | 2 | yes | no |
| `signer_rotation` | `config` | 3 | 3 | yes | yes |
| `routine_node_heartbeat` | `validator` | 1 | 1 | no | no |

Emergency unpause is intentionally harder than pause. Pause is allowed to be
fast. Unpause restores live risk and must go through normal governance.

## Custody Models

V0 permits three production custody patterns for counted high-value signatures:

```text
hardware wallet
hsm
mpc
```

`software` keys remain valid only for noncritical actions whose policy does not
require non-software custody.

Shamir Secret Sharing is a backup and recovery mechanism in this specification.
It can split recovery material across custodians, support disaster recovery, and
reduce single-person loss risk. It must not be counted as a live production
signature by itself. A reconstructed key is usable only after a recorded recovery
ceremony, signer rotation, and key descriptor update.

MPC/TSS can be a live signing backend. It is modeled as `storage_class = mpc`
when the MPC signer emits one public key or account address and produces
signatures over the canonical packet hash. The admission layer still sees a
normal public key, signature envelope, role, environment, custodian ID, and
receipt.

The security rule is:

```text
MPC_or_SSS_used -> public_admission_policy_still_applies
```

MPC and Shamir improve custody. They do not weaken role quorum, distinct
custodian quorum, revocation, timelock, transparency, or break-glass scope.

## Data Contracts

Future runtime work should implement these JSON-like objects with canonical
hashing using the repo's shared canonical encoder.

### `KeyDescriptorV0`

Required fields:

- `schema`: `zenodex.production_key_management.key_descriptor.v0`
- `key_id`: stable public identifier, never a private key
- `public_key`: canonical public key or account address
- `role`: one of the v0 roles
- `environment`: `testnet` or `production`
- `status`: `active`, `revoked`, or `expired`
- `storage_class`: `software`, `hardware`, `hsm`, or `mpc`
- `custodian_id`: stable non-secret custodian identifier
- `custody_model`: optional descriptive value such as `hardware_wallet`,
  `cloud_hsm`, `on_prem_hsm`, `mpc_tss`, or `sss_recovery_only`
- `recovery_policy_hash`: optional hash of the recovery ceremony policy
- `valid_from_epoch`
- `valid_until_epoch`
- `key_descriptor_hash`

Private key material is never represented in this object.

### `ActionPolicyV0`

Required fields:

- `schema`: `zenodex.production_key_management.action_policy.v0`
- `action`
- `role`
- `critical`
- `threshold`
- `min_distinct_custodians`
- `hardware_required`
- `timelock_required`
- `break_glass_allowed`
- `transparency_required`
- `policy_hash`

### `PrivilegedActionPacketV0`

Required fields:

- `schema`: `zenodex.production_key_management.privileged_action_packet.v0`
- `environment`
- `action`
- `target_kind`
- `target_hash`
- `policy_hash`
- `nonce`
- `epoch`
- `not_before_epoch`
- `expires_at_epoch`
- `payload_hash`
- `packet_hash`

The action packet is what signers sign. Runtime code must reject signatures over
anything except the canonical packet hash.

### `SignatureEnvelopeV0`

Required fields:

- `schema`: `zenodex.production_key_management.signature_envelope.v0`
- `key_id`
- `public_key`
- `packet_hash`
- `signature_scheme`
- `signature`
- `signature_envelope_hash`

### `AdmissionReceiptV0`

Required fields:

- `schema`: `zenodex.production_key_management.admission_receipt.v0`
- `ok`
- `status`
- `environment`
- `action`
- `packet_hash`
- `policy_hash`
- `accepted_key_ids`
- `accepted_custodian_ids`
- `accepted_signature_count`
- `threshold`
- `distinct_custodian_count`
- `min_distinct_custodians`
- `timelock_satisfied`
- `hardware_requirement_met`
- `transparency_log_hash`
- `receipt_hash`

Every production privileged action must emit this receipt before the action is
applied.

## Admission Predicate

```text
Admit(action, packet, policy, keys, signatures) :=
  packet.environment = production
  and packet.action = policy.action
  and packet.policy_hash = hash(policy)
  and packet_hash_valid(packet)
  and signatures_bind_packet(signatures, packet.packet_hash)
  and all_counted_keys_are_active(keys)
  and all_counted_keys_are_production(keys)
  and all_counted_keys_have_policy_role(keys, policy.role)
  and count(distinct accepted signatures) >= policy.threshold
  and count(distinct accepted custodian_id) >= policy.min_distinct_custodians
  and (not policy.hardware_required or all_counted_keys_non_software_custody(keys))
  and (not policy.timelock_required or packet.epoch >= packet.not_before_epoch)
  and (not break_glass_used(keys) or action = emergency_pause)
  and (not policy.transparency_required or transparency_receipt_bound)
```

This predicate is the implementation target for `src/integration/production_key_management_v0.py`.

## Mathematical Contract

Let:

```text
K = finite set of key descriptors
S = finite set of signature envelopes
P = action policy
A = privileged action packet
counted(K, S, A) = keys in K with a valid signature in S over A.packet_hash
```

The v0 runtime admission function must implement:

```text
Accept(A, P, K, S) <->
  PacketOK(A, P)
  and SignaturesBind(A, K, S)
  and RoleOK(P, counted(K, S, A))
  and EnvironmentOK(A, counted(K, S, A))
  and StatusOK(counted(K, S, A))
  and QuorumOK(P, counted(K, S, A))
  and StorageOK(P, counted(K, S, A))
  and TimelockOK(A, P)
  and BreakGlassOK(A, counted(K, S, A))
  and TransparencyOK(P, A)
```

Where:

```text
PacketOK(A, P) :=
  A.action = P.action
  and A.policy_hash = hash(P)
  and A.packet_hash = hash(canonical(A without packet_hash))
  and A.not_before_epoch <= A.expires_at_epoch
  and A.epoch <= A.expires_at_epoch

RoleOK(P, C) :=
  forall k in C, k.role = P.role

EnvironmentOK(A, C) :=
  A.environment = production -> forall k in C, k.environment = production

StatusOK(C) :=
  forall k in C, k.status = active

QuorumOK(P, C) :=
  count(distinct key_id in C) >= P.threshold
  and count(distinct custodian_id in C) >= P.min_distinct_custodians

StorageOK(P, C) :=
  P.hardware_required = false
  or forall k in C, k.storage_class in {hardware, hsm, mpc}

TimelockOK(A, P) :=
  P.timelock_required = false
  or A.epoch >= A.not_before_epoch

BreakGlassOK(A, C) :=
  (exists k in C, k.break_glass = true) -> A.action = emergency_pause

TransparencyOK(P, A) :=
  P.transparency_required = false
  or A.transparency_log_hash is nonempty and bound into the receipt hash
```

The implementation must count a key at most once. If two signature envelopes
claim the same `key_id`, the action is malformed and must be rejected before
quorum counting. If two keys share one `custodian_id`, they may contribute at
most one unit toward the distinct-custodian threshold.

## Theorem Ladder

The current Lean file proves the abstract boolean safety shape. Runtime work
should preserve these theorem names as the stable public proof surface and add
finite-role refinements under them.

Base theorem:

```text
Admitted(a) -> Safe(a)
```

Key corollaries:

```text
Admitted(a) -> quorumMet(a)
Admitted(a) -> thresholdAtLeastTwoForCritical(a) and distinctCustodiansMet(a)
Admitted(a) -> noRevokedSigner(a)
Admitted(a) -> noExpiredSigner(a)
Admitted(a) -> productionKeysOnly(a)
Admitted(a) -> transparencyReceiptBound(a)
```

Rejection theorems:

```text
productionEnvironment(a) = false -> not Admitted(a)
quorumMet(a) = false -> not Admitted(a)
thresholdAtLeastTwoForCritical(a) = false -> not Admitted(a)
distinctCustodiansMet(a) = false -> not Admitted(a)
noRevokedSigner(a) = false -> not Admitted(a)
noExpiredSigner(a) = false -> not Admitted(a)
hardwareBackedIfRequired(a) = false -> not Admitted(a)
timelockSatisfiedIfRequired(a) = false -> not Admitted(a)
breakGlassScopeOk(a) = false -> not Admitted(a)
productionKeysOnly(a) = false -> not Admitted(a)
transparencyReceiptBound(a) = false -> not Admitted(a)
```

The next proof layer should replace booleans with finite `Role`, `Action`,
`Environment`, `KeyStatus`, and `StorageClass` types. It should prove that each
row in `formal/property/production_key_management_v0.json` maps into the same
abstract safety obligations.

## Property Test Work

The first executable artifact is:

```bash
python3 tools/check_production_key_management_spec.py
pytest -q tests/test_production_key_management_spec.py
```

The checker enumerates every v0 action policy and asserts:

- valid quorum accepts;
- single key is rejected for critical actions;
- same-custodian quorum is rejected for critical actions;
- revoked key is rejected;
- expired key is rejected;
- testnet keys are rejected for production actions;
- wrong role is rejected;
- MPC keys are accepted as non-software custody when the action otherwise has a
  valid quorum;
- software keys are rejected when non-software custody is required;
- missing timelock is rejected when timelock is required;
- missing transparency receipt is rejected when transparency is required;
- break-glass keys authorize only `emergency_pause`.

Agents may add cases, but they must not weaken any existing action policy unless
the spec document is explicitly revised in the same change.

## ESSO Work

ESSO spec file:

```text
formal/esso/production_key_management_v0.esso.yaml
```

Required ESSO commands once ESSO is available:

```bash
python3 -m ESSO validate formal/esso/production_key_management_v0.esso.yaml
python3 -m ESSO guide --input formal/esso/production_key_management_v0.esso.yaml --goal verify --profile ci
python3 -m ESSO verify --input formal/esso/production_key_management_v0.esso.yaml --output runs/esso/production_key_management_v0
```

Fail closed on missing ESSO, timeout, solver `unknown`, invalid IR, or any
invariant failure. Do not introduce unbounded integers, strings, network calls,
wall-clock time, or random values.

## Lean Proof Work

Current proof file:

```text
lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
```

Checked surface:

```bash
/home/trevormoc/.elan/toolchains/leanprover--lean4---v4.27.0/bin/lean \
  lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
rg -n -w "sorry|admit|axiom" \
  lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
```

The proof establishes:

- admitted production actions imply quorum;
- admitted production actions imply no single-key authority;
- revoked signers are rejected;
- expired signers are rejected;
- missing non-software custody evidence is rejected when required;
- missing timelock is rejected when required;
- break-glass scope violations are rejected;
- testnet keys are rejected for production;
- missing transparency receipts are rejected.

Future Lean work should refine the boolean abstraction into finite role/action
types, then connect the property-model action table to the proof surface. A
later runtime theorem can model `storage_class = mpc` as satisfying
non-software custody only after ordinary public-key signature verification over
the canonical packet hash.

## Runtime Integration Targets

The implementation should be layered:

1. Pure admission library:
   `src/integration/production_key_management_v0.py`
2. Config checker:
   `tools/check_production_key_management_config.py`
3. ZenoLedger config gate:
   public network config updates require `config` role admission.
4. Treasury/DAO gate:
   protocol spends require `treasury` role admission.
5. Oracle/verifier registry gates:
   reporter/verifier set updates require the matching role admission.
6. Release gate:
   production release claims require `release` role admission.
7. Emergency gate:
   emergency keys can pause only; unpause routes through `config` role.

No implementation task may introduce private-key storage in the repo, Docker
image, local config examples, or generated artifacts.

## Production Runbook Requirements

The operational runbook must specify:

- key ceremony steps;
- signer inventory;
- role assignment;
- hardware wallet/HSM custody procedure;
- backup and recovery procedure;
- rotation cadence;
- revocation drill;
- emergency pause drill;
- unpause governance procedure;
- transparency log publication;
- incident response decision tree;
- separation between testnet and production signers.

The runbook should record evidence hashes and public keys, never seed phrases or
private keys.

## Done Criteria

The production key-management work is not done until all are true:

```text
property_checker_green
and ESSO_or_equivalent_finite_model_green
and Lean_receipt_green
and runtime_admission_library_green
and privileged_action_gates_wired
and release_gate_checks_key_management
and operator_runbook_exists
and no_private_key_material_in_repo
```

The current commit is expected to close the first proof/spec layer. Runtime
admission and operator procedures remain separate implementation tasks.
