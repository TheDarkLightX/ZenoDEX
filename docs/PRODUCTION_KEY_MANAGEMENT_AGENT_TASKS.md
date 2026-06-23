# Production Key Management Agent Tasks

These task packets are written for lower-cost implementation agents. Keep edits
small, run the listed commands, and do not broaden scope without an explicit
follow-up task.

## Global Rules

- Do not commit private keys, mnemonics, `.env` files, wallet exports, HSM
  credentials, or generated secrets.
- Do not add a dependency unless the task explicitly requires it.
- Use the repo's canonical JSON/hash helpers instead of ad hoc serialization.
- Fail closed on missing fields, unknown roles, unsupported signature schemes,
  expired keys, revoked keys, duplicate signers, duplicate custodians, or
  malformed policies.
- Treat Shamir Secret Sharing as backup/recovery evidence. It must not become a
  live quorum shortcut.
- Treat MPC/TSS as a live signing custody class only when it exposes an ordinary
  public key and verified signature over the canonical packet hash.
- Keep `formal/property/production_key_management_v0.json`,
  `formal/esso/production_key_management_v0.esso.yaml`, the runtime policy table,
  and the docs aligned.
- Never weaken a threshold, custodian count, non-software custody requirement,
  timelock requirement, or transparency requirement without updating the spec
  and tests in the same change.

## Shared Mathematical Contract

All implementation tasks must preserve this predicate:

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

Agents should treat each conjunct as a separate failure axis. A negative test
should flip exactly one axis when practical. If a negative fixture flips several
axes, the test must state which axis is the intended primary rejection reason.

The counted key set is:

```text
counted(K, S, A) :=
  { k in K | exists s in S,
      s.key_id = k.key_id
      and s.packet_hash = A.packet_hash
      and signature_valid(k.public_key, A.packet_hash, s.signature) }
```

V0 tests may use deterministic test signatures. Production-facing code must keep
the signature verification hook explicit and fail closed when the scheme is
unsupported. Duplicate `key_id` or duplicate counted signature envelopes are
malformed input and must be rejected before quorum counting.

## Required Agent Output Format

Every agent should end its work with:

```text
Changed files:
- path

Commands run:
- command: pass/fail

Remaining gaps:
- concise item or "none"

Policy changes:
- "none" unless thresholds, roles, or action policies changed
```

If a command is skipped, the agent must say why. A missing ESSO binary counts as
skipped local execution and must remain an open verification item.

## Task 1: Property Checker Extension

Owner scope:

- `tools/check_production_key_management_spec.py`
- `tests/test_production_key_management_spec.py`
- optional: `formal/property/production_key_management_v0.json`

Goal:

Strengthen the bounded checker into a counterexample-producing specification
gate.

Required changes:

- Add a `reject_reason` string to every negative case.
- Add one positive and one negative case per invariant ID `PKM-G-001` through
  `PKM-G-007`.
- Add a `--json-out <path>` option that writes the result object.
- Add a `counterexamples` array for failed cases. It must include action, policy,
  signer summaries, and failed invariant ID.
- Add `primary_axis` to every case, using one of:
  `packet`, `signature_binding`, `role`, `environment`, `status`, `quorum`,
  `storage`, `timelock`, `break_glass`, or `transparency`.
- Preserve deterministic ordering.

Acceptance commands:

```bash
python3 -m py_compile tools/check_production_key_management_spec.py tests/test_production_key_management_spec.py
python3 tools/check_production_key_management_spec.py
pytest -q tests/test_production_key_management_spec.py
git diff --check
```

Definition of done:

- Checker returns `ok: true`.
- Test asserts every invariant ID appears in at least one case.
- Test asserts every `primary_axis` appears in at least one negative case.
- No private key material appears in fixtures.

## Task 2: Runtime Admission Library

Owner scope:

- `src/integration/production_key_management_v0.py`
- `tests/integration/test_production_key_management_v0.py`

Goal:

Implement the pure runtime admission predicate described in
`docs/PRODUCTION_KEY_MANAGEMENT_V0_SPEC.md`.

Required APIs:

```python
build_key_descriptor_v0(...)
validate_key_descriptor_v0(descriptor)
build_action_policy_v0(...)
validate_action_policy_v0(policy)
build_privileged_action_packet_v0(...)
validate_privileged_action_packet_v0(packet)
build_signature_envelope_v0(...)
build_admission_receipt_v0(packet, policy, key_descriptors, signature_envelopes, *, transparency_log_hash)
validate_admission_receipt_v0(...)
```

Required behavior:

- Reject unknown roles and actions.
- Reject policy/action mismatch.
- Reject packet hash mismatch.
- Reject policy hash mismatch.
- Reject duplicate `key_id`.
- Reject duplicate counted signer public keys.
- Reject duplicate signature envelope for the same `key_id`.
- Reject signature envelopes that bind to a different packet hash.
- Reject duplicate custodian quorum when `min_distinct_custodians` is unmet.
- Reject revoked and expired keys.
- Reject testnet keys for production action packets.
- Reject wrong-role keys.
- Reject software keys when non-software custody is required.
- Accept `storage_class = mpc` for non-software custody only after the normal
  signature verification hook succeeds.
- Reject missing timelock for timelocked actions.
- Reject break-glass signatures for every action except `emergency_pause`.
- Reject missing transparency log hash when policy requires it.
- Bind every receipt to packet hash, policy hash, accepted key IDs, accepted
  custodian IDs, threshold, and receipt hash.
- Return a structured `AdmissionReceiptV0` for both accepted and rejected
  actions. Rejected receipts must contain `ok: false`, `status`, and a stable
  `reject_reason`.

Acceptance commands:

```bash
python3 -m py_compile src/integration/production_key_management_v0.py tests/integration/test_production_key_management_v0.py
pytest -q tests/integration/test_production_key_management_v0.py
python3 tools/check_production_key_management_spec.py
git diff --check
```

Definition of done:

- Tests cover every action policy in the property model.
- Tests cover every `primary_axis` from Task 1.
- Receipt tampering tests fail closed.
- No signing private key helper is introduced.

## Task 3: Config Checker CLI

Owner scope:

- `tools/check_production_key_management_config.py`
- `tests/test_check_production_key_management_config.py`
- optional examples under `docs/examples/`, without secrets

Goal:

Validate a production key-management config file before deployment.

Required CLI:

```bash
python3 tools/check_production_key_management_config.py \
  --config <path> \
  --policy-model formal/property/production_key_management_v0.json
```

Required checks:

- Config schema and hash match.
- Every action has a policy.
- Every policy matches or strengthens the v0 default.
- Every production role has enough active production keys to satisfy threshold.
- Every critical action has at least two distinct custodians.
- No production key uses `software` storage when any assigned action requires
  non-software custody.
- `mpc` custody entries include a non-secret policy hash describing threshold,
  participants, rotation, and recovery process.
- Shamir recovery policies are present only as recovery metadata and cannot
  appear as counted live signers.
- Revoked keys remain present in the revocation log and cannot be active.
- Testnet keys cannot appear in production role quorum sets.
- Emergency keys are scoped to pause only.
- The config cannot delete revoked key IDs from the revocation history.
- Every signer rotation preserves at least one valid future quorum after the
  rotation is applied.

Acceptance commands:

```bash
python3 -m py_compile tools/check_production_key_management_config.py tests/test_check_production_key_management_config.py
pytest -q tests/test_check_production_key_management_config.py
python3 tools/check_production_key_management_config.py --help
git diff --check
```

Definition of done:

- CLI emits `schema`, `ok`, `errors`, `warnings`, `config_hash`, and per-action
  summaries.
- Negative fixtures cover at least threshold weakening, duplicate custodian,
  revoked active key, testnet production key, and break-glass spend.

## Task 4: ZenoLedger Gate Wiring

Owner scope:

- `tools/zeno_ledger_node.py`
- ZenoLedger config/admission helpers under `src/integration/`
- focused tests under `tests/integration/`

Goal:

Require production key-management admission receipts for production-sensitive
ZenoLedger operations.

Required gates:

- public network config update -> `config` role;
- validator set update -> `validator` role;
- verifier registry update -> `verifier` role;
- oracle reporter registry update -> `oracle` role;
- release artifact publish -> `release` role;
- emergency pause -> `emergency` role;
- emergency unpause -> `config` role.

The implementation must keep public-testnet and local-demo flows explicitly
profile-scoped. Production-strict profile operations must require an admission
receipt before applying the operation.

Acceptance commands:

```bash
python3 -m py_compile tools/zeno_ledger_node.py src/integration/production_key_management_v0.py
pytest -q tests/integration/test_production_key_management_v0.py
pytest -q tests/integration/test_zeno_ledger_public_network_config_quorum.py
pytest -q tests/integration/test_zeno_ledger_verifier_registry_v0.py
git diff --check
```

Definition of done:

- Existing public-testnet flows still work without production profile.
- Production-strict flows require key-management receipts.
- Missing or tampered receipts are deterministic rejections.

## Task 5: Release Gate Integration

Owner scope:

- `tools/run_release_gate.sh`
- `tools/run_public_testnet_candidate_gate.sh`
- `tests/test_security_posture_files.py`
- claims/traceability docs if needed

Goal:

Make production key-management checks part of release posture.

Required changes:

- Run `tools/check_production_key_management_spec.py` in release gate.
- Py-compile all new runtime and checker files.
- Add security posture tests asserting the gate includes these checks.
- Add traceability entry once runtime admission exists.
- Add one static check that searches production-sensitive entrypoints for direct
  bypasses of the admission library.

Acceptance commands:

```bash
bash -n tools/run_release_gate.sh
bash -n tools/run_public_testnet_candidate_gate.sh
pytest -q tests/test_security_posture_files.py
python3 tools/check_production_traceability_matrix.py
git diff --check
```

Definition of done:

- Release gate fails if the property checker fails.
- Public-testnet gate may record the spec check as evidence. Production
  enforcement remains profile-specific.

## Task 6: Operator Runbook

Owner scope:

- `docs/PRODUCTION_KEY_MANAGEMENT_RUNBOOK.md`

Goal:

Write the human operational runbook without exposing secrets.

Required sections:

- key ceremony;
- signer inventory;
- role assignment;
- hardware wallet/HSM storage;
- MPC/TSS custody procedure;
- Shamir Secret Sharing backup and recovery ceremony;
- backup and recovery;
- rotation cadence;
- revocation drill;
- emergency pause drill;
- unpause governance;
- transparency log publication;
- incident response;
- testnet versus production separation.

Acceptance commands:

```bash
rg -n "BEGIN .*PRIVATE KEY|mnemonic:|seed phrase:|SECRET=|PASSWORD=" docs/PRODUCTION_KEY_MANAGEMENT_RUNBOOK.md
git diff --check
```

The `rg` command should return no matches. Descriptive text that says secrets
must not be committed is acceptable if it does not include a secret-like value.

## Task 7: Lean Refinement

Owner scope:

- `lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean`
- optional additional proof file if the first one becomes too large

Goal:

Refine the boolean proof surface into finite roles and action classes.

Required proof targets:

- `treasury_spend_admitted_no_single_key`
- `config_update_admitted_requires_timelock`
- `emergency_pause_admitted_does_not_authorize_unpause`
- `revoked_key_cannot_be_counted`
- `production_action_excludes_testnet_key`

Acceptance commands:

```bash
lean \
  lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
rg -n -w "sorry|admit|axiom" lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
git diff --check
```

Definition of done:

- No `sorry`, `admit`, or new `axiom`.
- Existing theorem names remain stable unless the spec is explicitly revised.
- New finite-role theorems either import the abstract boolean theorem or prove a
  direct bridge into it. They must not duplicate the policy table by hand unless
  the duplication is checked against the JSON model by a test.

## Handoff Order

Recommended order:

1. Task 1
2. Task 2
3. Task 3
4. Task 5
5. Task 4
6. Task 6
7. Task 7

Task 7 can run in parallel after Task 2 defines the runtime objects. Proof
changes must be checked locally before integration.
