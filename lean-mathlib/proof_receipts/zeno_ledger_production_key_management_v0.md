# ZenoLedger Production Key Management V0 Proof Receipt

Date: 2026-05-19

Target:

```text
lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
```

Claim:

```text
Admitted production key-management actions imply the abstract safety contract:
production environment, authorized role, quorum, no single-key critical
authority, distinct custodians, no revoked or expired signer, hardware backing
when required, timelock when required, break-glass scope, production-key
separation, and transparency receipt binding.
```

Checked theorem surface:

```text
admitted_safe
admitted_quorum_met
admitted_no_single_key_authority
admitted_no_revoked_signer
admitted_no_expired_signer
admitted_production_keys_only
admitted_transparency_receipt_bound
rejects_non_production_environment
rejects_missing_quorum
rejects_single_key_authority
rejects_same_custodian_quorum
rejects_revoked_signer
rejects_expired_signer
rejects_software_key_when_hardware_required
rejects_missing_timelock_when_required
rejects_break_glass_scope_violation
rejects_testnet_key_for_production
rejects_missing_transparency_receipt
admits_safe_production_key_action
treasury_spend_admitted_no_single_key
config_update_admitted_requires_timelock
emergency_pause_admitted_does_not_authorize_unpause
revoked_key_cannot_be_counted
production_action_excludes_testnet_key
```

Commands run:

```bash
python3 -m json.tool formal/property/production_key_management_v0.json >/dev/null
python3 -m py_compile tools/check_production_key_management_spec.py tests/test_production_key_management_spec.py
python3 tools/check_production_key_management_spec.py
python3 tools/check_production_key_management_esso_equivalent.py
pytest -q tests/test_production_key_management_spec.py
/home/trevormoc/.elan/toolchains/leanprover--lean4---v4.27.0/bin/lean lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
rg -n -w "sorry|admit|axiom" lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
git diff --check
```

Results:

```text
property model JSON parse: pass
py_compile: pass
property checker: pass, 164 cases
ESSO-equivalent finite-model checker: pass
pytest: pass, 1 test
standalone Lean target: pass
placeholder scan: pass, no matches
git diff --check: pass
```

Known local environment limit:

```text
cd lean-mathlib && lake env lean Proofs.lean
```

This full aggregator check did not run in the current worktree because
`external/mathlib4` is absent. The new Lean target itself checks with the pinned
Lean binary because it is intentionally mathlib-free.

Artifact hashes:

```text
4649e1ab848af81ed61c0813708af5845d5af97db37369ad8f2486ea62dc0167  lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
f1a8fceab39a2768784f57db96990fa2442db95a88d1ddd358069c4eaaa350e7  formal/property/production_key_management_v0.json
2c85414aa9f0133ce44e953e8c700a9bea626a489392cbeb5476454b782614c4  formal/esso/production_key_management_v0.esso.yaml
8b3e70f441b687d5fef7cf147f7b734e8cd509cf041f0c71692a338318479815  tools/check_production_key_management_spec.py
d4165eb51731d350fc07e57afb77c3dd41620015f4a739f8f57587941209f9d7  tools/check_production_key_management_esso_equivalent.py
73fd3bdac46792a16363cd6b69a0e28a2c7ba4dbd047d3b17ac5176912d2c9c1  docs/PRODUCTION_KEY_MANAGEMENT_V0_SPEC.md
277d62426199d913453171205d55a56e10a09600a6455cb505c01a69250bde2b  docs/PRODUCTION_KEY_MANAGEMENT_AGENT_TASKS.md
```
