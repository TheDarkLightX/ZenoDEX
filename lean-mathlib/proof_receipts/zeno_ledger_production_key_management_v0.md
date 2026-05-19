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
```

Commands run:

```bash
python3 -m json.tool formal/property/production_key_management_v0.json >/dev/null
python3 -m py_compile tools/check_production_key_management_spec.py tests/test_production_key_management_spec.py
python3 tools/check_production_key_management_spec.py
pytest -q tests/test_production_key_management_spec.py
/home/trevormoc/.elan/toolchains/leanprover--lean4---v4.27.0/bin/lean lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
rg -n -w "sorry|admit|axiom" lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
git diff --check
```

Results:

```text
property model JSON parse: pass
py_compile: pass
property checker: pass, 135 cases
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
ae54b9ed816efb8e420fd0355044b199e182e524824085507e8129bdc9d59e2d  lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean
f1a8fceab39a2768784f57db96990fa2442db95a88d1ddd358069c4eaaa350e7  formal/property/production_key_management_v0.json
5584331fc5dd16e3b0c8ddf0e6888a16953cdf3e7b9681757ef236e75ee99a22  formal/esso/production_key_management_v0.esso.yaml
38aec28dd2172943e39c5447b7f83311e68f43e66c908097474303d5b0f69b27  tools/check_production_key_management_spec.py
8dddc93fa6971a2a2777cfb740eb4890cafdf3f29aa54e68540033c5ff2af61a  docs/PRODUCTION_KEY_MANAGEMENT_V0_SPEC.md
277d62426199d913453171205d55a56e10a09600a6455cb505c01a69250bde2b  docs/PRODUCTION_KEY_MANAGEMENT_AGENT_TASKS.md
```
