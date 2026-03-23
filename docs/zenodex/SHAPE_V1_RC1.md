# ZenoDEX `SHAPE_V1` Release Candidate 1

## Freeze

- tag: `shape-v1-rc1`
- release target commit: `dfeee90d3893309c6df72982a9c2d69c5add6a4b`
- note publication commit: `51ac3afd168fd0cf6b3353703639810d593bdb9f`
- claim label: `ZenoDEX SHAPE_V1 release candidate`

This document is the scoped freeze note for the first `SHAPE_V1` release candidate.
It is narrower than a universal `1.0` statement.

## Included Release Surface

This freeze includes the audited-domain `D_v1` surface described in:

- `docs/zenodex/SHAPE_V1.md`
- `docs/zenodex/SHAPE_V1_RELEASE_CHECKLIST.md`

Release-relevant merges included in this freeze:

- `#102` docs: reconcile Shape evidence backlog claims
- `#104` security: require settlement attestation signer allowlists
- `#106` docs: add shape v1 release checklist
- `#107` security: govern settlement attestation policy
- `#108` tests: fix clean release gate drift

## Gate Receipts

Pinned release receipts on the candidate branch that became this tag:

- `python3 tools/check_shape_v1_ratchet.py`
  - `OK SHAPE_V1 shape_pp_candidate_v1=10/10 dex_kernel_candidate_v1=6/6 runtime_boundary_candidate_v1=5/5`
- `bash tools/run_release_gate.sh`
  - passed end to end on the clean candidate branch before merge
- `python3 tools/check_derivatives_evidence_manifest.py`
  - `ok`
- `python3 tools/check_spot_proof_assurance_manifest.py`
  - `ok`
- `python3 tools/system_spec_lint.py src/kernels/dex/zenodex_system_compose_v2.yaml`
  - `ok`
- `python3 -m pip_audit -r requirements.txt`
  - `No known vulnerabilities found`

Key release-lane counts from that freeze:

- acceptance TCB gate: `361 passed`, `99.4%` branch coverage
- critical pytest + coverage gate: `735 passed`, `1 skipped`, `99%` branch-enabled coverage
- mutation gate: `7/7` killed
- fuzz gate: `11 passed`
- snapshot recovery gate: `19 passed`
- Tau syntax gate: `62/62` specs passed
- Tau trace registry gate: `1/1` passed
- perps evidence lane: `330 passed`, plus ESSO cross-solver verification and Lean proof builds
- spot evidence lane: `214 passed`, `2 skipped`, plus ESSO cross-solver verification
- derivatives evidence lane: `160 passed`, plus ESSO cross-solver verification

## Public Claim

The correct public statement for this tag is:

```text
ZenoDEX SHAPE_V1 is release-backed on audited domain D_v1.
```

That means:

- the promoted Shape targets remain green
- the release gate cleared on the exact candidate branch used for this freeze
- the public replay surface is fail-closed and manifest-backed

## Explicit Non-Claims

This tag does not justify any of the following:

- unrestricted exact-out generator completeness
- fully decentralized oracle governance
- Tau-native direct signer-registry state proof binding
- universal settlement authorization beyond the promoted bounded surface
- repo-wide `1.0` status for weaker subsystems such as `zUSD`

External-dependency note:

- Tau-native provenance beyond the published host-side contract remains conditional on the external Tau Testnet surface documented in
  `docs/zenodex/EXTERNAL_ASSUMPTION_BOUNDARY_V1.md`

## Replay Entry Points

Fresh-clone replay surface:

```bash
python3 tools/permissionless_assurance.py status
python3 tools/permissionless_assurance.py replay public
python3 tools/permissionless_assurance.py replay critical
python3 tools/permissionless_assurance.py replay full
```

## Immediate Next Upgrade

The next hardening lane after this freeze is:

- Tau-native governed signer-registry retrieval or state-proof binding

That lane is formalized in:

- `docs/zenodex/SETTLEMENT_SIGNER_REGISTRY_TAU_NATIVE_V1.md`
- `docs/zenodex/EXTERNAL_ASSUMPTION_BOUNDARY_V1.md`
- `src/tau_specs/recommended/settlement_signer_registry_anchor_gate_v1.tau`
- `formal/tla/SettlementSignerRegistryTauBridge.tla`
