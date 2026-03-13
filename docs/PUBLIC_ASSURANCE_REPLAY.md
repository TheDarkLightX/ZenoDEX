---
title: PUBLIC_ASSURANCE_REPLAY
type: note
permalink: autonomous-tau-dex-review/docs/public-assurance-replay
---

## Public assurance replay

This repo exposes a narrow, replayable public assurance surface. The goal is:

- ship enough material for a fresh clone to reproduce the main assurance claims
- avoid shipping private scratch, internal solver outputs, or local agent tooling
- keep the publishable surface fail-closed

Current pinned release snapshot on this tree:

- acceptance TCB: `341 passed`, `100%` branch coverage
- critical gate: `1311 passed`, `100%` branch coverage
- release gate: passed end to end
- mutation gate: `7/7` killed
- fuzz gate: `11 passed`
- snapshot recovery: `16 passed`
- Tau syntax: `58/58`

Current derivatives note:

- The published v1.1 funding-rate formal story is the decomposed one:
  `funding_rate_market_v1` for phase/state transitions plus
  `funding_rate_settlement_witness_v1_1` for settlement arithmetic.
- The monolithic `funding_rate_market_v1_1` kernel remains useful for parity/reference work, but it is no longer
  part of the public formal release claim.
- `funding_rate_market_v1` and `curve_selection_market_v1` should currently be treated as disputed for settlement
  authorization semantics until their settlement paths are guarded by a trusted witness/auth lane end to end.

What is intentionally public:

- pinned manifests under `tools/*.json`
- replay/checker CLIs under `tools/`
- the small exported Python refs under `generated/*_ref.py` that parity tests depend on
- the gate scripts that rebuild internal artifacts locally

What is intentionally **not** shipped:

- `internal/` solver reports and coverage maps
- `external/` vendored toolchains
- `runs/`, local agent scratch, MCP configs, or other local workspace state

Fresh clone workflow:

```bash
python3 tools/permissionless_assurance.py status
python3 tools/permissionless_assurance.py replay public
python3 tools/permissionless_assurance.py replay zusd
python3 tools/permissionless_assurance.py replay critical
python3 tools/permissionless_assurance.py replay full
```

Notes:

- `status` is the fast proofboard. It reports whether the publishable lanes and exported refs are present and tracked.
- `replay public` is the public proof surface: manifest-backed kernel assurance plus the spot/derivatives proof lanes.
- `replay zusd` reruns the zUSD monetary core, Tau gating, Tau transfer transport, wallet CLI, and `protocol_token_v1` formal lane.
- `replay critical` reruns the publishable critical quality gate.
- `replay full` runs the full release gate.
- `internal/` artifacts are regenerated locally during replay. They are not part of the repo payload.

Pre-commit / pre-merge hygiene:

```bash
python3 tools/permissionless_assurance.py stage-scope
python3 tools/permissionless_assurance.py leak-check
```

- `stage-scope` lists the narrow public-assurance files worth staging from a dirty tree.
- `leak-check` blocks obvious private/internal paths and the explicit internal markers we do not want in a public merge.

The important distinction is that public replayability does **not** mean shipping every intermediate artifact. The public contract is:

1. tracked manifests pin the expected source/toolchain posture,
2. tracked exported refs let parity tests run on a fresh clone,
3. gate scripts rebuild local `internal/` evidence and fail closed on drift.
