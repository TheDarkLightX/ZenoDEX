---
title: RC1_READINESS
type: note
permalink: autonomous-tau-dex-review/docs/rc1-readiness
---

# ZenoDEX RC1 Readiness

This document answers a narrower question than [docs/dex_readiness.md](dex_readiness.md):

**What still needs to be completed before an honest RC1 cut?**

It is not a generic “is the repo good?” note. It is a release-boundary document.

For the proposed include/exclude release surface, see [RC1_SCOPE.md](RC1_SCOPE.md).

## Recommended RC1 Scope

**Include**

- core spot DEX functional path
- supported API/runtime path
- wallet/sign/transport path for the supported operations
- public assurance replay surface
- pinned proof/evidence/release gates

**Exclude**

- experimental autotrader live authority
- KRR / ZenoGraph ranking influence
- experimental advisory/research shells
- disputed derivatives settlement authorization claims

Reason:

- the core public proofboard is strong enough to support an RC1 lane
- the experimental AI/advisory surfaces are intentionally fenced off and should stay out of RC1 authority
- some derivatives claims are still explicitly disputed in the public assurance surface

## Current RC1 Posture

As of 2026-04-05:

- `python3 tools/permissionless_assurance.py status` reports:
  - `assurance snapshot: OK (as of 2026-03-22)`
  - `tla claim summary: OK`
  - `lane readiness: 8/8`
  - `release: READY`
- the tree is still heavily dirty, so this is **not** yet an RC1 cut candidate by itself

Interpretation:

- the release machinery and proofboard are in good shape
- the remaining RC1 work is now mostly about scope discipline, hardening closure, and release hygiene

## Must Be Complete For RC1

### 1. Freeze the RC1 scope

RC1 must name the exact supported surface:

- which product lanes are in
- which are out
- which claims are public
- which claims are explicitly experimental or disputed

Without this, “RC1” is ambiguous and will overclaim.

The checked artifact for this scope freeze is:

```bash
python3 tools/render_rc1_supported_runtime_path.py --check
python3 tools/render_rc1_verified_surface_matrix.py --check
```

### 2. Cut from a clean release tree

The live status still shows a large dirty tree.

RC1 should be cut only from:

- a clean worktree
- a pinned commit/tag
- a replayed assurance state

This is a release hygiene requirement, not just a preference.

### 3. Keep the public proofboard fully clean

RC1 should not ship with:

- stale generated summaries
- missing claim entries
- undocumented TLA models
- broken public replay lanes

The TLA claim-summary drift around `ZenoGraphHostLocalAcceptance` was a real example of the kind of issue that must be closed before RC1.

### 4. Resolve or defer disputed derivatives claims

The public assurance note already says:

- `funding_rate_market_v1` remains disputed for settlement authorization semantics
- `curve_selection_market_v1` remains disputed for settlement authorization semantics

For RC1, either:

- resolve these claims, or
- keep them clearly outside the RC1 authorization surface

Do not market disputed claims as RC1-backed guarantees.

### 5. Pin the supported runtime/signing path

RC1 should have one declared supported path for:

- request admission
- signing
- nonce/sequence handling
- submission transport
- failure and retry behavior

The repo contains multiple integration surfaces. RC1 needs one pinned contract, not several partial ones.

### 6. Close or defer active mechanism hardening items

The mechanism roadmap still shows active hardening work, especially around:

- oracle-clamp and manipulation-envelope posture
- exact-out/routing hot-path behavior
- compute-budget and monitoring posture

If RC1 includes the affected runtime paths, these are release blockers.
If RC1 excludes them, that exclusion must be explicit.

### 7. Pin operational hardening for the supported path

RC1 should have a concrete posture for:

- rate limiting
- circuit breakers / kill switches
- monitoring and alerting
- restart/recovery expectations
- load/chaos posture for the supported boundary

Code existence is not enough; the supported operational contract must be named.

### 7a. Keep the acceptance fuzz posture explicit

RC1 now has two acceptance fuzz tiers:

- fast default lane:
  - `bash tools/run_acceptance_tcb_fuzz_gate.sh`
- deep stateful campaign lane:
  - `bash tools/run_acceptance_tcb_fuzz_gate_deep.sh`
  - `python3 tools/acceptance_tcb_fuzz_campaign.py`

Reason:

- the fast lane keeps routine RC1 hygiene bounded
- the deep lane covers heavier stateful `dex_engine` replay, quote-receipt, and settlement trajectories
- deep campaign receipts now default under `internal/fuzz_campaigns/deep/`

The release gate should rely on the fast lane.
The deep lane should remain part of campaign evidence and periodic replay, not disappear.

### 8. Keep experimental AI/advisory lanes out of authority

For RC1:

- autotrader should remain advanced/experimental
- ZenoGraph should remain advisory-only
- ranking influence should remain blocked until the signed replay gate actually passes

This is both a product-scope boundary and a safety boundary.

## Suggested RC1 Exit Criteria

RC1 is honest when all of the following are true:

1. RC1 scope is written down and reviewed.
2. The verified surface matrix is current.
3. The supported runtime/signing path artifact is current.
4. The release tree is clean and pinned.
5. `python3 tools/permissionless_assurance.py status` is clean.
6. The public release gate is replayed successfully from the pinned tree.
7. Disputed claims are either resolved or explicitly excluded from RC1.
8. The supported runtime/signing path is documented and smoke-tested.
9. Active hardening gaps for included runtime paths are closed or explicitly deferred out of scope.
10. Experimental autotrader / AI lanes remain non-authoritative.
11. The fast-vs-deep acceptance fuzz posture is documented and used consistently.

## Practical Next Steps

1. Create a clean RC1 candidate branch or tag from a clean tree.
2. Write the final include/exclude list for RC1 using this document as the boundary.
3. Freeze and check the verified surface matrix and supported runtime-path artifact.
4. Re-run the public release gate from that candidate tree.
5. If derivatives are in scope, settle the disputed-claim posture before calling it RC1.
6. Keep autotrader and ZenoGraph outside runtime authority for RC1.
