# `SHAPE_V1` Release Checklist

This is the operational release checklist for the current `SHAPE_V1` claim.

It is intentionally narrower than a universal `1.0` checklist.

## Ship / No-Ship Rule

You may ship a `SHAPE_V1` release candidate only if all of the following are true:

- the Shape ratchet is green
- the release gate is green from a clean checkout of the exact release commit
- the published docs match the actual artifact surface on that commit
- the public claim stays inside audited domain `D_v1`
- any still-open hardening lane is either:
  - merged into the release branch, or
  - explicitly excluded from the public claim

You must not widen the public label to unrestricted `1.0` if any of these remain open:

- Tau-native governed signer-registry retrieval or state-proof binding is absent
- exact-out global generator completeness is absent
- disputed settlement lanes remain outside witness-complete authorization
- zUSD still trails the spot core public replay bar

## Required Gates

Run these from a clean checkout of the exact release commit:

```bash
python3 tools/check_shape_v1_ratchet.py
bash tools/run_release_gate.sh
```

Expected result:

- `tools/check_shape_v1_ratchet.py` returns `OK SHAPE_V1 ...`
- `tools/run_release_gate.sh` passes end to end

If either gate fails, do not tag a release.

## Public Claim Discipline

The release statement should remain:

```text
ZenoDEX SHAPE_V1 is release-backed on audited domain D_v1.
```

Do not widen that statement to any of:

- unrestricted exact-out completeness
- fully decentralized oracle governance
- globally closed autotrader safety or liveness
- universal settlement authorization beyond the promoted bounded surface

Do not treat external Tau node behavior as repo-proved unless the upstream
boundary itself is brought under proof or equivalent machine-checked contract
control. The current assumption boundary is documented in:

- `docs/zenodex/EXTERNAL_ASSUMPTION_BOUNDARY_V1.md`

## Documentation Gate

Before tagging:

- `docs/zenodex/SHAPE_V1.md` matches the promoted Shape surface
- `docs/PUBLIC_ASSURANCE_REPLAY.md` matches the pinned replay surface
- `docs/ASSURANCE.md` does not overstate weaker subsystems
- Shape/backlog docs do not describe witness or liveness carriers that are not on clean `main`

If documentation drifts from the artifact surface, fix the docs before release.

## Settlement Attestation Lane

This lane is release-relevant because it affects settlement-price trust.

Before including governed settlement attestation in the public release claim, the release branch must contain:

- mandatory signer/source allowlists in attestation mode
- governed settlement attestation policy objects
- fail-closed policy/snapshot binding
- typed quorum bundle handling if governance requires more than one signer

If those are not all on the release branch, the release must explicitly exclude governed settlement attestation from the public claim.

Current limit that still blocks a stronger decentralization claim:

- the repo does not yet ship a Tau-native direct registry/state-proof loader
- the Tau Testnet node surface remains externally controlled and therefore part of the release assumption boundary

## Publication Bundle

At tag time, publish one authoritative release bundle:

- commit sha
- release tag
- release note
- Shape ratchet receipt
- release gate receipt
- pinned public claim text
- explicit exclusions / out-of-scope items

Current authoritative example:

- `docs/zenodex/SHAPE_V1_RC1.md`

Do not rely on multiple hand-maintained summaries as the authority surface.

## Correct Release Label

If every gate above is green, the correct label is:

```text
ZenoDEX SHAPE_V1 release candidate
```

If stronger claims are desired, they require a new manifest revision and a new checklist.

## Immediate Next Upgrades

These are the next honest upgrades after a scoped `SHAPE_V1` release:

1. Tau-native governed signer-registry retrieval or state-proof binding
2. witness-complete settlement treatment for disputed lanes
3. zUSD promotion to the same public replay bar as the spot core
4. stronger protocol-level liveness publication
5. generated single-source release/publication manifest
