---
title: SHAPEFORGE_AUTOTRADER_REASONING
type: note
permalink: autonomous-tau-dex-review/docs/zenodex/shapeforge-autotrader-reasoning
---

# ShapeForge AutoTrader Reasoning

## Baseline

The AutoTrader now has a dedicated ShapeForge world model in
`docs/zenodex/shapeforge_promoted/autotrader_world_model.seed.json` and a
negative-knowledge ledger in
`docs/zenodex/shapeforge_promoted/autotrader_negative_knowledge.seed.json`.

This formalizes five slices that already exist in code:

- signal provenance
- candidate-set contract
- binary decision certificate
- live admission bundle
- system composition

## What Improved

The most immediate runtime improvement was on the decision certificate surface.
`src/integration/autotrader_decision.py` no longer treats `binding_ok` as a
constant. The builder now derives it from the candidate set, winner pair, and
kill-switch posture, and the live path recomputes and verifies the expected
certificate before promoting a decision in `src/integration/autotrader_live.py`.

That closes a real gap: the old surface could claim a valid argmax witness
without explicitly re-binding the decision to the candidate set hashes and the
kill-switch state.

The mathematical core is now stronger as well. The repo has a Lean proof in
`lean-mathlib/Proofs/ZenoDEXAutoTraderBinaryDecision.lean` showing that the
current binary decision kernel has a unique canonical winner under the same
`(key desc, index asc)` order used by `argmax_stream_certificate_v1`, including
the `NO_OP` tie-break when emit is blocked.

The binding shell is also sharper now. The repo has a second Lean proof in
`lean-mathlib/Proofs/ZenoDEXAutoTraderDecisionBinding.lean` showing that, for a
fixed binary candidate set and kill-switch posture, the decision verifier
accepts exactly the canonical rebuilt certificate and that the verifying
certificate is unique. That closes the old "binding bit is just a convention"
gap at the shell-logic level.

## DEX Improvements Found With ShapeForge

The DEX settlement lane is stronger than before, but it is not end-to-end
formally closed.

Current strongest improvements identified by ShapeForge:

1. Make the replay-bound settlement certificate the default acceptance posture
   only after price-history provenance is internalized.
2. Internalize the remaining settlement feature-extension lanes
   (`buyback_floor`, `rebate`, `lock_weight`) or separately attest them.
3. Keep pushing exact-out generator completeness from bounded-search evidence
   toward a tighter certificate or proof surface.

## AutoTrader Improvements Found With ShapeForge

Current highest-leverage AutoTrader improvements:

1. Replace the current binary candidate frontier with a bounded multi-action
   frontier and a new total key plus certificate surface.
2. Tighten the concrete canonical JSON plus SHA256 modeling for the new
   stage-aware certificate and the stricter populated-report live-release
   packet.
3. Promote external-signal trust and source-registry posture into a tighter,
   replayable provenance surface.

## Current Bound

The AutoTrader decision binding is now locally derived and verified, and the
binary winner/tie-break kernel plus the abstract deterministic rebuild shell are
formally proved. The repo now also attaches a stage-aware certificate to every
runtime report, attaches the stricter live-release packet to populated reports,
and has abstract shell proofs for both packet families. The concrete decision,
stage, and live-release hashes now also share the repo-level canonical JSON plus
SHA256 primitives instead of three local helper copies, and the repo now has
payload-level fail-closed verifiers for those serialized certificate surfaces.
The external-signal provenance surface is tighter too: observation packets and
source registries now have roundtrip payload verifiers, and the live/shadow CLI
ingestion path fail-closes when a typed registry payload does not match its
canonical serialized form. What remains unproved is narrower: the concrete
canonical JSON plus SHA256 implementation of those packet surfaces, and a
stronger replayable provenance object that carries source-trust posture all the
way into the promoted AutoTrader slices. The repo now also has a parallel
bounded multi-action frontier in `src/integration/autotrader_multiaction_decision.py`:
`NO_OP + one candidate per allowed action`, an explicit total key, a deterministic
argmax-style winner certificate, and payload-level fail-closed verifiers. The
repo now also has a dedicated bounded multi-action candidate-set contract in
`src/kernels/dex/strategy_multi_action_candidate_set_contract_v1.yaml` with a
Python adapter, so the multi-action lane is no longer only an implemented/tested
payload surface. That closes the old “no concrete multi-action object exists”
gap. The shadow and
live assurance reports now expose that bounded multi-action lane whenever the
strategy action frontier is unambiguous, so it is no longer a dead-side module.
The repo now also maps both the binary decision certificate and the bounded
multi-action decision certificate into the shared `DecisionWitness` schema and
re-verifies those witnesses inside the shadow and live assurance reports. That
means the AutoTrader assurance lane now has one replayable witness object
family instead of a disconnected packet set. When Tau is enabled, the bounded
multi-action shadow and live sidecars now also replay their argmax witness
steps against the existing generic `argmax_stream_certificate_v1` Tau contract
instead of relying only on the local Python rebuild. It still has not replaced
the binary live admission path or been promoted into a proved kernel.