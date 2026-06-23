---
title: AUTOTRADER_KRR
type: note
permalink: autonomous-tau-dex-review/docs/autotrader-krr
---

# Auto-Trader KRR

The policy-constrained auto-trader uses KRR only as an advisory layer.

## Risk Notice

The auto-trader, KRR, and `ZenoGraph` surfaces are advanced experimental
automation and AI features.

- They are not recommended for general users.
- They should be treated as operator/research tooling first.
- They can contribute to bad live decisions and total loss.
- Use them only at your own risk.
- `tools/autotrader_live.py` now requires an explicit
  `--acknowledge-experimental-live-risk` flag before it will prepare live
  operations.

The trust boundary is fixed:

- LLMs can propose policy text.
- The bounded compiler turns that text into `StrategyIR`.
- KRR ranks which checks matter most for the current phase.
- Verified guards and fail-closed shell logic decide whether anything is allowed.
- KRR never signs, never mutates balances, and never replaces the core runtime.

The advisory boundary also has a small Lean capability model in
`lean-mathlib/Proofs/AgentCapabilityBounds.lean`. The key machine-checked
facts are:

- `advisory_non_authoritative_blocks_live_execution`
- `advisory_non_authoritative_blocks_execute`

Plain English: an advisory-only, non-live capability cannot authorize live
execution, even when the request labels itself as advisory, and it cannot
authorize execute-class requests at all.

That boundary is linked to the poka-yoke submit theorem in
`lean-mathlib/Proofs/AdvisoryPokayokeBridge.lean`. The bridge proves that an
advisory, non-live capability cannot both authorize an execute/live request and
pass through the generic submit predicate; for dangerous unshielded requests,
capability admission and poka-yoke interlocks reject on separate fail-closed
boundaries.

## Signal Method

The auto-trader uses a signals-first method for execution and keeps open-ended
research inputs advisory-only.

- Trusted execution signals come from deterministic protocol state, verified
  quote receipts, Tau receipts, and capability/session state.
- External feeds, user-loaded knowledge bases, LLM text, and OSI-style
  research are allowed only as advisory context unless they are wrapped in a
  typed verified or attested signal packet.
- KRR consumes a bounded observation packet, not raw APIs.
- Public `shadow` and `live` CLIs now accept `--external-signals-file` so
  users can replay the exact advisory/attested signal bundle that KRR saw.

The observation packet is modeled in
[`src/integration/autotrader_signals.py`](../src/integration/autotrader_signals.py)
under the schema `zenodex/autotrader-observation-packet/v1`.

It contains:

- one primary trusted signal packet
- zero or more external signal observations
- optional wallet capability state
- an explicit `tau_enabled` bit

The current trust tiers are:

- `protocol`
- `verified`
- `attested`
- `advisory`

Only trusted signals may unlock execution. Advisory signals may influence KRR
ranking or explanations, but never bypass shell guards.

## Logic Model

The KRR import path uses a strong logic model, but not a live OWL reasoner in
the execution path.

The offline import bundle is a closed-world typed graph with five primary row
families:

- source snapshots
- evidence records
- canonical claims
- review records
- derived source-quality rows

This is deliberately close to a subject-predicate-object pipeline, but with
explicit provenance and temporal structure:

- a source snapshot identifies the exact fetched artifact and parser version
- an evidence record points at a citeable span inside that snapshot
- a canonical claim distills one reviewed fact from one or more evidence rows
- a review record approves or rejects bundles, claims, sources, or evidence
- derived source quality is computed from replay history and source reviews

We do not use open-world semantics at runtime. Runtime only reads a reviewed,
signed local bundle and then compiles it back into bounded artifacts already
supported by the auto-trader:

- `runtime_krr_kb`
- `runtime_external_signals`
- `runtime_signal_source_registry`
- `runtime_history`

That keeps execution deterministic and fail-closed. The bundle may contain
research knowledge, but execution still goes through typed observation packets,
ESSO/Tau guards, and signed intent logic.

## Offline Bundle Import

The public import/build/verify tools are:

- `tools/autotrader_krr_import_source.py`
- `tools/autotrader_krr_import_wikidata.py`
- `tools/autotrader_krr_bundle_build.py`
- `tools/autotrader_krr_bundle_verify.py`

The compile, shadow, and live CLIs can now consume one reviewed signed bundle:

- `tools/autotrader_policy_compile.py --krr-bundle-file ...`
- `tools/autotrader_shadow.py --krr-bundle-file ...`
- `tools/autotrader_live.py --krr-bundle-file ...`

The live CLI remains intentionally harder to use than compile/shadow surfaces.
Shadow and replay are accessible for research, but live preparation is gated by
an explicit risk acknowledgement because this is still experimental automation.

The same posture applies to signed `ZenoGraph` material: signed packs may be
used for advisory replay and comparison, but ranking influence remains blocked
unless the separate signed-pack ranking-promotion gate passes. That gate now
also requires a signed replay-coverage contract:

- minimum signed baseline size: `20`
- required family coverage:
  - `aligned_neutral`
  - `aligned_irrelevant`
  - `governance_block`
  - `oracle_stale_block`
- `slippage_limit_block`
- zero submit-vs-block disagreement
- zero block-vs-allow disagreement

If that gate eventually passes, `tools/zenograph_autotrader_ranking_stage.py`
is the intended non-core staging surface. It can surface a ranking candidate,
but it still does not change controller execution.

Mixed modes are rejected fail-closed. A reviewed bundle cannot be combined with
raw `--krr-kb`, `--external-signals-file`, `--signal-source-registry-file`, or
`--history-check-stats-file` inputs.

## High-ROI Financial Knowledge

For trading strategy work, not all public knowledge is equally valuable.

The highest-ROI import order is:

1. deterministic protocol and venue state
2. replayed fills, quote outcomes, and local execution history
3. official macro, rates, and reporting feeds
4. trusted external market structure and positioning feeds
5. slow-moving reference ontologies and entity directories

That means:

- on-chain venue state, oracle state, and replay history should dominate KRR
- SEC/XBRL, FRED, World Bank, IMF, and CFTC-style sources are stronger than
  generic web pages for strategy context
- Wikidata, FIBO, GLEIF, and OpenCorporates are primarily reference layers for
  entity resolution, identifiers, taxonomy, and ownership context
- do not treat Wikidata or ontology imports as alpha by themselves

The Wikidata importer supports a bounded
`financial-trading-reference` profile so users can fetch only a narrow finance
slice from remote entity JSON instead of the full dump. This profile is for
reference facts such as:

- LEI
- ISIN
- stock exchange
- industry
- country
- headquarters
- parent/subsidiary links
- OpenCorporates ID

Use that profile to build reviewed reference bundles, then combine those with
separate higher-frequency market and macro bundles.

The repo also includes a priority policy file for this ordering in
[`tools/krr_financial_trading_source_policy.json`](../tools/krr_financial_trading_source_policy.json).

## Full Plan

The KRR plan for the auto-trader is:

1. Unify advisory semantics across `compile`, `shadow`, and `live`.
2. Use one bounded schema and one deterministic semantic signature for all three phases.
3. Keep KRR phase-aware, with explicit checks for:
   - compile bounds and owner binding
   - compile-contract validity for the bounded `StrategyIR`
   - window, cadence, budget, lifetime, and live-order pressure
   - oracle freshness and quote-receipt validation
   - live signer and nonce checks
   - Tau bundle checks when the strategy is Tau-backed
4. Emit replayable advisory output in every CLI/report surface.
5. Feed replayed reports back into `history_check_stats` so later rankings can learn from observed guard outcomes.
6. Keep KRR advisory-only even after refinement; execution still goes through verified guards, Tau checks, and signed intents.

## Phase Status

- Phase 1, bounded policy IR and deterministic compiler: complete
- Phase 2, shadow-mode controller and replay CLI: complete
- Phase 3, live prepare/emit shell with signer, nonce, tx-envelope, wallet-capability, and composed admission guards: complete
- Phase 4, typed signal packets with trusted/advisory separation and formal provenance/freshness checks: complete
- Phase 5, replayable KRR outputs plus history/refinement loop across compile/shadow/live: complete

The remaining exclusions are intentional safety boundaries, not unfinished
implementation phases.

## Current State

Completed:

- Shared KRR helper in `src/agents/krr_policy_advisor.py`
- Compile, shadow, and live integration
- Phase-aware semantic signatures and candidate-check sets
- Replayable KRR output in compile/shadow/live reports
- Deterministic history builder in `tools/autotrader_krr_history.py`
- Typed observation packets and trusted/advisory signal separation
- ESSO-backed external-signal intake contract for user-loaded advisory and
  attested signals
- Deterministic per-source quality summaries, including registry posture and
  replayed source-history rates when available
- ESSO-backed compile contract for `StrategyIR`, enforced fail-closed in
  `src/agents/policy_compiler.py`
- Tau-backed compile contract receipts in the public compile CLI, with a
  dedicated Tau spec and witness builder alongside the ESSO kernel
- ESSO-backed end-to-end system compose contract for the live emit path,
  enforced fail-closed in `src/integration/autotrader_live.py`
- ESSO-backed signer/owner binding guard for the live shell path, folded into
  the live emit compose contract before intent signing

Still intentionally not done:

- No autonomous KRR execution path
- No KRR inside `src/core/` or `src/state/`
- No wallet authority for KRR

## System Compose

The live auto-trader now checks one end-to-end shell compose contract before it
emits signed intents:

- signer binding is still satisfied
- compile contract is still satisfied
- signal provenance is still satisfied
- execution guard is satisfied
- oracle freshness is satisfied
- budget guard is satisfied
- wallet capability is satisfied
- nonce checks are satisfied

This contract is modeled in
[`src/kernels/dex/strategy_system_compose_v1.yaml`](../src/kernels/dex/strategy_system_compose_v1.yaml)
and adapted in
[`src/kernels/python/strategy_system_compose_v1_adapter.py`](../src/kernels/python/strategy_system_compose_v1_adapter.py).

The public live report includes a `system_compose` block so replay users can
see whether the emit path was admitted by the full composed contract or stopped
fail-closed before signing.

## Replay and Refinement

You can build KRR history from replay reports:

```bash
python3 tools/autotrader_krr_history.py \
  --report-file /tmp/compile.json \
  --report-file /tmp/shadow.json \
  --report-file /tmp/live.json \
  --history-out /tmp/autotrader_krr_history.json \
  --pretty
```

That output can be passed back into `--history-check-stats-file` for:

- `tools/autotrader_shadow.py`
- `tools/autotrader_live.py`

This keeps the loop replayable and local. It does not change consensus behavior.
When the full history artifact is supplied instead of only raw
`history_check_stats`, KRR also loads `history_source_stats` and emits
`source_quality_summary` rows for each external signal source.

## Observation Summary

When an observation packet is available, KRR output now includes a deterministic
`observation_summary` with:

- primary source kind and trust tier
- quote verification and binding status
- signal age/freshness
- trusted/advisory external signal counts
- trusted external signal count vs advisory external signal count
- source-history availability and low-reliability/unseen external-source counts
- wallet capability presence
- Tau enablement

This summary is included in the semantic signature and replay output so later
history/refinement runs can distinguish trusted-signal posture from advisory
signal posture without re-reading arbitrary external feeds.
