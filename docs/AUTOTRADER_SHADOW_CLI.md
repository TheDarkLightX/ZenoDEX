---
title: AUTOTRADER_SHADOW_CLI
type: note
permalink: autonomous-tau-dex-review/docs/autotrader-shadow-cli
---

# AutoTrader Shadow CLI

`tools/autotrader_shadow.py` is the shell-side replay tool for the bounded auto-trader.

## Risk Notice

This is an advanced experimental automation and AI surface.

- It is not recommended for general users.
- It should be treated as advisory-only research tooling.
- Any live use of automation outputs is at your own risk.
- You can lose everything if you later promote bad automation decisions into live trading or investing.

It does not sign transactions, submit operations, or mutate consensus state. It:

- loads a bounded `StrategyIR` from a local policy document, raw candidate JSON,
  or controlled policy text
- loads a verified route quote receipt and pool snapshot set
- evaluates the policy with the shell controller in `src/integration/autotrader_controller.py`
- emits deterministic JSON describing whether the strategy would submit intents
- optionally runs the Tau budget guard for Tau-backed policies
- optionally attaches KRR advice as advisory metadata only
- optionally attaches `ZenoGraph` advisory reasoning without changing controller semantics

## Scope

Current Phase 2 scope:

- `DCA` template only
- quote-receipt-driven `SWAP_EXACT_IN` intent emission
- local policy backend or Tau-backed budget admission
- dry-run / shadow evaluation only

Out of scope:

- live signing
- transaction submission
- direct wallet control
- unconstrained LLM trading

## Inputs

- `--policy-file`: local policy document JSON produced from `StrategyIR`
- `--candidate-file`: raw candidate JSON compiled through `policy_compiler`
- `--policy-text`: inline controlled policy text
- `--policy-text-file`: path to controlled policy text
- `--receipt-file`: route quote receipt JSON
- `--pools-file`: pool snapshot JSON
- `--controller-state-file`: optional controller state JSON
- `--external-signals-file`: optional advisory/attested external signal JSON
- `--zenograph-enable`: enable parallel `ZenoGraph` advisory evaluation
- `--zenograph-facts-file`: optional `ZenoGraph` facts JSON
- `--zenograph-fact-pack-file`: optional reviewed and signed `ZenoGraph` fact pack JSON
- `--zenograph-signals-file`: optional `ZenoGraph` signals JSON
- `--zenograph-user-state-file`: optional `ZenoGraph` user-state JSON
- `--zenograph-source-trust`: advisory trust tier for `ZenoGraph` evaluation
- `--zenograph-liquidity-state`: optional liquidity-state token for `ZenoGraph` rules

## Output

The tool emits `zenodex/autotrader-shadow-report/v1` JSON with:

- `risk_disclosure`
- `strategy`
- `external_signals`
- `observation_packet`
- `controller_state_before`
- `decision`
- `decision.controller_state_after`
- `decision.intents`
- `decision.tau_policy_receipt`
- `krr_advice`
- `zenograph_advisory`

When KRR is enabled and the shadow run can build a trusted observation packet,
`krr_advice` also includes an `observation_summary` describing:

- primary signal source/trust tier
- quote verification/binding status
- signal freshness posture
- advisory vs trusted external signal counts
- wallet capability presence
- Tau enablement

User-loaded external signals are still advisory unless they satisfy the
bounded external-signal intake contract. Advisory signals can influence KRR
ranking or explanations, but they never bypass shell guards.

## Examples

Local policy:

```bash
python3 tools/autotrader_shadow.py \
  --policy-file /tmp/policy.json \
  --receipt-file /tmp/receipt.json \
  --pools-file /tmp/pools.json \
  --current-epoch 5 \
  --intent-deadline 99 \
  --pretty
```

Tau-backed policy:

```bash
python3 tools/autotrader_shadow.py \
  --policy-file /tmp/policy_tau.json \
  --receipt-file /tmp/receipt.json \
  --pools-file /tmp/pools.json \
  --current-epoch 5 \
  --intent-deadline 99 \
  --tau-enabled \
  --tau-bin /absolute/path/to/tau \
  --pretty
```

Controlled policy text:

```bash
python3 tools/autotrader_shadow.py \
  --policy-text "dca 100 zUSD into BTC every 4 epochs until epoch 20" \
  --owner-pubkey owner.pubkey.1 \
  --receipt-file /tmp/receipt.json \
  --pools-file /tmp/pools.json \
  --current-epoch 5 \
  --intent-deadline 99 \
  --pretty
```

With telemetry artifact:

```bash
python3 tools/autotrader_shadow.py \
  --policy-file /tmp/policy.json \
  --receipt-file /tmp/receipt.json \
  --pools-file /tmp/pools.json \
  --current-epoch 5 \
  --intent-deadline 99 \
  --telemetry-out /tmp/autotrader_shadow_report.json
```

With external signals:

```bash
python3 tools/autotrader_shadow.py \
  --policy-file /tmp/policy.json \
  --receipt-file /tmp/receipt.json \
  --pools-file /tmp/pools.json \
  --external-signals-file /tmp/external_signals.json \
  --current-epoch 5 \
  --intent-deadline 99 \
  --pretty
```

## KRR

`--krr-backend` controls optional advisory ranking of checks around the strategy.

This advice is not part of execution semantics. It is metadata for operators and
future LLM frontends. The controller still makes the final deterministic
allow/skip/reject decision without KRR.

KRR is also an advanced experimental layer. Treat it as advisory and
operator-facing, not as a promise of safe or profitable automation.

## ZenoGraph

`ZenoGraph` runs in parallel as advisory-only metadata. It does not override the
controller and it does not change the emitted submit/skip/reject decision.

`ZenoGraph` should also be treated as advanced experimental automation at your
own risk. It is accessible for research and shadow use, not as a safety claim
or profit guarantee.

Even when `ZenoGraph` facts are reviewed and signed, they remain advisory-only
by default. Signed packs are not allowed to influence ranking unless the
separate ranking-promotion gate is replay-clean, meets the signed replay
coverage contract, and is explicitly enabled. The current contract requires:

- a signed accepted-store replay baseline
- at least `20` baseline cases
- required family coverage for:
  - `aligned_neutral`
  - `aligned_irrelevant`
  - `governance_block`
  - `oracle_stale_block`
  - `slippage_limit_block`
- zero `controller_submit_vs_zenograph_block_rate`
- zero `controller_block_vs_zenograph_allow_rate`

The separate `tools/zenograph_autotrader_ranking_stage.py` helper is only a
ranking-stage surface. It can stage a candidate template under a passing gate,
but it still does not alter controller execution.

The companion `tools/zenograph_autotrader_ranking_stage_summary.py` helper
renders that staging output into human-readable markdown for operator review.

For signed replay governance, `tools/zenograph_autotrader_ranking_review_bundle.py`
emits the current baseline report, gate report, and a markdown review summary
in one non-executing operator bundle. Use `--out-dir` to emit the whole review
pack with default filenames plus a manifest in a single command. If you omit
explicit output paths entirely, it now defaults to a stable campaign directory
under `internal/zenograph_shadow/` using:

- `YYYYMMDDTHHMMSSZ_<run-id>`

You can control that with `--campaign-root`, `--timestamp-utc`, and `--run-id`.
The emitted `manifest.json` now records bundle metadata such as timestamp,
repo git SHA when available, dirty-worktree status, Python/runtime info, and
tool contract versions. It also records per-artifact checksums and byte sizes
for the emitted review files.

Use `tools/zenograph_autotrader_ranking_review_bundle_verify.py` to re-check
that a copied or archived review bundle still matches its manifest.

Use `tools/zenograph_autotrader_ranking_review_campaign_index.py` to list and
summarize recent campaign bundles under `internal/zenograph_shadow/`. It now
supports filtering by `--gate-status`, `--run-id-prefix`, `--git-prefix`,
`--dirty-state`, `--generated-since-utc`, and `--generated-until-utc`.
The generated-time filters use the stable campaign directory timestamp first,
with manifest generation time only as a fallback.
The index summary also includes per-day bundle counts, per-day gate-status
counts, latest gate/block-reason streaks, and first/last-seen block-reason
spans for simple trend review.
It can also emit:
- a flat per-bundle CSV listing with `--csv-out`
- a daily aggregate CSV with `--csv-daily-out`
- a daily block-reason CSV with `--csv-daily-block-reasons-out`

For read-only operator review, `tools/zenograph_autotrader_ranking_review_campaign_report.py`
renders the campaign index into a static HTML report with the same safety
boundary: advisory only, no ranking authority, no execution authority. The
report now includes drilldown links into each bundle's manifest, markdown
review, gate report, baseline report, and bundle README when available. It also
surfaces the latest bundle prominently with its current gate posture and lead
block reason.

Example:

```bash
python3 tools/autotrader_shadow.py \
  --policy-file /tmp/policy.json \
  --receipt-file /tmp/receipt.json \
  --pools-file /tmp/pools.json \
  --current-epoch 5 \
  --intent-deadline 99 \
  --zenograph-enable \
  --zenograph-facts-file /tmp/zenograph_facts.json \
  --pretty
```

The `--zenograph-facts-file` accepts either:

- nested object form: `{"protocol": {"governance_attack_risk": "elevated"}}`
- list form: `{"facts": [{"subject_id": "protocol", "predicate": "governance_attack_risk", "value": "elevated"}]}`

Alternatively, `--zenograph-fact-pack-file` accepts a reviewed and signed
`zenodex/zenograph-fact-pack/v1` bundle. This is the preferred runtime-advisory
path because it carries provenance and approval instead of raw unsigned facts.

Operator tooling:

```bash
python3 tools/zenograph_fact_pack_build.py \
  --pack-name zenograph.pack.example \
  --fact-file /tmp/fact.json \
  --review-record-file /tmp/review.json \
  --signer-privkey 21 \
  --pack-out /tmp/zenograph_fact_pack.json

python3 tools/zenograph_fact_pack_verify.py \
  --pack-file /tmp/zenograph_fact_pack.json \
  --pretty

python3 tools/zenograph_fact_pack_from_store.py \
  --store-root internal/zenograph \
  --pack-name zenograph.pack.from_store \
  --review-record-file /tmp/review.json \
  --signer-privkey 21 \
  --pack-out /tmp/zenograph_fact_pack.json
```

When enabled, the report includes `zenograph_advisory` with:

- active microtheories
- tactic admissibility and block reasons
- selected template id under the symbolic selector
- the unchanged observation packet used for existing shell/KRR logic