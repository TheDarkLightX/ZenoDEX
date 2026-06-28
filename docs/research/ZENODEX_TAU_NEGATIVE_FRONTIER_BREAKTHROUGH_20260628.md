# ZenoDEX Tau Negative-Frontier Breakthrough - 2026-06-28

## Executive Result

Tau now gates an advisory falsifier-campaign scheduler that selects high-severity negative-frontier axes by entropy gain while preserving deterministic replay, AB/CoW work-item coverage, runtime-subset compatibility, and no-authority rails.

Tau admits the research campaign certificate only. Host/kernel verifiers remain authoritative for settlement, oracle updates, governance, balances, and state roots.

## Tau Certificate

- Spec: `src/tau_specs/recommended/negative_frontier_entropy_campaign_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau cases: `11`
- Invalid accepts: `0`

Certificate facts:
- `certificate_active` = `1`
- `bounded_corpus_ok` = `1`
- `entropy_beats_recency_ok` = `1`
- `entropy_not_worse_than_random_ok` = `1`
- `deterministic_replay_ok` = `1`
- `severity_floor_ok` = `1`
- `work_item_1_ab_covered` = `1`
- `work_item_2_cow_covered` = `1`
- `tau_runtime_subset_ok` = `1`
- `negative_controls_pass` = `1`
- `evidence_artifacts_bound` = `1`
- `advisory_model_only` = `1`
- `no_authority_effect` = `1`

## Scheduler Evidence

- Bounded corpus axes: `125`
- Budget: `10`
- Entropy unique families: `14`
- Recency unique families: `12`
- Stable-random unique families: `7`
- Entropy post-schedule nats: `2.518747`
- Recency post-schedule nats: `2.254158`
- Priority floor observed: `50`

Selected axes:
- `identity_registry_drift`
- `serialization_width_aliasing`
- `epoch_split_brain`
- `market_namespace_version_isolation`
- `bounded_advisory_search_envelope`
- `confidential_receipt_attestation_drift`
- `strategy_session_capability_replay`
- `external_state_drift`
- `tau_gate_policy_aliasing`
- `atomicity_partial_side_effect`

## Work Items 1 And 2

### 1. AB Ordering

bounded full-state subset DP with brute-force parity and explicit fallback after 12
The certificate does not claim a compressed Held-Karp state is sound for integer CPMM ordering.
AB n=12 permutation-vs-state-reduction proxy ratio: `812.109375`.

### 2. CoW Matching

uncoupled Hungarian assignment plus bounded coupled-capacity DP evidence
The certificate does not claim arbitrary grouped-capacity CoW matching is polynomial.
CoW n=20 perfect-matching-vs-Hungarian proxy ratio: `304112751022080.0`.

## What Tau Can Do For ZenoDEX

- `src/tau_specs/recommended/negative_frontier_entropy_campaign_certificate_v1.tau`: Turns negative-frontier campaign selection into an executable, fail-closed Tau certificate.
- `src/tau_specs/recommended/solver_portfolio_upgrade_certificate_v1.tau`: Keeps AB ordering and CoW matching upgrades behind parity, scope, performance, fallback, rollback, and no-authority facts.
- `src/tau_specs/recommended/tauspec_ebrm_frontier_selection_certificate_v1.tau`: Ranks high-value Tau specs while requiring AB/CoW coverage, zero invalid accepts, deterministic replay, and profile-budget compliance.

The current Tau runtime profile supports the safe boolean guard surface used here. Arithmetic-heavy checks remain host-computed facts.

## Tau Runtime Frontier

- Latest stream compatibility ok: `True`
- Runtime rule: stream equality/comparison and constant-right multiplication are admitted; stream add/sub are rejected by latest Tau, so profile-specific gates must choose runtime Tau, a host proof flag, or an upstream stream-arithmetic fix

## Tau Negative Cases

| case | ok | primary output |
| --- | --- | ---: |
| `campaign_pass` | `True` | `1` |
| `recency_baseline_reject` | `True` | `0` |
| `random_baseline_reject` | `True` | `0` |
| `determinism_reject` | `True` | `0` |
| `severity_floor_reject` | `True` | `0` |
| `ab_work_item_reject` | `True` | `0` |
| `cow_work_item_reject` | `True` | `0` |
| `tau_runtime_subset_reject` | `True` | `0` |
| `negative_controls_reject` | `True` | `0` |
| `authority_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- The entropy scheduler is advisory and does not prove that selected tasks will find bugs.
- Tau does not compute entropy, matching, DP, CPMM arithmetic, hashes, or timing budgets in this artifact.
- The latest Tau runtime still rejects stream add/sub shapes, so arithmetic-heavy obligations stay host-side as named facts.
- The AB and CoW statements remain within their declared scoped solver surfaces.

## Replay

```bash
python3 tools/zenodex_tau_negative_frontier_breakthrough_20260628.py
python3 tools/zenodex_negative_frontier_entropy_scheduler_20260628.py
python3 tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py
python3 tools/zenodex_tauspec_ebrm_baseline_breakthrough_20260628.py
python3 tools/check_tau_latest_stream_compat.py
```
