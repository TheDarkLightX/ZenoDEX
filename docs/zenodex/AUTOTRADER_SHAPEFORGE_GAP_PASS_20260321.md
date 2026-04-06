# Autotrader ShapeForge Gap Pass (2026-03-21)

This note records the current ShapeForge posture for the autotrader assurance surface on `main` plus the immediately pending signal/registry foundation PR.

## Current working model

```text
Φ := ⟨
  M = zenodex_shape_reference_v3,
  S = autotrader_admission_submit,
  A = evidence_class_promotion,
  T = make the autotrader workflow honestly promotable from tested shell fragments into replayable bounded contracts and liveness artifacts,
  V = {
    quote_receipt(kind, receipt_hash, quote_epoch),
    signal_packet(source_kind, trust_tier, auth_ok, freshness_ok, binding_ok),
    external_signal(source_id, source_kind, trust_tier, advisory_only),
    source_registry(entry, allowed_trust_tiers, require_auth, require_freshness),
    strategy(strategy_id, template, risk_limits, notional_caps),
    session(session_id, owner, chain_id, valid_from, valid_until),
    capability(enabled, assets, actions, notional_remaining),
    nonce(last_used, requested),
    submit_bundle(intent_set, tx_envelope, signer_binding),
    release(decision_ok, emit_ok, finalize_ok)
  },
  O = {
    build_quote_receipt,
    build_signal_packet,
    validate_external_signal_contract,
    validate_signal_source_registry,
    validate_observation_packet,
    check_signal_provenance,
    check_oracle_freshness,
    check_wallet_capability,
    check_session_binding,
    check_nonce,
    check_submit_bundle,
    compose_live_admission,
    decide,
    emit_finalize
  },
  G = {
    quote_epoch >= 0,
    verified quote receipt required when policy demands it,
    trusted external signals require registry binding,
    stale or unauthenticated signals are rejected,
    session window is contained in strategy window,
    capability scope is no wider than strategy scope,
    nonce is strictly sequential,
    submit bundle and tx envelope are fail-closed,
    kill switch and budget guards remain live-mode vetoes
  },
  Obs = {
    admission_ok / rejection_reason,
    source_registry_ok,
    signal_provenance_ok,
    oracle_fresh_ok,
    session_capability_binding_ok,
    wallet_capability_ok,
    nonce_ok,
    submit_bundle_ok,
    emit_finalize_ok,
    explicit submit or explicit failure
  },
  K = {
    candidate argmax / tie-break key for autotrader decisions,
    canonical receipt hash,
    canonical source_id and strategy_id token domains
  },
  E = evidence map below,
  Gap = gap map below,
  N = {
    tests do not justify global liveness,
    local theorems do not justify end-to-end autotrader correctness,
    unmerged shell code must not be treated as Shape on main,
    temporal learning in Tau is not currently an executable assurance path
  },
  Δ = promote autotrader from fragmented shells into one bounded admission→decision→submit/finalize world model with explicit contracts and finite-trace liveness
⟩
```

## Baseline evidence on `main`

### Proved
- Lean autotrader theorem family is merged:
  - `lean-mathlib/Proofs/ZenoDEXAutoTraderBinaryDecision.lean`
  - `lean-mathlib/Proofs/ZenoDEXAutoTraderDecisionBinding.lean`
  - `lean-mathlib/Proofs/ZenoDEXAutoTraderLiveReleaseCertificate.lean`
  - `lean-mathlib/Proofs/ZenoDEXAutoTraderStageCertificate.lean`
- TLA shadow specs for strict sequencing / envelope safety exist:
  - `formal/tla/AutoTraderNonceGuardShadow.tla`
  - `formal/tla/AutoTraderTxEnvelopeShadow.tla`

### Implemented on `main`
- Route quote receipts with optional `quote_epoch` and fail-closed verification:
  - `src/core/quote_receipts.py`
- Two recommended Tau autotrader guards already landed:
  - `src/tau_specs/recommended/autotrader_nonce_guard_v1.tau`
  - `src/tau_specs/recommended/autotrader_tx_envelope_guard_v1.tau`

### Contract / tested-discovery already landed on `main`
- `src/agents/strategy_ir.py`
- `src/integration/autotrader_signals.py`
- `src/integration/autotrader_signal_registry.py`
- `src/kernels/python/strategy_external_signal_contract_v1_adapter.py`
- `src/kernels/python/strategy_external_signal_source_registry_guard_v1_adapter.py`
- `src/kernels/python/strategy_observation_packet_contract_v1_adapter.py`
- Focused tests:
  - `tests/agents/test_strategy_ir.py`
  - `tests/core/test_strategy_external_signal_contract_v1_adapter.py`
  - `tests/core/test_strategy_external_signal_source_registry_guard_v1_adapter.py`
  - `tests/core/test_strategy_observation_packet_contract_v1_adapter.py`
  - `tests/integration/test_autotrader_signal_registry.py`

## Honest gap map

### Gap 1: no promoted autotrader slice in ShapeForge
The promoted world model currently contains no autotrader slice or autotrader cross-slice invariant. The autotrader surface is therefore present only as scattered proofs, specs, and tests.

### Gap 2: admission contracts are fragmented
The natural admission chain is:
1. quote receipt verification
2. signal packet contract
3. source-registry binding
4. signal provenance
5. oracle freshness
6. wallet capability
7. session capability binding
8. session state
9. nonce
10. submit bundle / tx envelope

Today these are not yet promoted as one typed world-model slice on `main`.

### Gap 3: liveness is missing
Safety fragments exist, but there is no bounded finite-trace liveness artifact for:
- admitted observation packets eventually becoming explicit submit or explicit failure
- accepted nonces eventually being consumed or explicitly rejected
- emit/finalize paths not stalling silently once admission succeeded

### Gap 4: optimization claims are under-specified
The decision theorems on `main` are stronger than the runtime carrier currently merged. The missing bridge is explicit candidate-family completeness / bounded-domain optimality over the emitted candidate set.

### Gap 5: coverage posture must be refreshed against the published 100% baseline
The published acceptance-TCB baseline elsewhere in-tree is `100%` branch coverage. Any refresh after the new autotrader slices should therefore compare against that stronger historical target, not a softer `~99%` proxy. Until the gate is rerun on the new branch set, coverage remains `implemented` / `tested_discovery`, not a refreshed public-assurance claim.

## Promotion targets in order

### 1. Autotrader signal/registry foundation
Status:
- `contract` / `tested_discovery` on `main`

Shape effect:
- makes trusted external signals unrepresentable without an allowlisted registry binding
- upgrades signal admission from ad hoc host behavior into typed packet and registry objects

### 2. Bounded autotrader liveness lane
Target artifact class:
- `contract` plus `tested_discovery`

Goal family:
- `G(valid_observation -> F(submit_ok OR explicit_reject))`
- `G(accepted_nonce -> F(consumed_nonce OR reject_nonce))`
- `G(emit_ready -> F(finalized OR explicit_abort))`

Recommended form:
- finite-trace LTLf micro-kernel in `formal/ltlf/`
- explicit end action
- bounded state variables only

### 3. Candidate completeness / optimization lane
Target artifact class:
- `proved` or at least `contract` + bounded oracle receipts

Needed claims:
- candidate family admitted into decision binding is explicit and finite on the claimed domain
- winner relation uses an explicit total key
- the emitted winner is `argmax/argmin(key, candidates)`
- if completeness over all feasible candidates is too expensive, the bounded domain must be stated explicitly

### 4. Autotrader compose promotion
Target artifact class:
- `contract`

Needed end-to-end slice:
- admission bundle
- submit bundle
- emit/finalize composition
- explicit failure observables

### 5. Coverage refresh
Target artifact class:
- `tested_discovery`

Needed receipt:
- rerun acceptance TCB coverage with dev tooling installed
- compare against prior 99% posture
- identify whether new autotrader shell code reduced any critical file below target

## Recommended next files after `#90`
- `formal/ltlf/autotrader_live_admission_ltlf_v1.yaml`
- `formal/ltlf/autotrader_live_admission_goal_family_v1.json`
- `tests/formal/test_autotrader_live_admission_ltlf.py`

Then:
- candidate-family / completeness note or proof lane for decision binding and emitted candidate sets

## Negative knowledge to preserve
- Do not promote unmerged autotrader shell/controller code as `implemented` on `main`.
- Do not promote Lean decision theorems as end-to-end runtime correctness.
- Do not claim infinite-run liveness from bounded LTLf artifacts.
- Do not treat coverage floors as 100% coverage.
- Do not claim Tau-carried temporal perceptron learning is currently executable in this repo; the current runtime times out on that path.
