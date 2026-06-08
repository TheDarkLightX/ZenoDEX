# ZenoDEX Codebase Complexity Refactor Queue

Date: 2026-06-07

Source command:

```bash
python3 tools/check_complexity_ratchet.py --json
```

This queue is repository-wide across `src/**/*.py`. It ranks functions by
current audit difficulty and consensus or security blast radius. The grade is a
maintainability and reviewability grade, not a claim that the function is
behaviorally incorrect.

## Current Ratchet Snapshot

| Metric | Value |
| --- | ---: |
| Python source files scanned | 430 |
| Functions scanned | 5,687 |
| Functions over complexity 5 | 1,605 |
| Functions over 60 lines | 435 |
| Maximum complexity | 676 |
| Maximum function length | 3,349 lines |

## Refactor Principles

1. Keep behavior stable first. Every extraction should start with golden tests or
   property tests over the current behavior.
2. Split boundary parsing from state changes. Route handlers should parse and
   authorize, then call typed command services.
3. Split validation into named rules. Each rule should have one invariant,
   explicit inputs, and a small regression test suite.
4. Keep telemetry and presentation outside consensus or proof-checking code.
5. Add teeth for each extraction. Mutating a rule, field order, nonce check, or
   proof binding must fail a focused test.

## P0 Refactor Targets

| Rank | Location | Size | Grade | Why It Is Risky | First Extraction |
| ---: | --- | ---: | --- | --- | --- |
| 1 | `src/integration/api_server.py::_Handler._maybe_handle_dex_api` | 676 complexity, 3,349 lines | D | One method mixes routing, auth, JSON parsing, DTO coercion, service calls, and response shaping for many unrelated API families. It is the highest injection and regression surface in the repo. | Continue the route-table extraction. The read-only routes live in `api_server_dex_readonly_routes.py`; exact-out many-pool contract builders, repaired-selected-domain quotes, repaired-advisory quotes, repaired-full-domain certified quotes, bounded-advisory quotes, the default certified-advisory quote, the adaptive liveness quote, the certified-advisory quote, repaired-advisory packet builder, repaired-full-domain certified packet builder, repaired-key-cover packet builder, repaired-key-cover interpretation packet builder, bounded-advisory packet builder, certified-advisory packet builder, replacement-shadow packet builder, default packet builder, bounded-workaround packet builder, oracle contract builder, audited-bounds contract builder, and adaptive-liveness packet builder live in `api_server_exact_out_many_pool_routes.py`; the next slice is exact-out many-pool remaining packet-build and packet-verify routes. |
| 2 | `src/core/settlement_strong_validator.py::_validate_settlement_strong_impl` | 190 complexity, 612 lines | C- | This is a fail-closed value-moving acceptance gate. The logic is conceptually right, but duplicate-ID checks, fill coverage, replay, deltas, events, LP effects, and conservation live in one control flow. | Extract pure rule functions returning `(ok, error)`: `IntentIdRule`, `IncludedIntentRule`, `FillCoverageRule`, `CowPairRule`, `ReplayDeltaRule`, `EventRule`, `ConservationRule`. |
| 3 | `src/integration/dex_snapshot.py::state_from_snapshot` | 126 complexity, 622 lines | C- | Snapshot hydration is consensus-adjacent because bad defaults or weak parsing can create forked local state. Many schema branches share one broad parser. | Split into typed parsers per section: balances, pools, LP, fees, nonces, confidential requests, oracle metadata. Add round-trip tests section by section. |
| 4 | `src/integration/dex_engine.py::apply_ops` | 118 complexity, 549 lines | C- | Operation application is an orchestration choke point. Mixed dispatch and mutation increases the chance that an operation bypasses a guard. | Replace the branch ladder with an `op_type -> apply_*` dispatch table. Each handler should receive validated DTOs and return data-only effects. |
| 5 | `src/integration/autotrader_live.py::prepare_autotrader_live_quote_receipt` | 100 complexity, 1,925 lines | D+ | A large live integration path combines network/config handling, quote construction, proof metadata, and presentation. Advisory code must remain outside verifier authority. | Separate live IO, quote normalization, verifier receipt construction, and UI/report shaping. Add an import-boundary test that verifier modules do not import advisory/live modules. |

## P1 Refactor Targets

| Rank | Location | Size | Grade | Why It Is Risky | First Extraction |
| ---: | --- | ---: | --- | --- | --- |
| 6 | `src/integration/fast_quote_router_v1.py::FastQuoteRouterV1.quote_exact_out_2hop_fast_v1` | 98 complexity, 361 lines | C | Routing math has many edge branches. It should be easy to prove no candidate path uses inconsistent rounding or bounds. | Extract candidate enumeration, candidate scoring, and receipt construction. Reuse the same helpers for exact-in and exact-out. |
| 7 | `src/fire/verifier/proof_tree_cert_v1.py::verify_fire_proof_tree_certificate` | 96 complexity, 239 lines | C | Proof verification needs obvious fail-closed order and anti-self-weakening checks. One large verifier makes missing-field and downgrade paths hard to audit. | Convert to staged checks: schema, digest binding, rule catalog binding, leaf validation, parent aggregation, root binding. Add mutation tests for dropped leaf and downgraded verdict. |
| 8 | `src/integration/tau_gate.py::validate_settlement_swaps` | 87 complexity, 430 lines | C- | Tau gate checks are assurance-critical and can become config mirrors if field-level bindings are not isolated. | Split swap projection, Tau input construction, tool invocation, result parsing, and fallback policy. Add tests that a live swap-field order mutation fails. |
| 9 | `src/core/quote_receipts.py::verify_route_quote_receipt` | 80 complexity, 223 lines | C | Quote receipts are user-facing safety objects. The verifier should make path, slippage, pool snapshot, and hash checks separately visible. | Extract receipt schema check, pool binding check, route math check, and signature/hash check. Add downgrade tests for missing route hop and stale pool root. |
| 10 | `src/fire/verifier/object_package_v1.py::verify_fire_object_package` | 78 complexity, 299 lines | C | FIRE object packages are evidence carriers. Broad verification logic raises fake-green risk when package sections drift. | Use a package verification pipeline with explicit section results and a final aggregator. Add tests that empty required bodies fail. |
| 11 | `src/fire/compiler/fmos_file_v1.py::_verify_fire_math_object_spec_file` | 78 complexity, 163 lines | C | Compiler-side proof metadata can accidentally accept weak specs if every clause is checked inside one branch-heavy function. | Extract schema, theorem statement, dependency digest, and exported artifact checks. |
| 12 | `src/core/split_routing.py::resolve_two_pool_split_search_params` | 78 complexity, 147 lines | C | Split routing is math-sensitive and branch-heavy. Small parameter helpers make boundary tests clearer. | Extract domain validators and default-resolution helpers. Add max, max+1, zero, and impossible-route tests. |
| 13 | `src/core/fhe_sealed_bid_alpha.py::verify_fhe_sealed_bid_alpha_plan` | 78 complexity, 177 lines | C | Confidential-plan verification needs crisp trust labels. Mixed checks can blur privacy, replay, and arithmetic claims. | Split confidentiality claim checks, replay checks, and arithmetic checks. Label each result as host, committee, or math. |
| 14 | `src/integration/zusd_monetary_bridge.py::_apply_one` | 77 complexity, 201 lines | C | zUSD bridge operations are value-moving. A central branch ladder makes fail-closed behavior harder to inspect. | Dispatch by operation type into bounded handlers, each with a no-op-on-reject regression test. |
| 15 | `src/integration/perps_wallet_encrypted_sss_backup.py::evaluate_perps_wallet_encrypted_sss_backup_v1` | 76 complexity, 269 lines | C | Wallet backup evaluation is security-sensitive and combines crypto metadata, policy, and UX results. | Split cryptographic envelope validation from policy classification and display/report output. |

## Next Implementation Slice

Continue with `src/integration/api_server.py::_maybe_handle_dex_api`, but do it
in small route-family PRs. The first safe slice has landed:

1. `src/integration/api_server_dex_readonly_routes.py` handles
   `impact_preview` and `slippage_advice`.
2. `src/integration/api_server_exact_out_many_pool_routes.py` handles the
   exact-out many-pool contract-builder endpoints and
   `quote_exact_out_many_pool_repaired_selected_domain` plus
   `quote_exact_out_many_pool_repaired_advisory` and
   `quote_exact_out_many_pool_repaired_full_domain_certified` and
   `quote_exact_out_many_pool_bounded_advisory` and
   `quote_exact_out_many_pool` and
   `quote_exact_out_many_pool_adaptive` and
   `quote_exact_out_many_pool_certified_advisory` and
   `build_exact_out_many_pool_repaired_advisory_quote_packet` and
   `build_exact_out_many_pool_repaired_full_domain_certified_packet` and
   `build_exact_out_many_pool_repaired_key_cover_packet` and
   `build_exact_out_many_pool_repaired_key_cover_interpretation_packet` and
   `build_exact_out_many_pool_bounded_advisory_quote_packet` and
   `build_exact_out_many_pool_certified_advisory_packet` and
   `build_exact_out_many_pool_repaired_replacement_shadow_packet`,
   `build_exact_out_many_pool_default_packet`, and
   `build_exact_out_many_pool_bounded_workaround_packet`, and
   `build_exact_out_many_pool_oracle_contract`, and
   `build_exact_out_many_pool_audited_bounds_contract`, and
   `build_exact_out_many_pool_adaptive_liveness_packet`.
3. `_maybe_handle_dex_api` remains the dispatcher and response writer.
4. Focused route tests cover success, error mapping, unhandled-path behavior,
   bad integer fields, and pool-parse error precedence.
5. The baseline records the reduced handler complexity and line count.

Next, move `guard_exact_out_many_pool_canonicality` and the remaining exact-out
many-pool packet-build and packet-verify endpoints one family at a time with
mutation tests for auth bypass, malformed integer fields, oversized search
budgets, and bad quote/proof packet receipts.
