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
| Python source files scanned | 450 |
| Functions scanned | 5,976 |
| Functions over complexity 5 | 1,604 |
| Functions over 60 lines | 435 |
| Maximum complexity | 126 |
| Maximum function length | 1,925 lines |

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
| 1 | `src/core/settlement_strong_validator.py::_validate_settlement_strong_impl` | 100 complexity, 421 lines | C | This is a fail-closed value-moving acceptance gate. The preflight/index checks, early quote-binding metadata guard, CREATE_POOL replay helpers, shared pool lookup, swap metadata guards, swap reserve-witness setup, exact-in replay/application, exact-out replay/application, and swap delta synthesis are extracted, but liquidity replay branches, final deltas, events, LP effects, and conservation still live in one control flow. | Continue extracting one replay action family at a time. The next safe slice is ADD_LIQUIDITY field validation, fill matching, balance/LP/reserve application, and delta synthesis, preserving apply-error order and no-op-on-reject behavior. |
| 2 | `src/integration/dex_snapshot.py::state_from_snapshot` | 126 complexity, 622 lines | C- | Snapshot hydration is consensus-adjacent because bad defaults or weak parsing can create forked local state. Many schema branches share one broad parser. | Split into typed parsers per section: balances, pools, LP, fees, nonces, confidential requests, oracle metadata. Add round-trip tests section by section. |
| 3 | `src/integration/dex_engine.py::apply_ops` | 118 complexity, 549 lines | C- | Operation application is an orchestration choke point. Mixed dispatch and mutation increases the chance that an operation bypasses a guard. | Replace the branch ladder with an `op_type -> apply_*` dispatch table. Each handler should receive validated DTOs and return data-only effects. |
| 4 | `src/integration/autotrader_live.py::prepare_autotrader_live_quote_receipt` | 100 complexity, 1,925 lines | D+ | A large live integration path combines network/config handling, quote construction, proof metadata, and presentation. Advisory code must remain outside verifier authority. | Separate live IO, quote normalization, verifier receipt construction, and UI/report shaping. Add an import-boundary test that verifier modules do not import advisory/live modules. |
| 5 | `src/integration/fast_quote_router_v1.py::FastQuoteRouterV1.quote_exact_out_2hop_fast_v1` | 98 complexity, 361 lines | C | Routing math has many edge branches. It should be easy to prove no candidate path uses inconsistent rounding or bounds. | Extract candidate enumeration, candidate scoring, and receipt construction. Reuse the same helpers for exact-in and exact-out. |

## P1 Refactor Targets

| Rank | Location | Size | Grade | Why It Is Risky | First Extraction |
| ---: | --- | ---: | --- | --- | --- |
| 6 | `src/fire/verifier/proof_tree_cert_v1.py::verify_fire_proof_tree_certificate` | 96 complexity, 239 lines | C | Proof verification needs obvious fail-closed order and anti-self-weakening checks. One large verifier makes missing-field and downgrade paths hard to audit. | Convert to staged checks: schema, digest binding, rule catalog binding, leaf validation, parent aggregation, root binding. Add mutation tests for dropped leaf and downgraded verdict. |
| 7 | `src/integration/tau_gate.py::validate_settlement_swaps` | 87 complexity, 430 lines | C- | Tau gate checks are assurance-critical and can become config mirrors if field-level bindings are not isolated. | Split swap projection, Tau input construction, tool invocation, result parsing, and fallback policy. Add tests that a live swap-field order mutation fails. |
| 8 | `src/core/quote_receipts.py::verify_route_quote_receipt` | 80 complexity, 223 lines | C | Quote receipts are user-facing safety objects. The verifier should make path, slippage, pool snapshot, and hash checks separately visible. | Extract receipt schema check, pool binding check, route math check, and signature/hash check. Add downgrade tests for missing route hop and stale pool root. |
| 9 | `src/fire/verifier/object_package_v1.py::verify_fire_object_package` | 78 complexity, 299 lines | C | FIRE object packages are evidence carriers. Broad verification logic raises fake-green risk when package sections drift. | Use a package verification pipeline with explicit section results and a final aggregator. Add tests that empty required bodies fail. |
| 10 | `src/fire/compiler/fmos_file_v1.py::_verify_fire_math_object_spec_file` | 78 complexity, 163 lines | C | Compiler-side proof metadata can accidentally accept weak specs if every clause is checked inside one branch-heavy function. | Extract schema, theorem statement, dependency digest, and exported artifact checks. |
| 11 | `src/core/split_routing.py::resolve_two_pool_split_search_params` | 78 complexity, 147 lines | C | Split routing is math-sensitive and branch-heavy. Small parameter helpers make boundary tests clearer. | Extract domain validators and default-resolution helpers. Add max, max+1, zero, and impossible-route tests. |
| 12 | `src/core/fhe_sealed_bid_alpha.py::verify_fhe_sealed_bid_alpha_plan` | 78 complexity, 177 lines | C | Confidential-plan verification needs crisp trust labels. Mixed checks can blur privacy, replay, and arithmetic claims. | Split confidentiality claim checks, replay checks, and arithmetic checks. Label each result as host, committee, or math. |
| 13 | `src/integration/zusd_monetary_bridge.py::_apply_one` | 77 complexity, 201 lines | C | zUSD bridge operations are value-moving. A central branch ladder makes fail-closed behavior harder to inspect. | Dispatch by operation type into bounded handlers, each with a no-op-on-reject regression test. |
| 14 | `src/integration/perps_wallet_encrypted_sss_backup.py::evaluate_perps_wallet_encrypted_sss_backup_v1` | 76 complexity, 269 lines | C | Wallet backup evaluation is security-sensitive and combines crypto metadata, policy, and UX results. | Split cryptographic envelope validation from policy classification and display/report output. |

## Recent API Dispatcher Burn-Down

`src/integration/api_server.py::_Handler._maybe_handle_dex_api` is now down to
32 complexity and 515 lines. It remains worth simplifying because it still owns
shared parser and response-writer helpers, but it is no longer a top-five
complexity hotspot.

Extracted route helpers now cover:

- Read-only DEX endpoints, quotes, quote receipts, and exact-in route helpers.
- Exact-out certificate, audit, many-pool quote, packet, and contract helpers.
- Settlement value, LP value, spot value, endogenous LP value, feature-extension,
  witness lifecycle, end-to-end certificate, and spot-price helpers.
- Pokayoke swap suggestions.
- Proof-mining status.

Residual API cleanup should move local parser and formatter helpers such as
`_parse_pools`, `_quote_to_dict`, `_exact_out_split_quote_from_dict`, and
`_projected_path_from_exact_out_quote_payload` into shared modules. The next
codebase-wide ROI target is the settlement strong validator.

## Recent Settlement Validator Burn-Down

`src/core/settlement_strong_validator.py::_validate_settlement_strong_impl` is
now down from 190 complexity and 612 lines to 100 complexity and 421 lines.
The extracted preflight/index, quote-binding, and CREATE_POOL replay helpers cover:

- validation mode and protocol-fee configuration;
- duplicate input intent IDs;
- included-intent coverage and duplicate included IDs;
- duplicate and extra fill IDs;
- missing fill details for filled intents;
- fill action mismatches;
- CoW pair indexing through the existing `_validate_cow_pair_index` helper.
- early quote receipt metadata validation before action replay, including
  unsupported non-swap quote bindings, invalid leg indexes, unsanitized transport
  metadata, invalid fingerprints, and disabled snapshot-bound fingerprints.
- CREATE_POOL field extraction and validation, preserving the legacy rejection
  order for missing fields, invalid asset IDs, fee bounds, amount bounds, and
  `created_at`.
- CREATE_POOL kernel replay, duplicate-pool detection, fill matching,
  balance/LP application, expected event construction, and
  balance/reserve/LP delta synthesis.
- shared non-CREATE_POOL pool lookup, preserving missing `pool_id` before
  unknown-pool rejection and before operation-specific field validation.
- swap metadata guards for exact-in and exact-out swaps, preserving asset-field,
  inactive-pool, asset-pair, and quote-pool fingerprint rejection order before
  amount and kernel replay checks.
- matching snapshot-bound quote fingerprints on both exact-in and exact-out swap
  replay paths, plus a fail-closed internal error if swap metadata extraction
  ever returns no result without an explicit rejection reason.
- swap direction and reserve-witness setup for exact-in and exact-out swaps,
  preserving reverse-direction reserve selection and proof-carrying witness
  precedence before amount and fill validation.
- exact-in amount and fill preflight, preserving invalid `amount_in`, invalid
  `min_amount_out`, `amount_in_filled` mismatch, and protocol-fee unsupported
  curve rejection order before kernel replay.
- exact-in quote replay and post-quote validation, preserving kernel error,
  `amount_out_filled` mismatch, slippage, `fee_paid` mismatch, and
  `protocol_fee_paid` mismatch order before balance application.
- exact-in balance application, directional pool reserve mutation, and
  balance/reserve delta synthesis, preserving apply-error behavior before final
  canonical delta comparison.
- exact-out amount/fill preflight, protocol-fee curve guard, quote replay, and
  post-quote validation, preserving field, fill, kernel, slippage, fee, and
  protocol-fee error ordering before balance application.
- exact-out balance application, directional pool reserve mutation, and
  balance/reserve delta synthesis, preserving reverse-direction protocol-fee
  deltas, multi-fill proof-carrying reserve witnesses, and apply-error
  no-mutation behavior.

The public rejection order is pinned by combined-invalid tests in
`tests/core/test_settlement_strong_validator.py`, so moving those checks again
should fail if it changes the legacy error precedence.

This pass also fixed an adjacent CREATE_POOL construction bug in
`src/core/batch_clearing.py`: an explicit `created_at=None` was already admitted
and normalized by the replay validator, but settlement construction emitted
`created_at: None` in the event, causing an `events mismatch vs replay`. The event
now uses the normalized pool timestamp, and the regression checks that the
computed settlement validates.

## Next Implementation Slice

Continue `src/core/settlement_strong_validator.py::_validate_settlement_strong_impl`.
Extract ADD_LIQUIDITY replay next. Keep it staged: first pin invalid field and
fill mismatch precedence, apply-error behavior, LP recipient credit, pool reserve
mutation, and emitted balance/reserve/LP deltas. Then move only the
ADD_LIQUIDITY validation/application/delta block into named helpers before
touching REMOVE_LIQUIDITY.

The API route-family extraction pass has landed in small behavior-preserving
slices:

1. `src/integration/api_server_dex_readonly_routes.py` handles
   `impact_preview` and `slippage_advice`.
2. `src/integration/api_server_quote_routes.py` handles `/api/dex/quote`.
3. `src/integration/api_server_quote_receipt_routes.py` handles
   `/api/dex/verify_quote_receipt`.
4. `src/integration/api_server_exact_in_route_contract_routes.py` handles
   `build_exact_in_route_oracle_contract` and
   `verify_exact_in_route_oracle_contract`.
5. `src/integration/api_server_exact_in_route_common.py` centralizes exact-in
   route request parsing for the extracted exact-in route helpers.
6. `src/integration/api_server_exact_in_route_guard_routes.py` handles
   `guard_exact_in_route_canonicality`.
7. `src/integration/api_server_exact_in_route_quote_routes.py` handles
   `quote_exact_in_route_guarded`.
8. `src/integration/api_server_exact_in_route_packet_routes.py` handles
   `build_exact_in_route_guarded_quote_packet` and
   `verify_exact_in_route_guarded_quote_packet`.
9. `src/integration/api_server_exact_in_route_rank_projection_routes.py` handles
   `build_exact_in_route_rank_projection_packet` and
   `verify_exact_in_route_rank_projection_packet`.
10. `src/integration/api_server_exact_in_route_true_key_routes.py` handles
   `build_exact_in_route_true_key_interpretation_packet` and
   `verify_exact_in_route_true_key_interpretation_packet`.
11. `src/integration/api_server_settlement_spot_value_routes.py` handles
   `build_settlement_spot_value_contract` and
   `verify_settlement_spot_value_contract`.
12. `src/integration/api_server_settlement_lp_value_routes.py` handles
   `build_settlement_lp_value_contract` and
   `verify_settlement_lp_value_contract`.
13. `src/integration/api_server_settlement_value_packet_routes.py` handles
   `build_settlement_value_packet` and `verify_settlement_value_packet`.
14. `src/integration/api_server_settlement_endogenous_lp_value_packet_routes.py`
   handles `build_settlement_endogenous_lp_value_packet` and
   `verify_settlement_endogenous_lp_value_packet`.
15. `src/integration/api_server_settlement_feature_extension_routes.py` handles
   `build_settlement_feature_extension_packet` and
   `verify_settlement_feature_extension_packet`.
16. `src/integration/api_server_exact_out_certificate_routes.py` handles
   `build_exact_out_route_certificate` and `verify_exact_out_route_certificate`.
17. `src/integration/api_server_exact_out_audit_routes.py` handles
   `audit_exact_out_two_pool_canonicality` and
   `audit_exact_out_many_pool_canonicality`.
18. `src/integration/api_server_exact_out_many_pool_routes.py` handles the
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
   `build_exact_out_many_pool_adaptive_liveness_packet`, and
   `guard_exact_out_many_pool_canonicality`, and
   `quote_exact_out_many_pool_guarded`, and
   `build_exact_out_many_pool_guarded_quote_packet`, and
   `verify_exact_out_many_pool_guarded_quote_packet`, and
   `build_exact_out_many_pool_certified_winner_packet`, and
   `verify_exact_out_many_pool_certified_winner_packet`, and all remaining
   `verify_exact_out_many_pool_*packet` endpoints, and all
   `verify_exact_out_many_pool_*contract` endpoints.
19. `src/integration/api_server_settlement_end_to_end_certificate_routes.py`
   handles `build_settlement_end_to_end_certificate_packet` and
   `verify_settlement_end_to_end_certificate_packet`.
20. `src/integration/api_server_settlement_witness_routes.py` handles
   `build_settlement_witness_lifecycle_packet` and
   `verify_settlement_witness_lifecycle_packet`.
21. `src/integration/api_server_settlement_spot_price_routes.py` handles
   `build_settlement_spot_price_packet`, `verify_settlement_spot_price_packet`,
   `build_settlement_spot_price_attestation`, and
   `verify_settlement_spot_price_attestation`.
22. `src/integration/api_server_pokayoke_routes.py` handles
   `pokayoke_swap_suggest` and `pokayoke_swap_suggest_heavy`.
23. `src/integration/api_server_proof_mining_routes.py` handles
   `proof_mining_status`.
24. `_maybe_handle_dex_api` remains the dispatcher and response writer.
25. Focused route tests cover success, error mapping, unhandled-path behavior,
   bad integer fields, and pool-parse error precedence.
26. The baseline records the reduced handler complexity and line count.
