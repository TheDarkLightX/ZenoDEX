# Tau Structural-Semantic View

This is a mechanical extraction of recommended Tau control surfaces and output equations.
It is not a human-reviewed semantic contract or an exactness proof.

Execution census: `formal/tau/recommended_execution_census_best.json`
Spec count: `234`

## ab_cow_exact_solver_envelope_v1

- Profile: `proof_gate_or_certificate`
- Rule: `frontier_host_certificate_envelopes`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Control helpers: `ab_ok, cow_ok, fallback_boundary_ok, is1, mode_ok, proof_surface_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> mode_ok(i2[t]:sbf, i3[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> proof_surface_ok(i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i10[t]:sbf, i11[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> fallback_boundary_ok(i8[t...`

## add_liquidity_apply_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i10, i11`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i10[t]:sbf = 1:sbf) && (i11[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32] > { #x00000000 }:bv[32]) && (i4[t]:bv[32] > { #...`

## add_liquidity_ratio_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i9, i10`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i9[t]:sbf = 1:sbf) && (i10[t]:sbf = 1:sbf) && (i3[t]:bv[32] > { #x00000000 }:bv[32]) && (i4[t]:bv[32] > { #x00000000 }:bv[32]) && (i5[t]:bv[32] > { #x00000000 }:bv[32]) && (i6[t]:bv[32] > { #x...`

## arbitrage_bounds_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3, i5`, always clauses `1`
- Control helpers: `arb_bounds_valid, params_ok, profit_ok`
- Data helpers: `depth_ok, input_ok, max_safe_32, profit_bounded, rate_ok, safe_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> profit_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> depth_ok(i1[t]:bv[32], i5[t]:bv[32])) &...`

## argmax_stream_certificate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i5`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Data helpers: `ge_pair`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i5[t]:sbf = 1:sbf) && ge_pair(i1[t]:bv[64], i2[t]:bv[32], i3[t]:bv[64], i4[t]:bv[32])))`

## argmin_stream_certificate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i5`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Data helpers: `le_pair`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i5[t]:sbf = 1:sbf) && le_pair(i1[t]:bv[64], i2[t]:bv[32], i3[t]:bv[64], i4[t]:bv[32])))`

## atomic_batch_commit_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Control helpers: `abort_containment_ok, all_modules_committed`
- Data helpers: `aggregate_commit_consistent`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> all_modules_committed(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> aggregate_commit_consistent(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:s...`

## autotrader_budget_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i6`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Data helpers: `add_no_wrap, budget_step_valid, is_positive_32`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> budget_step_valid(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32], i6[t]:sbf))`

## autotrader_compilation_witness_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `( o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i9[t]:...`

## autotrader_compile_contract_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `( o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i9[t]:...`

## autotrader_emit_finalize_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `i1, i2, i3`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `( o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 0:sbf) || ((i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf)) ) )`

## autotrader_execution_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3, i5, i6, i7, i8, i9`, always clauses `1`
- Control helpers: `execution_guard_ok`
- Data helpers: `cadence_ok, live_orders_ok, monotone_epoch_ok, within_window_ok`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> execution_guard_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:sbf, i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32], i8[t]:bv[32], i9[t]:bv[32]))`

## autotrader_external_signal_source_registry_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i1, i2, i5, i6, i7, i9, i10, i11, i12, i13, i14, i15`, bv inputs `i3, i4, i8`, always clauses `1`
- Control helpers: `advisory_mode_allowed, auth_requirement_ok, freshness_requirement_ok, registry_enabled_ok, registry_entry_found, source_kind_matches, source_registry_ok`
- Data helpers: `trust_tier_allowed`
- Equation surface: extractable `True`, equations `1`, covered outputs `o8`
- Always: `(o8[t]:sbf = 1:sbf <-> source_registry_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:bv[32], i4[t]:bv[32], i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:bv[32], i9[t]:sbf, i10[t]:sbf, i11[t]:sbf, i12[t]:sbf, i13[t]:sbf, i14[t]:sbf, i15[t]:...`

## autotrader_live_admission_bundle_v1

- Profile: `bundle_or_composition`
- Rule: `bundles_and_compositions`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `00000000000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `12`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12`
- Always: `(o1[t]:sbf = 1:sbf <-> (i1[t]:sbf = 1:sbf)) && (o2[t]:sbf = 1:sbf <-> (i2[t]:sbf = 1:sbf)) && (o3[t]:sbf = 1:sbf <-> (i3[t]:sbf = 1:sbf)) && (o4[t]:sbf = 1:sbf <-> (i4[t]:sbf = 1:sbf)) && (o5[t]:sbf = 1:sbf <-> (i5[t]...`

## autotrader_nonce_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> (i3[t]:bv[32] = (i2[t]:bv[32] + { #x00000001 }:bv[32]))) && (o2[t]:sbf = 1:sbf <-> (i1[t]:bv[32] > i2[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> (i1[t]:bv[32] = i3[t]:bv[32])) && (o4[t]:sbf = 1:sbf <...`

## autotrader_observation_packet_contract_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `i3, i4, i5, i6, i7, i8`, bv inputs `i1, i2, i9, i10, i11`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `( o1[t]:sbf = 1:sbf <-> ( ( (i1[t]:bv[32] = { #x00000001 }:bv[32]) && ( (i2[t]:bv[32] = { #x00000002 }:bv[32]) || (i2[t]:bv[32] = { #x00000003 }:bv[32]) ) ) || ( (i1[t]:bv[32] = { #x00000002 }:bv[32]) && (i2[t]:bv[32]...`

## autotrader_oracle_freshness_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `oracle_freshness_guard_ok`
- Data helpers: `freshness_ok, quote_epoch_not_future`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> oracle_freshness_guard_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32]))`

## autotrader_route_economic_sanity_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7`, bv inputs `i8, i9, i10, i11, i12, i13`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `( o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 0:sbf) ) ) && (o2[t]:sbf = 1:sbf <-> (i8...`

## autotrader_session_capability_binding_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0000010`
- Control surface: sbf inputs `i1, i2, i3, i4, i5`, bv inputs `i6, i7, i8, i9`, always clauses `1`
- Equation surface: extractable `True`, equations `7`, covered outputs `o1, o2, o3, o4, o5, o6, o7`
- Always: `(o1[t]:sbf = 1:sbf <-> (i1[t]:sbf = 1:sbf)) && (o2[t]:sbf = 1:sbf <-> (i2[t]:sbf = 1:sbf)) && (o3[t]:sbf = 1:sbf <-> (i3[t]:sbf = 1:sbf)) && (o4[t]:sbf = 1:sbf <-> (i4[t]:sbf = 1:sbf)) && (o5[t]:sbf = 1:sbf <-> (i5[t]...`

## autotrader_session_state_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `000010`
- Control surface: sbf inputs `i1, i2, i3, i4, i5`, bv inputs `i6, i7`, always clauses `1`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> (i1[t]:sbf = 1:sbf)) && (o2[t]:sbf = 1:sbf <-> (i2[t]:sbf = 1:sbf)) && (o3[t]:sbf = 1:sbf <-> (i3[t]:sbf = 1:sbf)) && (o4[t]:sbf = 1:sbf <-> (i4[t]:sbf = 1:sbf)) && ( o5[t]:sbf = 1:sbf <-> ( (i5...`

## autotrader_signal_provenance_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `i3, i4, i5, i6, i7, i8, i9`, bv inputs `i1, i2`, always clauses `1`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> (i1[t]:bv[32] = { #x00000001 }:bv[32])) && (o2[t]:sbf = 1:sbf <-> (i2[t]:bv[32] >= { #x00000002 }:bv[32])) && ( o3[t]:sbf = 1:sbf <-> ( (i9[t]:sbf = 0:sbf) || ( (i3[t]:sbf = 1:sbf) && (i4[t]:sbf...`

## autotrader_submit_bundle_guard_v1

- Profile: `bundle_or_composition`
- Rule: `bundles_and_compositions`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `00011`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `( o1[t]:sbf = 1:sbf <-> ( (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) ) ) && ( o2[t]:sbf = 1:sbf <-> ( (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) ) ) && ( o3[t]:sbf = 1:sbf <-> (i7[t]:sbf = 1:sbf...`

## autotrader_system_compose_v1

- Profile: `bundle_or_composition`
- Rule: `bundles_and_compositions`
- Temporal: `False`
- Execution: `ok` via `spec`
- Observed output signatures: `001`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `( o1[t]:sbf = 1:sbf <-> ( (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i9[t]:sbf = 1:sbf) && (i10[t]...`

## autotrader_tx_envelope_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1111`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `( o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 0:sbf) || ((i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf)) ) ) && ( o2[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 0:sbf) || ((i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf))...`

## autotrader_wallet_capability_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `00110`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6`, bv inputs `i7, i8, i9, i10, i11`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> (i1[t]:sbf = 1:sbf)) && ( o2[t]:sbf = 1:sbf <-> ( (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) ) ) && (o3[t]:sbf = 1:sbf <-> ((...`

## autotrader_wallet_outbound_guard_v1

- Profile: `bundle_or_composition`
- Rule: `autotrader_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `01101`
- Control surface: sbf inputs `i5, i6, i7, i8`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> (i8[t]:sbf = 1:sbf)) && (o2[t]:sbf = 1:sbf <-> (i3[t]:bv[32] = i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> (i1[t]:bv[32] <= i2[t]:bv[32])) && (o4[t]:sbf = 1:sbf <-> ((i5[t]:sbf = 1:sbf) && (i6[t]:s...`

## balance_safety_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Control helpers: `balance_inputs_non_negative`
- Data helpers: `is_non_negative`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> balance_inputs_non_negative(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16], i5[t]:bv[16], i6[t]:bv[16]))`

## balance_transition_v1

- Profile: `multi_limb_word_arithmetic`
- Rule: `multi_limb_arithmetic_specs`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10`, always clauses `1`
- Control helpers: `balance_transition_constraints`
- Data helpers: `add_32, is_non_negative_32, sub_32, value_gte_32`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> balance_transition_constraints(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16], i5[t]:bv[16], i6[t]:bv[16], i7[t]:bv[16], i8[t]:bv[16], i9[t]:bv[16], i10[t]:bv[16]))`

## batch_auction_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `001110`
- Control surface: sbf inputs `i8, i9, i10, i11`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i12, i13, i14, i15, i16`, always clauses `1`
- Control helpers: `all_equal_4_sbf, all_settled_4, batch_auction_ok, batch_valid_base, expiries_ok_4, no_partial_fill, none_settled_4, settlement_atomic_4`
- Data helpers: `batch_id_monotonic, not_expired, price_in_bounds, settlement_aligned_4, volumes_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `((o1[t]:sbf = 1:sbf <-> batch_id_monotonic(i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> expiries_ok_4(i3[t]:bv[64], i4[t]:bv[64], i5[t]:bv[64], i6[t]:bv[64], i7[t]:bv[64])) && (o3[t]:sbf = 1:sbf <-> volumes_...`

## batch_canonical_v1_4

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Data helpers: `is_strictly_increasing_4`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> is_strictly_increasing_4(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64]))`

## batching_all_distinct_4_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:bv[64] != i2[t]:bv[64]) && (i1[t]:bv[64] != i3[t]:bv[64]) && (i1[t]:bv[64] != i4[t]:bv[64]) && (i2[t]:bv[64] != i3[t]:bv[64]) && (i2[t]:bv[64] != i4[t]:bv[64]) && (i3[t]:bv[64] != i4[t]:...`

## batching_executed_sorted_4_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:bv[64] < i2[t]:bv[64]) && (i2[t]:bv[64] < i3[t]:bv[64]) && (i3[t]:bv[64] < i4[t]:bv[64])))`

## batching_left_in_right_4_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((((i1[t]:bv[64] = i5[t]:bv[64]) || (i1[t]:bv[64] = i6[t]:bv[64]) || (i1[t]:bv[64] = i7[t]:bv[64]) || (i1[t]:bv[64] = i8[t]:bv[64])) && ((i2[t]:bv[64] = i5[t]:bv[64]) || (i2[t]:bv[64] = i6[t]:bv...`

## batching_v1_4

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8`, always clauses `1`
- Control helpers: `all_distinct_4, is_member_4`
- Data helpers: `is_strictly_increasing_4`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> (all_distinct_4(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64]) && is_member_4(i5[t]:bv[64], i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64]) && is_member_4(i6[t]:bv[64], i1[t]:bv...`

## batching_v1_5_compact_single_gate

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8`, always clauses `1`
- Control helpers: `all_distinct_4, is_member_4, left_in_right_4`
- Data helpers: `is_strictly_increasing_4`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> (all_distinct_4(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64]) && all_distinct_4(i5[t]:bv[64], i6[t]:bv[64], i7[t]:bv[64], i8[t]:bv[64]) && left_in_right_4(i5[t]:bv[64], i6[t]:bv[64], i...`

## burn_receipt_amount_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `i1`, bv inputs `i2, i3, i4`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i2[t]:bv[32] <= { #x00007FFF }:bv[32]) && (i3[t]:bv[32] <= { #x00007FFF }:bv[32]) && (i4[t]:bv[32] <= { #x00007FFF }:bv[32]) && ( ( (i1[t]:sbf = 0:sbf) && (i2[t]:bv[32] = { #x00000000 }:bv[32...`

## burn_receipt_batch_sum_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `i1`, bv inputs `i2, i3, i4`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i2[t]:bv[32] <= { #x00007FFF }:bv[32]) && (i3[t]:bv[32] <= { #x00007FFF }:bv[32]) && (i4[t]:bv[32] <= { #x0000FFFF }:bv[32]) && ( ( (i1[t]:sbf = 0:sbf) && (i4[t]:bv[32] = i3[t]:bv[32]) ) || (...`

## burn_receipt_replay_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `i1, i2, i3, i4`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( ( (i1[t]:sbf = 0:sbf) || ( (i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) ) ) ) )`

## burn_receipt_supply_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `i1`, bv inputs `i2, i3, i4`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i2[t]:bv[32] <= { #x00007FFF }:bv[32]) && (i3[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i4[t]:bv[32] <= { #x0000FFFF }:bv[32]) && ( ( (i1[t]:sbf = 0:sbf) && (i4[t]:bv[32] = i3[t]:bv[32]) ) || (...`

## circuit_breaker_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0100`
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `circuit_breaker_valid, cooldown_ok, params_ok`
- Data helpers: `deviation_ok_ge, deviation_ok_lt, deviation_within_bounds, max_safe_32, rate_ok, ref_ok, safe_range_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i3[t]:bv[32], i2[t]:bv[32], i1[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> deviation_within_bounds(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> cooldown_ok(i4[t]:sbf)...`

## commit_reveal_binding_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i3, i4, i5, i6`, bv inputs `i1, i2`, always clauses `1`
- Control helpers: `before_deadline, digest_binds, inside_reveal_window, proof_gated_reveal_accepted, reveal_accepted`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> digest_binds(i1[t]:bv[256], i2[t]:bv[256])) && (o2[t]:sbf = 1:sbf <-> inside_reveal_window(i3[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> before_deadline(i4[t]:sbf)) && (o4[t]:sbf = 1:sbf <-> reveal_acce...`

## concentrated_liquidity_range_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `bounds_ok, cl_range_valid, params_ok, ticks_aligned`
- Data helpers: `bounds_ordered, spacing_ok, tick_aligned, width_bounds_ok, width_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> bounds_ok(i1[t]:bv[32], i2[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> ticks_aligned(i1[t]:bv...`

## confidential_extension_live_admission_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) ))`

## cpmm_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, always clauses `1`
- Control helpers: `swap_constraints`
- Data helpers: `fee_bps_valid, is_positive, value_gte`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> swap_constraints(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16], i5[t]:bv[16], i6[t]:bv[16], i7[t]:bv[16], i8[t]:bv[16], i9[t]:bv[16]))`

## cpss_bc_research_scope_certificate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13`, bv inputs `(none)`, always clauses `1`
- Control helpers: `authority_boundary_ok, certificate_ok, falsification_scope_ok, formal_evidence_ok, is1, replay_bundle_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> formal_evidence_ok(i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i7[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> falsification_scope_ok(i6[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf)) && (o3[t]:sbf = 1:sbf <...`

## create_pool_apply_proof_gate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i11, i12`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10`, always clauses `1`
- Data helpers: `min_lp_lock`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i11[t]:sbf = 1:sbf) && (i12[t]:sbf = 1:sbf) && (i1[t]:bv[32] = { #x00000000 }:bv[32]) && (i2[t]:bv[32] = { #x00000000 }:bv[32]) && (i3[t]:bv[32] = { #x00000000 }:bv[32]) && (i4[t]:bv[32] > { #...`

## create_pool_initial_sqrt_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Control helpers: `create_pool_sqrt_ok`
- Data helpers: `lp_minted_ok, min_lp_lock, nonzero_ok, sqrt_witness_ok, u32_max, u32_ok`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> create_pool_sqrt_ok(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64]))`

## cross_module_conservation_consistency_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, bv inputs `(none)`, always clauses `1`
- Control helpers: `per_module_balanced`
- Data helpers: `combined_witness_consistent`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> per_module_balanced(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> combined_witness_consistent(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i7[t]:sbf)) && (o3[t]:sbf = 1:s...`

## disaster_axis_safe_noop_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Control helpers: `no_disaster_axis, safe_noop_valid`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> no_disaster_axis(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> safe_noop_valid(i8[t]:sbf, i9[t]:sbf, i10[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> ((i1[t]...`

## dispute_window_finality_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10`, bv inputs `(none)`, always clauses `1`
- Control helpers: `challenge_clear, dispute_window_ok, epoch_facts_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> epoch_facts_ok(i2[t]:sbf, i5[t]:sbf, i6[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> dispute_window_ok(i3[t]:sbf, i7[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> challenge_clear(i4[t]:sbf, i8[t]:sbf)) && (o4[t]:sbf...`

## emergency_pause_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1010`
- Control surface: sbf inputs `i3, i4, i5`, bv inputs `i1, i2`, always clauses `1`
- Control helpers: `auto_trigger_ok, can_pause, emergency_pause_valid, manual_trigger_ok, oracle_trigger, reserve_trigger`
- Data helpers: `deviation_trigger, threshold_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> auto_trigger_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:sbf, i4[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> manual_trigger_ok(i5[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> can_pause(i1[t]:bv[32], i2[t]:bv[32], i3[t]:s...`

## epoch_monotonic_step_gate_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `True`
- Execution: `missing` via ``
- Control surface: sbf inputs `(none)`, bv inputs `i1`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( ((i1[t-1]:bv[8] = { #x00 }:bv[8]) && (i1[t]:bv[8] = { #x01 }:bv[8])) || ((i1[t-1]:bv[8] = { #x01 }:bv[8]) && (i1[t]:bv[8] = { #x02 }:bv[8])) || ((i1[t-1]:bv[8] = { #x02 }:bv[8]) && (i1[t]:bv[8...`

## fee_accrual_proof_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `fee_calc_ok, fee_proof_valid, params_ok`
- Data helpers: `accrual_ok, fee_calc_lower, fee_calc_upper, max_safe_32, rate_ok, safe_ok, volume_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> fee_calc_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> accrual_ok(i4[t]:bv[32], i5[t]:bv[32], i3[t]:bv[...`

## fee_distribution_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Control helpers: `fee_distribution_ok`
- Data helpers: `conservation_ok, lp_expected, monotonicity_ok, no_wrap_add2, no_wrap_mul60, split_math_ok, treasury_expected`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `((o1[t]:sbf = 1:sbf <-> split_math_ok(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64])) && (o2[t]:sbf = 1:sbf <-> conservation_ok(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64])) && (o3[t]:sbf = 1:sbf <...`

## flash_loan_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0001`
- Control surface: sbf inputs `i1, i2, i3, i4`, bv inputs `(none)`, always clauses `1`
- Control helpers: `borrow_repay_same, flash_loan_safe, flash_pattern_detected, trade_with_borrow`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> borrow_repay_same(i1[t]:sbf, i3[t]:sbf, i4[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> trade_with_borrow(i1[t]:sbf, i2[t]:sbf, i4[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> flash_pattern_detected(i1[t]:sbf, i2[t...`

## frontier_certificate_menu_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Control helpers: `boundary_ok, core_ok, frontier_ok, is1, one_hot3`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> one_hot3(i10[t]:sbf, i11[t]:sbf, i12[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> core_ok(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i9[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> boundary_ok(i7[t]:sbf...`

## governance_multisig_timelock_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17`, bv inputs `i2, i3, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `action_one_hot_ok, governance_action_allowed, policy_binding_ok, proof_gated_governance_action_allowed`
- Data helpers: `threshold_ok, timelock_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> threshold_ok(i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> timelock_ok(i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32], i8[t]:sbf, i9[t]:sbf, i15[t]:sbf)) && (o3[t]:sbf = 1:sbf <...`

## governance_rate_limiter_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `i2, i4`, bv inputs `i1, i3`, always clauses `1`
- Control helpers: `gov_rate_valid, params_ok, window_allows`
- Data helpers: `after_change_ok, current_ok, max_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> current_ok(i1[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> after_change_ok(i1[t]:bv[32], i3[t]:bv[32], i2[t]:sbf)) && (o4[t]:sbf = 1:sbf...`

## governance_timelock_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `True`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `executionvalid, governancesafe, proposalmature`
- Data helpers: `delayelapsed`
- Equation surface: extractable `True`, equations `8`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[0]:sbf = 0:sbf) && (o2[0]:sbf = 0:sbf) && (o3[0]:sbf = 0:sbf) && (o4[0]:sbf = 0:sbf) && (o1[t]:sbf = 1:sbf <-> delayelapsed(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16])) && (o2[t]:sbf = 1:sbf <-> executionvalid(i1[t]...`

## idempotency_window_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i3, i4, i5, i6, i7, i8`, bv inputs `i1, i2`, always clauses `1`
- Control helpers: `fresh_or_idempotent_ok, prior_in_window, proof_gated_idempotency_ok, replay_digest_matches, same_tuple`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> same_tuple(i4[t]:sbf, i5[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> prior_in_window(i3[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> replay_digest_matches(i1[t]:bv[256], i2[t]:bv[256])) && (o4[t]:sbf = 1:sbf <-> f...`

## incident_latch_reset_quorum_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10`, bv inputs `(none)`, always clauses `1`
- Control helpers: `reset_authorized`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> reset_authorized(i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> (((i1[t]:sbf = 1:sbf) || (i2[t]:sbf = 1:sbf)) && !reset_autho...`

## intent_expiry_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `intent_expiry_valid, params_ok`
- Data helpers: `not_expired, timestamps_ok, validity_bounds_ok, validity_in_range`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i5[t]:bv[32], i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> not_expired(i2[t]:bv[32], i1[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> validity_in_range(i5...`

## intent_oneshot_admission_gate_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `True`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = (i1[t]:sbf & (i1[t-1]:sbf)'))`

## isolated_margin_no_cascade_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `2`, covered outputs `o1, o2`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf))) && (o2[t]:sbf = 1:sbf <-> ((o1[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf)))`

## key_rotation_admission_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `2`, covered outputs `o1, o2`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i9[t]:sb...`

## limit_order_bounds_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `i5`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Control helpers: `bounds_ok, limit_order_valid, params_ok`
- Data helpers: `buy_ok, max_safe_32, price_ok, rate_ok, safe_ok, sell_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (price_ok(i1[t]:bv[32]) && price_ok(i2[t]:bv[32]))) && (o3[t]:sbf = 1:sbf <-> bounds_ok(i1[t]:bv[32],...`

## liquidity_utilization_cap_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Control helpers: `params_ok, utilization_valid`
- Data helpers: `cumulative_ok, max_safe_32, pool_ok, rate_ok, safe_ok, single_trade_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> single_trade_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> cumulative_ok(i1[t]:bv[32], i4[t]:bv[32], i2...`

## lp_burn_floor_math_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i7, i8`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32] > { #x00000000 }:bv[32]) && (i4[t]:bv[32] > { #x0...`

## lp_mint_burn_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `i5`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Control helpers: `direction_ok, lp_mint_burn_valid, params_ok, proportion_ok`
- Data helpers: `delta_ok, liquidity_ok, max_safe_32, proportion_lower, proportion_upper, safe_ok, supply_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> proportion_ok(i2[t]:bv[32], i3[t]:bv[32], i1[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> dire...`

## lp_mint_min_of_floors_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i7, i8`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32] > { #x00000000 }:bv[32]) && (i4[t]:bv[32] > { #x0...`

## m6_global_value_certificate_closure_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21`, bv inputs `(none)`, always clauses `1`
- Control helpers: `durability_and_effect_safety, is1, lifecycle_and_mediation_safety, semantic_value_safety`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> semantic_value_safety(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> durability_and_effect_safety(i11[t]:sbf, i12[...`

## m6_substrate_disposition_gate_v1

- Profile: `exact_combinational_guard`
- Rule: `m6_substrate_profile_and_disposition_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `2`, covered outputs `o1, o2`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i12[t]:sbf = 1:sbf) && (i13[t]:sbf = 1:sbf) && (i14[t]:sbf = 1:sbf) && (((i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 0:sbf) && (i4[t]:sbf = 0:sbf)) || ((i2[t]:sbf = 0:sbf) && (i3[t]:sbf = 1:sbf) && (...`

## m6_tau_substrate_profile_gate_v1

- Profile: `exact_combinational_guard`
- Rule: `m6_substrate_profile_and_disposition_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 0:sbf) && (i3[t]:sbf = 0:sbf) && (i4[t]:sbf = 0:sbf) && (i5[t]:sbf = 0:sbf) && (i6[t]:sbf = 0:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i9[t]:s...`

## m6_writer_activate_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `m6_writer_transition_guards`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 0:sbf) && (i2[t]:sbf = 0:sbf) && (i3[t]:sbf = 1:sbf) && (i6[t]:sbf = 0:sbf) && (i10[t]:sbf = 1:sbf) && (i11[t]:sbf = 1:sbf) && (i12[t]:sbf = 1:sbf) && (i13[t]:sbf = 1:sbf) && (i14...`

## m6_writer_emergency_failover_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `m6_writer_transition_guards`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 0:sbf) && (i3[t]:sbf = 0:sbf) && (i4[t]:sbf = 0:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 0:sbf) && (i7[t]:sbf = 0:sbf) && (i8[t]:sbf = 1:sbf) && (i9[t]:s...`

## m6_writer_quiesce_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `m6_writer_transition_guards`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i3[t]:sbf = 0:sbf) && (i4[t]:sbf = 0:sbf) && (i5[t]:sbf = 0:sbf) && (i6[t]:sbf = 1:sbf) && (i10[t]:sbf = 1:sbf) && (i11[t]:sbf = 1:sbf) && (i12[t]:sbf = 1:sbf) && (i13[t]:sbf = 1:sbf) && (i14...`

## m6_writer_steady_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `m6_writer_transition_guards`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i11[t]:sbf = 1:sbf) && (i12[t]:sbf = 1:sbf) && (i13[t]:sbf = 1:sbf) && (i14[t]:sbf = 1:sbf) && (i15[t]:sbf = 1:sbf) && (i16[t]:sbf = 1:sbf) && (((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 0:sbf) && ...`

## mev_batch_atomic_replay_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `2`, covered outputs `o1, o2`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i9[t]:sb...`

## mev_protection_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `mev_safe, params_ok`
- Data helpers: `base_ok, delay_ok, max_safe_32, priority_ok, rate_ok, safe_range_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> priority_ok(i1[t]:bv[32], i2[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> delay_ok(i3[t]:bv[32], i5[t]:bv[32...`

## nonce_manager_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2`, always clauses `1`
- Control helpers: `nonce_manager_ok`
- Data helpers: `no_overflow, nonce_gap_bounded, nonce_monotonic`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> nonce_manager_ok(i1[t]:bv[32], i2[t]:bv[32]))`

## nonce_replay_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `seed_disputed_specs`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `nonce_replay_valid, nonce_sequential, params_ok`
- Data helpers: `expected_ok, nonce_fresh`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> nonce_fresh(i1[t]:bv[32], i2[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> nonce_sequential(i1[t]:bv[32], i3[t]:bv[32])) &&...`

## optimal_choice_certificate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i7`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Control helpers: `cert_ok, idx_range_ok, minimal_ok`
- Data helpers: `binding_key_ok, idx0, idx1, idx2, idx3, le_pair`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i7[t]:sbf = 1:sbf) && cert_ok(i1[t]:bv[32], i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64], i5[t]:bv[64], i6[t]:bv[64])))`

## optimizer_audited_bounds_liveness_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7`, bv inputs `(none)`, always clauses `1`
- Control helpers: `audited_bounds_contract_ok, budget_facts_ok, public_outcome_explicit`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> budget_facts_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> public_outcome_explicit(i6[t]:sbf, i7[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> audited_bounds_contract...`

## optimizer_audited_bounds_liveness_v2

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14`, bv inputs `(none)`, always clauses `1`
- Control helpers: `adaptive_liveness_ok, budget_facts_ok, no_spurious_failure, outcome_total`
- Data helpers: `attempt_order_ok, failure_total, success_replayable`
- Equation surface: extractable `True`, equations `7`, covered outputs `o1, o2, o3, o4, o5, o6, o7`
- Always: `(o1[t]:sbf = 1:sbf <-> budget_facts_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> attempt_order_ok(i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> outcome_...`

## optimizer_quotient_certificate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14`, bv inputs `(none)`, always clauses `1`
- Control helpers: `boundary_ok, core_ok, is1, mode_ab_ok, mode_cow_ok, mode_route_ok, one_hot3`
- Equation surface: extractable `True`, equations `8`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8`
- Always: `(o1[t]:sbf = 1:sbf <-> one_hot3(i12[t]:sbf, i13[t]:sbf, i14[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> core_ok(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i11[t]:sbf)) && (o3[t]:sbf = 1:sbf <-...`

## oracle_bounded_move_gate_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Data helpers: `bounded_move`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> bounded_move(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32]))`

## oracle_committee_commit_admission_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i11, i12, i13, i14, i15, i16, i17`, bv inputs `i2, i3, i4, i5, i6, i7, i8, i9, i10`, always clauses `1`
- Control helpers: `authority_ok, oracle_commit_admissible, proof_gated_oracle_commit_admissible`
- Data helpers: `fault_budget_ok, price_envelope_ok, quorum_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> quorum_ok(i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> fault_budget_ok(i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32], i8[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> price_envelope_o...`

## oracle_epoch_equivocation_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `2`, covered outputs `o1, o2`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf) && (i9[t]:sb...`

## oracle_freshness_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0100`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `oracle_fresh_valid, params_ok`
- Data helpers: `freshness_ok, staleness_ok, timestamp_order_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> timestamp_order_ok(i1[t]:bv[32], i2[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> (params_ok(i1[t]:bv[32], i2[t]:bv[32], i3...`

## oracle_freshness_v2

- Profile: `exact_combinational_guard`
- Rule: `seed_disputed_specs`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0000`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `oracle_v2_valid, params_ok`
- Data helpers: `freshness_ok, jump_bounded, jump_ok, max_safe_32, monotonic_ok, order_ok, staleness_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i3[t]:bv[32], i4[t]:bv[32], i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (params_ok(i3[t]:bv[32], i4[t]:bv[32], i1[t]:bv[32], i2[t]:bv[32]) && freshness_ok(i1[t]:bv[32], i2[t...`

## oracle_polytope_frontier_envelope_v1

- Profile: `proof_gate_or_certificate`
- Rule: `frontier_host_certificate_envelopes`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Control helpers: `authority_ok, external_assumptions_ok, interval_feasible_ok, is1, oracle_ok, parity_boundary_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> interval_feasible_ok(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> parity_boundary_ok(i6[t]:sbf, i7[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> external_assumptions_ok(i8[t]:sbf,...`

## oracle_sustained_freshness_2epoch_gate_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `True`
- Execution: `missing` via ``
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3`, always clauses `1`
- Data helpers: `fresh, quote_not_future`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i4[t]:sbf = 1:sbf) && (i4[t-1]:sbf = 1:sbf) && fresh(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32]) && fresh(i1[t-1]:bv[32], i2[t-1]:bv[32], i3[t-1]:bv[32]) ))`

## order_route_decision_table_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `(none)`, bv inputs `i1`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> (i1[t]:bv[8] <= { #x03 }:bv[8])) && (o2[t]:sbf = 1:sbf <-> (i1[t]:bv[8] = { #x00 }:bv[8])) && (o3[t]:sbf = 1:sbf <-> (i1[t]:bv[8] = { #x01 }:bv[8])) && (o4[t]:sbf = 1:sbf <-> (i1[t]:bv[8] = { #x...`

## parameter_bounds_registry_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1111`
- Control surface: sbf inputs `i5`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `param_bounds_valid`
- Data helpers: `bounds_valid, bps_ok, value_in_range`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> bounds_valid(i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> value_in_range(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> bps_ok(i1[t]:bv[32], i5[t]:sbf)) && (o4[t]...`

## parameter_registry_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `o1 output non-integer value: "x1'"`
- Control surface: sbf inputs `i1, i2`, bv inputs `i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24`, always clauses `1`
- Control helpers: `gate_ok`
- Data helpers: `apply_param`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> gate_ok(i1[t]:sbf, i2[t]:sbf)) && apply_param(o1[t], i3[t]:bv[16], i4[t]:bv[16], o2[t]) && apply_param(o1[t], i5[t]:bv[16], i6[t]:bv[16], o3[t]) && apply_param(o1[t], i7[t]:bv[16], i8[t]:bv[16],...`

## parameter_registry_v2

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `000000000000`
- Control surface: sbf inputs `i1, i2, i14, i15`, bv inputs `i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13`, always clauses `1`
- Equation surface: extractable `True`, equations `12`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12`
- Always: `(o1[t]:sbf = i1[t]:sbf & i2[t]:sbf & i14[t]:sbf & i15[t]:sbf) && (o2[t]:bv[16] = i3[t]:bv[16]) && (o3[t]:bv[16] = i4[t]:bv[16]) && (o4[t]:bv[16] = i5[t]:bv[16]) && (o5[t]:bv[16] = i6[t]:bv[16]) && (o6[t]:bv[16] = i7[t...`

## partial_fill_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `params_ok, partial_fill_valid`
- Data helpers: `fill_ok, max_safe_32, order_ok, rate_ok, remaining_ok, safe_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> fill_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> remaining_ok(i4[t]:bv[32], i5[t]:bv[32])) && (o4[t]:...`

## payout_template_age_replay_envelope_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Control helpers: `age_window_ok, payout_binding_ok, replay_ok, timestamp_source_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> timestamp_source_ok(i2[t]:sbf, i3[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> (timestamp_source_ok(i2[t]:sbf, i3[t]:sbf) && (i4[t]:sbf = 1:sbf))) && (o3[t]:sbf = 1:sbf <-> replay_ok(i5[t]:sbf, i6[t]:sbf)...`

## perp_account_net_exposure_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1110`
- Control surface: sbf inputs `i5, i6`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Control helpers: `exposure_safe, proof_gated_exposure_safe`
- Data helpers: `gross_exposure_ok, net_exposure_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> net_exposure_ok(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64])) && (o2[t]:sbf = 1:sbf <-> gross_exposure_ok(i1[t]:bv[64], i2[t]:bv[64], i4[t]:bv[64])) && (o3[t]:sbf = 1:sbf <-> exposure_safe(i1[t]:bv...`

## perp_adl_activation_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1110`
- Control surface: sbf inputs `i1, i2, i7, i8`, bv inputs `i3, i4, i5, i6`, always clauses `1`
- Control helpers: `adl_activation_safe, proof_gated_adl_activation_safe`
- Data helpers: `adl_precondition_ok, adl_tier_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> adl_precondition_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> adl_tier_ok(i5[t]:bv[32], i6[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> adl_activation_safe(i1[t]:sbf,...`

## perp_bounty_shock_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0001`
- Control surface: sbf inputs `i1`, bv inputs `i2, i3, i4, i5`, always clauses `1`
- Control helpers: `any_bounty_shock, bounty_threshold_decrease_shock, params_update_safe, penalty_increase_shock`
- Data helpers: `bounty_threshold_decrease, penalty_increase`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> penalty_increase_shock(i1[t]:sbf, i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> bounty_threshold_decrease_shock(i1[t]:sbf, i4[t]:bv[32], i5[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> any_bou...`

## perp_cross_margin_health_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `111110`
- Control surface: sbf inputs `i1, i8, i9`, bv inputs `i2, i3, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `account_health_ok, proof_gated_account_health_ok`
- Data helpers: `init_headroom_ok, liabilities_covered, maint_headroom_ok, pnl_bound_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> liabilities_covered(i2[t]:bv[64], i3[t]:bv[64])) && (o2[t]:sbf = 1:sbf <-> init_headroom_ok(i2[t]:bv[64], i3[t]:bv[64], i4[t]:bv[64])) && (o3[t]:sbf = 1:sbf <-> maint_headroom_ok(i2[t]:bv[64], i...`

## perp_funding_accumulator_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1110`
- Control surface: sbf inputs `i4, i5`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `accumulator_safe, proof_gated_accumulator_safe`
- Data helpers: `monotone_ok, step_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> monotone_ok(i1[t]:bv[64], i2[t]:bv[64])) && (o2[t]:sbf = 1:sbf <-> step_ok(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64])) && (o3[t]:sbf = 1:sbf <-> accumulator_safe(i1[t]:bv[64], i2[t]:bv[64], i3[t]...`

## perp_funding_velocity_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11110`
- Control surface: sbf inputs `i5, i8, i9`, bv inputs `i1, i2, i3, i4, i6, i7`, always clauses `1`
- Control helpers: `funding_update_safe, proof_gated_funding_update_safe`
- Data helpers: `funding_cap_ok, funding_step_ok, interval_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> funding_cap_ok(i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> funding_step_ok(i1[t]:bv[32], i2[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> interval_ok(i5[t]:sbf, i6[t]:bv[32], i7...`

## perp_latency_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11110`
- Control surface: sbf inputs `i6, i7`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `latency_safe, proof_gated_latency_safe`
- Data helpers: `latency_skew_ok, oracle_latency_ok, sequencer_latency_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> sequencer_latency_ok(i1[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> oracle_latency_ok(i2[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> latency_skew_ok(i1[t]:bv[32], i2[t]:bv[32], i...`

## perp_liquidation_auction_slippage_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11110`
- Control surface: sbf inputs `i7, i8`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> (i3[t]:bv[32] <= i1[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> ((i5[t]:bv[32] <= i6[t]:bv[32]) && (i4[t]:bv[32] >= i5[t]:bv[32]) && (i4[t]:bv[32] <= i6[t]:bv[32]))) && (o3[t]:sbf = 1:sbf <-> ((i1[t]:...`

## perp_liquidation_oracle_sanity_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8`, bv inputs `(none)`, always clauses `1`
- Control helpers: `liquidation_oracle_sanity_safe, liquidation_preconditions_ok, oracle_ready, proof_gated_liquidation_oracle_sanity_safe`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> oracle_ready(i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> liquidation_preconditions_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf)) && (o3[t]:sbf ...`

## perp_liquidation_queue_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11110`
- Control surface: sbf inputs `i7, i8`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Control helpers: `liquidation_queue_safe, proof_gated_liquidation_queue_safe`
- Data helpers: `block_rate_ok, insurance_floor_ok, queue_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> queue_ok(i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> block_rate_ok(i3[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> insurance_floor_ok(i5[t]:bv[32], i6[t]:bv[32])) && (o4[t]:sbf...`

## perp_mark_twap_spread_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11110`
- Control surface: sbf inputs `i7, i8`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Control helpers: `mark_twap_gap_ok, pricing_safe, proof_gated_pricing_safe`
- Data helpers: `book_order_ok, spread_ok, within_gap`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> mark_twap_gap_ok(i1[t]:bv[32], i2[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> book_order_ok(i3[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> spread_ok(i3[t]:bv[32], i4[t]:bv[32], i...`

## perp_market_param_velocity_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1110`
- Control surface: sbf inputs `i1, i2, i6, i7, i8, i9`, bv inputs `i3, i4, i5`, always clauses `1`
- Control helpers: `param_velocity_safe, proof_gated_param_velocity_safe`
- Data helpers: `abs_delta_ok, open_position_direction_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> abs_delta_ok(i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> open_position_direction_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:bv[32], i4[t]:bv[32], i6[t]:sbf, i7[t]:sbf)) && (o3[t]:sb...`

## perp_open_interest_delta_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1110`
- Control surface: sbf inputs `i1, i6, i7`, bv inputs `i2, i3, i4, i5`, always clauses `1`
- Control helpers: `oi_update_safe, proof_gated_oi_update_safe`
- Data helpers: `oi_cap_ok, within_delta`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> within_delta(i3[t]:bv[32], i2[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> oi_cap_ok(i3[t]:bv[32], i5[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> oi_update_safe(i1[t]:sbf, i2[t]:bv[32], i3[t]:b...`

## perp_oracle_quorum_median_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `spec`
- Observed output signatures: `11110`
- Control surface: sbf inputs `i7, i8`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:bv[32] <= i2[t]:bv[32]) && (i2[t]:bv[32] <= i3[t]:bv[32]))) && (o2[t]:sbf = 1:sbf <-> ((i1[t]:bv[32] <= i3[t]:bv[32]) && ((i3[t]:bv[32] - i1[t]:bv[32]) <= i5[t]:bv[32]))) && (o3[t]:sbf =...`

## perp_order_rate_limit_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11111`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `order_rate_limit_safe`
- Data helpers: `cancels_ok, orders_ok, replaces_ok, total_ops_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> orders_ok(i1[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> cancels_ok(i2[t]:bv[32], i5[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> replaces_ok(i3[t]:bv[32], i6[t]:bv[32])) && (o4[t]:sbf = 1:sbf ...`

## perp_position_tier_leverage_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1111`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8`, always clauses `1`
- Control helpers: `in_supported_tier, position_guard_ok`
- Data helpers: `in_tier1, in_tier2, in_tier3, leverage_ok, tiers_monotone`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> tiers_monotone(i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> in_supported_tier(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> leverage_...`

## perp_reduce_only_transition_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `110`
- Control surface: sbf inputs `i1, i4, i5`, bv inputs `i2, i3`, always clauses `1`
- Control helpers: `proof_gated_transition_safe, transition_safe`
- Data helpers: `reduction_ok`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> reduction_ok(i1[t]:sbf, i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> transition_safe(i1[t]:sbf, i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> proof_gated_transition_safe(i1[t]...`

## perp_risk_envelope_proof_gate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11111111110`
- Control surface: sbf inputs `i13, i14, i15, i16, i17`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i18, i19, i20, i21, i22`, always clauses `1`
- Equation surface: extractable `True`, equations `11`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11`
- Always: `(o1[t]:sbf = 1:sbf <-> ((((i1[t]:bv[32] >= i2[t]:bv[32]) && ((i1[t]:bv[32] - i2[t]:bv[32]) <= i20[t]:bv[32])) || ((i1[t]:bv[32] < i2[t]:bv[32]) && ((i2[t]:bv[32] - i1[t]:bv[32]) <= i20[t]:bv[32]))))) && (o2[t]:sbf = 1...`

## perp_settlement_batch_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11110`
- Control surface: sbf inputs `i6, i7`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `proof_gated_settlement_batch_safe, settlement_batch_safe`
- Data helpers: `batch_payout_cap_ok, batch_size_ok, insurance_cover_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> batch_size_ok(i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> batch_payout_cap_ok(i3[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> insurance_cover_ok(i3[t]:bv[32], i5[t]:bv[32])) &&...`

## perp_tau_ingress_schema_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Control helpers: `action_selection_ok, auth_bundle_ok, auth_mode_selected_ok, ingress_preconditions_ok, ingress_schema_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> action_selection_ok(i5[t]:sbf, i6[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> auth_bundle_ok(i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> ingress_preconditions_ok(i1[t]:sbf, i2...`

## perp_withdraw_buffer_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `perp_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `11110`
- Control surface: sbf inputs `i6, i7`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `proof_gated_withdraw_safe, withdraw_safe`
- Data helpers: `buffer_respected, epoch_cap_ok, final_balance_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> epoch_cap_ok(i2[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> final_balance_ok(i1[t]:bv[32], i2[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> buffer_respected(i1[t]:bv[32], i2[t]:bv[...`

## pool_params_binding_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i3, i4, i5, i6, i7`, bv inputs `i1, i2`, always clauses `1`
- Data helpers: `curve_code_ok, fee_ok`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i7[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && fee_ok(i1[t]:bv[32]) && curve_code_ok(i2[t]:bv[32])))`

## position_limit_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `params_ok, position_valid`
- Data helpers: `max_safe_32, pool_ok, position_within_limit, rate_ok, safe_range_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i2[t]:bv[32], i1[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> pool_ok(i2[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> position_within_limit(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) &...`

## price_band_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `params_ok, price_band_valid`
- Data helpers: `lower_bound_ok, max_safe_32, max_safe_32_2x, price_ok, rate_ok, safe_ok, upper_bound_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> upper_bound_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> lower_bound_ok(i1[t]:bv[32], i2...`

## price_impact_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3`, always clauses `1`
- Data helpers: `impact_ok, max_safe_32, pos_ok, rate_ok, safe_ok`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i4[t]:sbf = 1:sbf) && impact_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])))`

## proof_mining_payout_replay_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15`, bv inputs `(none)`, always clauses `1`
- Control helpers: `deterministic_generation_ok, historical_replay_ok, immediate_replay_ok, payout_allowed, proof_context_ok, replay_frontier_ok, reward_budget_ok`
- Equation surface: extractable `True`, equations `7`, covered outputs `o1, o2, o3, o4, o5, o6, o7`
- Always: `(o1[t]:sbf = 1:sbf <-> proof_context_ok(i2[t]:sbf, i3[t]:sbf, i6[t]:sbf, i7[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> replay_frontier_ok(i4[t]:sbf, i5[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> reward_budget_ok(i8[t]:sbf, i9[t]:sbf)...`

## proof_mining_slot_batch_certificate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13`, bv inputs `(none)`, always clauses `1`
- Control helpers: `baseline_comparison_ok, exact_certificate_ok, is1, mode_ok, safety_rail_ok, slot_batch_certificate_ok, structural_scope_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> mode_ok(i1[t]:sbf, i2[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> structural_scope_ok(i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> exact_certificate_ok(i7[t]:sbf, i8[t]:sbf, i9[...`

## proposal_lifecycle_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `i3, i4`, bv inputs `i1, i2`, always clauses `1`
- Control helpers: `active_to_passed_ok, conditions_met, from_active_ok, from_draft_ok, from_passed_ok, is_terminal, lifecycle_valid, passed_to_executed_ok, transition_allowed`
- Data helpers: `state_active, state_cancelled, state_draft, state_executed, state_failed, state_passed, state_valid`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> (state_valid(i1[t]:bv[16]) && state_valid(i2[t]:bv[16]))) && (o2[t]:sbf = 1:sbf <-> transition_allowed(i1[t]:bv[16], i2[t]:bv[16])) && (o3[t]:sbf = 1:sbf <-> conditions_met(i1[t]:bv[16], i2[t]:b...`

## proposal_quorum_floor_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `params_ok, quorum_floor_valid`
- Data helpers: `max_safe_32, participation_met, quorum_met, rate_ok, safe_ok, supply_ok, votes_safe_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i3[t]:bv[32], i4[t]:bv[32], i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> quorum_met(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> partici...`

## protocol_fee_cap_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `spec`
- Observed output signatures: `1111`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `protocol_fee_valid`
- Data helpers: `absolute_max_fee, cap_ok, current_ok, extraction_ok, proposed_ok, rate_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> current_ok(i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> proposed_ok(i3[t]:bv[32], i2[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> extraction_ok(i4[t]:bv[32], i5[t]:bv[32])) && (o4[t]:sbf = 1:...`

## protocol_fee_floor_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `protocol_fee_ok`
- Data helpers: `floor_bounds_ok, max_safe_64, rate_ok, safe_ok`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> protocol_fee_ok(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64]))`

## protocol_token_distribution_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15`, bv inputs `(none)`, always clauses `1`
- Control helpers: `flag_ok`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( flag_ok(i1[t]:sbf) && flag_ok(i2[t]:sbf) && flag_ok(i3[t]:sbf) && flag_ok(i4[t]:sbf) && flag_ok(i5[t]:sbf) && flag_ok(i6[t]:sbf) && flag_ok(i7[t]:sbf) && flag_ok(i8[t]:sbf) && flag_ok(i9[t]:sb...`

## protocol_token_policy_v1

- Profile: `multi_limb_word_arithmetic`
- Rule: `multi_limb_arithmetic_specs`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `i15, i16, i17`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14`, always clauses `1`
- Control helpers: `one_hot_3, token_ok`
- Data helpers: `add_32, burn_ok, burn_valid, is_positive_32, mint_valid, sub_32, supply_dec_by_amount, supply_eq, supply_inc_by_amount, transfer_ok, transfer_valid, underflow_ok, value_gte_32`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> token_ok()) && (o2[t]:sbf = 1:sbf <-> underflow_ok()) && (o3[t]:sbf = 1:sbf <-> (token_ok() && underflow_ok()))`

## protocol_token_underflow_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `i15, i17`, bv inputs `i1, i2, i5, i6, i7, i8`, always clauses `1`
- Data helpers: `burn_ok, transfer_ok, underflow_ok, value_gte_32`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> underflow_ok())`

## protocol_token_v1

- Profile: `multi_limb_word_arithmetic`
- Rule: `multi_limb_arithmetic_specs`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `i15, i16, i17`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14`, always clauses `1`
- Control helpers: `one_hot_3`
- Data helpers: `add_32, burn_valid, is_positive_32, is_zero_32, mint_valid, sub_32, supply_dec_by_amount, supply_eq, supply_inc_by_amount, transfer_valid`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((one_hot_3(i15[t]:sbf, i16[t]:sbf, i17[t]:sbf) = 1:sbf) && (((i15[t]:sbf = 1:sbf) && transfer_valid()) || ((i16[t]:sbf = 1:sbf) && mint_valid()) || ((i17[t]:sbf = 1:sbf) && burn_valid()))))`

## protocol_token_v2

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i8, i9, i10`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `one_hot_3`
- Data helpers: `safe_u32`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( safe_u32(i1[t]:bv[32]) && safe_u32(i2[t]:bv[32]) && safe_u32(i3[t]:bv[32]) && safe_u32(i4[t]:bv[32]) && safe_u32(i5[t]:bv[32]) && safe_u32(i6[t]:bv[32]) && safe_u32(i7[t]:bv[32]) && one_hot_3(...`

## protocol_token_v3

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i8, i9, i10`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `one_hot_3`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( one_hot_3(i8[t]:sbf, i9[t]:sbf, i10[t]:sbf) && (i4[t]:bv[16] > { #x0000 }:bv[16]) && ((i8[t]:sbf = 0:sbf) || ( (i1[t]:bv[16] >= i4[t]:bv[16]) && (i5[t]:bv[16] = (i1[t]:bv[16] - i4[t]:bv[16])) ...`

## public_testnet_node_admission_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13`, bv inputs `(none)`, always clauses `1`
- Control helpers: `chain_binding_ok, peer_capability_subset_ok, runtime_profile_ok, service_identity_ok`
- Equation surface: extractable `True`, equations `7`, covered outputs `o1, o2, o3, o4, o5, o6, o7`
- Always: `(o1[t]:sbf = 1:sbf <-> chain_binding_ok(i2[t]:sbf, i3[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> runtime_profile_ok(i4[t]:sbf, i5[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> peer_capability_subset_ok(i6[t]:sbf, i7[t]:sbf)) && (o4[t]:s...`

## quiet_window_request_gate_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `True`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = (i1[t]:sbf & (i1[t-1]:sbf)' & (i1[t-2]:sbf)'))`

## quorum_validator_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Control helpers: `params_ok, quorum_valid`
- Data helpers: `max_safe_32, quorum_met, rate_ok, safe_range_ok, supply_ok, total_votes, votes_safe_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i4[t]:bv[32], i3[t]:bv[32], i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (total_votes(i1[t]:bv[32], i2[t]:bv[32]) > { #x00000000 }:bv[32])) && (o3[t]:sbf = 1:sbf <-> quorum_m...`

## rate_limiter_v1

- Profile: `exact_combinational_guard`
- Rule: `seed_disputed_specs`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0100`
- Control surface: sbf inputs `i3`, bv inputs `i1, i2`, always clauses `1`
- Control helpers: `rate_limit_satisfied, window_reset`
- Data helpers: `count_within_limit, limit_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> limit_ok(i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> count_within_limit(i1[t]:bv[32], i2[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> window_reset(i3[t]:sbf)) && (o4[t]:sbf = 1:sbf <-> rate_limit_satisfie...`

## release_artifact_manifest_binding_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14`, bv inputs `(none)`, always clauses `1`
- Control helpers: `artifact_hashes_bound, ci_evidence_ok, release_posture_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> artifact_hashes_bound(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> ci_evidence_ok(i6[t]:sbf, i7[t]:sbf, i8[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> release_posture_ok(i9[t]:s...`

## remove_liquidity_apply_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i10, i11`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i10[t]:sbf = 1:sbf) && (i11[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32] > { #x00000000 }:bv[32]) && (i4[t]:bv[32] > { #...`

## reserve_invariant_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `params_ok, reserve_invariant_valid`
- Data helpers: `drift_ok, k_monotonic, k_ok, max_safe_32, reserves_ok, safe_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (k_ok(i1[t]:bv[32], i2[t]:bv[32]) && k_ok(i3[t]:bv[32], i4[t]:bv[32]))) && (o3[t]:sbf =...`

## reserve_ratio_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0010`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `params_ok, reserve_valid`
- Data helpers: `liabilities_ok, max_safe_32, ratio_ok, reserve_ratio_ok, safe_ratio_ok, safe_reserve_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> liabilities_ok(i2[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> reserve_ratio_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32]))...`

## resource_artifact_binding_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `resource_and_service_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `00100`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Control helpers: `artifact_binding_ok, artifact_core_ok, attachments_ok, optional_req, proof_gated_artifact_binding_ok, replay_and_signer_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> artifact_core_ok(i1[t]:sbf, i5[t]:sbf, i12[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> replay_and_signer_ok(i2[t]:sbf, i3[t]:sbf, i8[t]:sbf, i6[t]:sbf, i11[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> attachments_...`

## resource_budget_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `resource_and_service_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Control helpers: `admission_ok, operational_ok, optional_req, proof_gated_admission_ok`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> operational_ok(i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> admission_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:s...`

## resource_load_shedding_regret_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `resource_and_service_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `010000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Control helpers: `certs_ok, final_admission_ok, normal_path_ok, optional_req, proof_gated_final_admission_ok, shed_path_ok, user_safety_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> user_safety_ok(i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> certs_ok(i6[t]:sbf, i7[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> normal_path_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5...`

## revision_policy_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `i1, i2`, bv inputs `i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31, i32, i33, i34, i35, i36, i37, i38, i39, i40, i41, i42, i43, i44, i45, i46, i47, i48, i49, i50, i51, i52, i53, i54, i55, i56, i57, i58, i59, i60`, always clauses `1`
- Control helpers: `floor_bounds_ok, le_32`
- Data helpers: `abs_diff_ok, delay_ok, floor_step_ok, ge_32, param_update_ok`
- Equation surface: extractable `True`, equations `10`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8, o9, o10`
- Always: `(o1[t]:sbf = 1:sbf <-> delay_ok(i3[t]:bv[16], i4[t]:bv[16], i5[t]:bv[16])) && (o2[t]:sbf = (i2[t]:sbf = 0:sbf) || (i1[t]:sbf = 1:sbf && o1[t])) && (o3[t]:sbf = 1:sbf <-> param_update_ok(i6[t]:bv[16], i7[t]:bv[16], i8[...`

## revision_policy_v2

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `00000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o10`
- Always: `(o1[t]:sbf = i1[t]:sbf) && (o2[t]:sbf = i2[t]:sbf) && (o3[t]:sbf = i3[t]:sbf) && (o4[t]:sbf = i4[t]:sbf) && (o10[t]:sbf = i1[t]:sbf & i2[t]:sbf & i3[t]:sbf & i4[t]:sbf & i5[t]:sbf & i6[t]:sbf)`

## role_transition_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1101`
- Control surface: sbf inputs `i3, i4`, bv inputs `i1, i2, i5, i6`, always clauses `1`
- Control helpers: `elevation_ok, role_transition_valid, roles_ok`
- Data helpers: `is_demotion, is_elevation, role_admin, role_guardian, role_none, role_operator, role_valid`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> roles_ok(i1[t]:bv[8], i2[t]:bv[8])) && (o2[t]:sbf = 1:sbf <-> elevation_ok(i5[t]:bv[8], i6[t]:bv[8], i3[t]:sbf, i4[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> ((i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf))...`

## route_dominance_frontier_envelope_v1

- Profile: `proof_gate_or_certificate`
- Rule: `frontier_host_certificate_envelopes`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Control helpers: `certificate_path_ok, dominance_cover_ok, fallback_boundary_ok, is1, route_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> dominance_cover_ok(i3[t]:sbf, i4[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> certificate_path_ok(i2[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> fallback_boun...`

## route_path_valid_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0100`
- Control surface: sbf inputs `i3, i4, i5`, bv inputs `i1, i2`, always clauses `1`
- Control helpers: `no_cycles, params_ok, path_continuous, path_ok, pools_valid, route_path_valid`
- Data helpers: `hop_count_ok, hop_count_positive, max_hops_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> hop_count_ok(i1[t]:bv[32], i2[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> path_ok(i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) && (o4[t]:sbf = 1:s...`

## route_split_window_certificate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Control helpers: `fallback_boundary_ok, is1, proof_surface_ok, route_split_ok, window_search_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> window_search_ok(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> proof_surface_ok(i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i11[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> fallback_boundary...`

## routing_decision_tree_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i6, i7`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `proof_gated_decision_canonical`
- Data helpers: `decision_canonical, route_kind_valid`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> route_kind_valid(i5[t]:bv[8])) && (o2[t]:sbf = 1:sbf <-> decision_canonical(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[8])) && (o3[t]:sbf = 1:sbf <-> proof_gated_decision_c...`

## runtime_action_capability_envelope_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf))) && (o2[t]:sbf = 1:sbf <-> ((i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf))) && (o3[t]:sbf = 1:sbf <-> ((i8[t]:sbf = 1:sbf) && (i9[t]:sbf = 1:sbf))) && (...`

## sandwich_detection_v1

- Profile: `exact_combinational_guard`
- Rule: `seed_disputed_specs`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `params_ok, sandwich_safe`
- Data helpers: `back_impact_down, back_impact_ok, back_impact_up, front_impact_down, front_impact_ok, front_impact_up, max_safe_32, prices_ok, rate_ok, safe_range_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32]) && fro...`

## sandwich_window_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Control helpers: `params_ok, sandwich_window_valid`
- Data helpers: `max_safe_32, post_down, post_move_ok, post_up, pre_down, pre_move_ok, pre_up, prices_ok, rate_ok, window_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32], i6[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> pre_move_ok(i1[t]:bv[32], i2[t]:bv[32], i5[t]:bv[32])) && (o3[t]:sbf = 1:...`

## sealed_bid_marginal_bucket_certificate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11`, bv inputs `(none)`, always clauses `1`
- Control helpers: `apportionment_math_ok, is1, privacy_boundary_ok, production_scope_candidate_ok, research_certificate_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> apportionment_math_ok(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i7[t]:sbf, i10[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> privacy_boundary_ok(i6[t]:sbf, i11[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> research...`

## secure_signer_operation_admission_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf))) && (o2[t]:sbf = 1:sbf <-> ((i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf))) && (o3[t]:sbf = 1:sbf <-> ((i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8...`

## service_proof_registry_v1

- Profile: `stateful_policy_guard`
- Rule: `resource_and_service_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1010`
- Control surface: sbf inputs `i2`, bv inputs `i1, i3, i4, i5, i6, i7, i8`, always clauses `1`
- Control helpers: `service_proof_valid, sig_ok, verifier_ok`
- Data helpers: `freshness_ok, ts_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> verifier_ok(i1[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> sig_ok(i2[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> freshness_ok(i6[t]:bv[32], i7[t]:bv[32], i8[t]:bv[32])...`

## settlement_canonical_order_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:bv[16] < i2[t]:bv[16]) && (i2[t]:bv[16] < i3[t]:bv[16]) && (i3[t]:bv[16] < i4[t]:bv[16])))`

## settlement_core_module_bundle_v1

- Profile: `bundle_or_composition`
- Rule: `bundles_and_compositions`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf)))`

## settlement_disaster_envelope_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25`, bv inputs `(none)`, always clauses `1`
- Control helpers: `accounting_ok, deterministic_template_ok, identity_ok, market_data_ok, proof_gated_settlement_allowed, runtime_ok, settlement_preconditions_ok`
- Equation surface: extractable `True`, equations `7`, covered outputs `o1, o2, o3, o4, o5, o6, o7`
- Always: `(o1[t]:sbf = 1:sbf <-> identity_ok(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> market_data_ok(i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf, i12[t]:sbf)) && (o3[t]:sbf =...`

## settlement_feature_extension_bundle_v1

- Profile: `bundle_or_composition`
- Rule: `bundles_and_compositions`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf)))`

## settlement_master_admission_gate_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i9`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8`, always clauses `1`
- Data helpers: `conservation_ok, leg_sum, non_wrapping_sum, oracle_fresh, partial_sum_ab, partial_sum_abc`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i9[t]:sbf = 1:sbf) && conservation_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32]) && oracle_fresh(i6[t]:bv[32], i7[t]:bv[32], i8[t]:bv[32]) ))`

## settlement_module_flag_bundle_v1

- Profile: `bundle_or_composition`
- Rule: `bundles_and_compositions`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i1, i2, i3`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf)))`

## settlement_no_sandwich_aligned_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> (((i1[t]:bv[16] <= i2[t]:bv[16]) && (i2[t]:bv[16] <= i3[t]:bv[16])) || ((i1[t]:bv[16] >= i2[t]:bv[16]) && (i2[t]:bv[16] >= i3[t]:bv[16]))))`

## settlement_price_rails_aligned_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> (((i1[t]:bv[16] < i2[t]:bv[16]) && (i2[t]:bv[16] < i3[t]:bv[16]) && (i3[t]:bv[16] < i4[t]:bv[16])) && ((((i5[t]:bv[16] <= i6[t]:bv[16]) && (i6[t]:bv[16] <= i7[t]:bv[16])) || ((i5[t]:bv[16] >= i6...`

## settlement_price_stability_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> (((i2[t]:bv[16] >= i1[t]:bv[16]) && (i2[t]:bv[16] - i1[t]:bv[16] < { #x0032 }:bv[16])) || ((i2[t]:bv[16] < i1[t]:bv[16]) && (i1[t]:bv[16] - i2[t]:bv[16] < { #x0032 }:bv[16]))))`

## settlement_proof_binding_bundle_v1

- Profile: `bundle_or_composition`
- Rule: `bundles_and_compositions`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf)))`

## settlement_signer_registry_anchor_gate_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0000000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7`, bv inputs `i8, i9, i10, i11`, always clauses `1`
- Equation surface: extractable `True`, equations `7`, covered outputs `o1, o2, o3, o4, o5, o6, o7`
- Always: `(o1[t]:sbf = i1[t]:sbf & i2[t]:sbf & i3[t]:sbf & i4[t]:sbf & i5[t]:sbf & i6[t]:sbf & i7[t]:sbf) && (o2[t]:sbf = i2[t]:sbf & i3[t]:sbf & i4[t]:sbf & i5[t]:sbf) && (o3[t]:sbf = i6[t]:sbf & i7[t]:sbf) && (o4[t]:bv[16] = ...`

## settlement_v1_proof_gate

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110000`
- Control surface: sbf inputs `i8, i9, i10, i11, i12`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Data helpers: `canonical, no_sandwich, stable`
- Equation surface: extractable `True`, equations `7`, covered outputs `o1, o2, o3, o4, o5, o6, o7`
- Always: `(o1[t]:sbf = 1:sbf <-> canonical(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16])) && (o2[t]:sbf = 1:sbf <-> no_sandwich(i5[t]:bv[16], i6[t]:bv[16], i7[t]:bv[16])) && (o3[t]:sbf = 1:sbf <-> stable(i7[t]:bv[16],...`

## settlement_v2_buyback_proof_gate

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `01100000`
- Control surface: sbf inputs `i8, i9, i10, i11, i12, i13`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Data helpers: `canonical, no_sandwich, stable`
- Equation surface: extractable `True`, equations `8`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8`
- Always: `(o1[t]:sbf = 1:sbf <-> canonical(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16])) && (o2[t]:sbf = 1:sbf <-> no_sandwich(i5[t]:bv[16], i6[t]:bv[16], i7[t]:bv[16])) && (o3[t]:sbf = 1:sbf <-> stable(i7[t]:bv[16],...`

## settlement_v3_buyback_floor_proof_gate

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `01100000`
- Control surface: sbf inputs `i8, i9, i10, i11, i12, i13`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Data helpers: `canonical, no_sandwich, stable`
- Equation surface: extractable `True`, equations `8`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8`
- Always: `(o1[t]:sbf = 1:sbf <-> canonical(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16])) && (o2[t]:sbf = 1:sbf <-> no_sandwich(i5[t]:bv[16], i6[t]:bv[16], i7[t]:bv[16])) && (o3[t]:sbf = 1:sbf <-> stable(i7[t]:bv[16],...`

## settlement_v4_buyback_floor_rebate_lock

- Profile: `multi_limb_word_arithmetic`
- Rule: `multi_limb_arithmetic_specs`
- Temporal: `True`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `i32, i33, i34`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31, i35, i36, i37, i38, i39, i40, i41, i42, i43, i44, i45, i46, i47, i48, i49, i50, i51, i52, i53`, always clauses `1`
- Control helpers: `balance_ok, eq_32, floor_reached, le_32, one_hot_3, token_burn_valid, token_mint_valid, token_ok, token_supply_dec, token_supply_eq, token_supply_inc, token_transfer_valid`
- Data helpers: `add_32, burn_floor_ok, buyback_share_ok, canonical, cpmm_ok, fee_rate_ok, ge_32, is_positive_32, is_zero_32, no_sandwich, rebate_cap_ok, rebate_rate_ok, stable, sub_32, sub_32_tok, thresholds_ok, unit_ok, weight_tier_ok, weighted_stake_ok`
- Equation surface: extractable `True`, equations `33`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11`
- Always: `(o1[0]:sbf = 1:sbf <-> canonical(i1[0]:bv[16], i2[0]:bv[16], i3[0]:bv[16], i4[0]:bv[16])) && (o1[1]:sbf = 1:sbf <-> canonical(i1[1]:bv[16], i2[1]:bv[16], i3[1]:bv[16], i4[1]:bv[16])) && (o2[0]:sbf = 0:sbf) && (o2[1]:s...`

## settlement_v4_buyback_floor_rebate_lock_proof_gate

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `01100000000`
- Control surface: sbf inputs `i8, i9, i10, i11, i12, i13, i14, i15, i16`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Data helpers: `canonical, no_sandwich, stable`
- Equation surface: extractable `True`, equations `11`, covered outputs `o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11`
- Always: `(o1[t]:sbf = 1:sbf <-> canonical(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16])) && (o2[t]:sbf = 1:sbf <-> no_sandwich(i5[t]:bv[16], i6[t]:bv[16], i7[t]:bv[16])) && (o3[t]:sbf = 1:sbf <-> stable(i7[t]:bv[16],...`

## settlement_v5_aligned_compact_bundle

- Profile: `bundle_or_composition`
- Rule: `bundles_and_compositions`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i8, i9, i10, i11, i12, i13, i14, i15, i16`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> (((i1[t]:bv[16] < i2[t]:bv[16]) && (i2[t]:bv[16] < i3[t]:bv[16]) && (i3[t]:bv[16] < i4[t]:bv[16])) && ((((i5[t]:bv[16] <= i6[t]:bv[16]) && (i6[t]:bv[16] <= i7[t]:bv[16])) || ((i5[t]:bv[16] >= i6...`

## settlement_witness_lifecycle_v1

- Profile: `bundle_or_composition`
- Rule: `batching_and_settlement_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7`, bv inputs `(none)`, always clauses `1`
- Control helpers: `lifecycle_progress, outcome_total, settlement_witness_lifecycle_ok`
- Data helpers: `rejection_total, settled_requires_witness, witness_coherent`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> outcome_total(i5[t]:sbf, i6[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> witness_coherent(i1[t]:sbf, i2[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> settled_requires_witness(i5[t]:sbf, i2[t]:sbf, i4[t]:sbf)) && (o4...`

## slippage_bounds_v2

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `output_ok, params_ok, safe_pair_ok, slippage_v2_valid`
- Data helpers: `expected_ok, floor_ok, impact_down, impact_ok, impact_up, max_safe_32, price_ok, rate_ok, safe_ok, slip_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> output_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o3...`

## slippage_floor_invariant_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i4, i5`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `floor_locked_and_honored, floor_unchanged, proof_gated_floor_locked_and_honored`
- Data helpers: `floor_honored`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> floor_unchanged(i1[t]:bv[64], i2[t]:bv[64])) && (o2[t]:sbf = 1:sbf <-> floor_honored(i2[t]:bv[64], i3[t]:bv[64])) && (o3[t]:sbf = 1:sbf <-> floor_locked_and_honored(i1[t]:bv[64], i2[t]:bv[64], i...`

## slippage_protection_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `params_ok, safe_pair_ok, slippage_valid`
- Data helpers: `expected_ok, max_amount_ok, max_safe_32, min_amount_ok, rate_ok, safe_range_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> min_amount_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> max_amount_ok(i1[t]:bv[32], i2[t...`

## sss_recovery_share_quorum_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `2`, covered outputs `o1, o2`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf))) && (o2[t]:...`

## supply_cap_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `params_ok, supply_cap_valid`
- Data helpers: `after_mint_ok, cap_ok, current_ok, no_overflow`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> current_ok(i1[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> after_mint_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:sbf)) && (o4[t]...`

## swap_bv32_safe_range_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i2[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i3[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i4[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i5[t]:bv[32] <= { #x...`

## swap_exact_in_fee_proof_gate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i10, i11, i12`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i10[t]:sbf = 1:sbf) && (i11[t]:sbf = 1:sbf) && (i12[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32] > { #x00000000 }:bv[32]...`

## swap_exact_in_proof_gate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i9, i10, i11`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i9[t]:sbf = 1:sbf) && (i10[t]:sbf = 1:sbf) && (i11[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32] > { #x00000000 }:bv[32])...`

## swap_exact_in_protocol_fee_apply_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i11, i12, i13, i14`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i11[t]:sbf = 1:sbf) && (i12[t]:sbf = 1:sbf) && (i13[t]:sbf = 1:sbf) && (i14[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32]...`

## swap_exact_in_v1

- Profile: `multi_limb_word_arithmetic`
- Rule: `multi_limb_arithmetic_specs`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15`, always clauses `1`
- Control helpers: `swap_exact_in_constraints`
- Data helpers: `add_32, fee_bps_valid, is_positive_32, sub_32, value_gte_32`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> swap_exact_in_constraints(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16], i5[t]:bv[16], i6[t]:bv[16], i7[t]:bv[16], i8[t]:bv[16], i9[t]:bv[16], i10[t]:bv[16], i11[t]:bv[16], i12[t]:bv[16...`

## swap_exact_out_fee_proof_gate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i10, i11, i12`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i10[t]:sbf = 1:sbf) && (i11[t]:sbf = 1:sbf) && (i12[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32] > { #x00000000 }:bv[32]...`

## swap_exact_out_proof_gate_v1

- Profile: `proof_gate_or_certificate`
- Rule: `proof_gates_and_certificates`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i9, i10, i11`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i9[t]:sbf = 1:sbf) && (i10[t]:sbf = 1:sbf) && (i11[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32] > { #x00000000 }:bv[32])...`

## swap_exact_out_protocol_fee_apply_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i11, i12, i13, i14`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i11[t]:sbf = 1:sbf) && (i12[t]:sbf = 1:sbf) && (i13[t]:sbf = 1:sbf) && (i14[t]:sbf = 1:sbf) && (i1[t]:bv[32] > { #x00000000 }:bv[32]) && (i2[t]:bv[32] > { #x00000000 }:bv[32]) && (i3[t]:bv[32]...`

## swap_exact_out_v1

- Profile: `multi_limb_word_arithmetic`
- Rule: `multi_limb_arithmetic_specs`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15`, always clauses `1`
- Control helpers: `swap_exact_out_constraints`
- Data helpers: `add_32, fee_bps_valid, is_positive_32, sub_32, value_gt_32, value_gte_32`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> swap_exact_out_constraints(i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16], i4[t]:bv[16], i5[t]:bv[16], i6[t]:bv[16], i7[t]:bv[16], i8[t]:bv[16], i9[t]:bv[16], i10[t]:bv[16], i11[t]:bv[16], i12[t]:bv[1...`

## swap_execution_regret_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0100`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Control helpers: `certs_ok, execute_safe, limits_ok, proof_gated_execute_safe, requirement_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> limits_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> certs_ok(i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> execute_sa...`

## swap_fee_total_ceil_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `fee_total_ok`
- Data helpers: `fee_bounds_ok, max_safe_64, rate_ok, safe_ok`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> fee_total_ok(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64]))`

## tau_policy_shadow_migration_gate_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12`, bv inputs `(none)`, always clauses `1`
- Control helpers: `artifact_binding_ok, decision_equivalent, shadow_evidence_ok`
- Equation surface: extractable `True`, equations `6`, covered outputs `o1, o2, o3, o4, o5, o6`
- Always: `(o1[t]:sbf = 1:sbf <-> decision_equivalent(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> artifact_binding_ok(i6[t]:sbf, i7[t]:sbf, i8[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> shadow_evidence_ok(i5[t]:sbf, i9[t...`

## tdex_buyback_floor_fixedpoint_v2

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `i9, i10, i11`, bv inputs `i3, i4, i5, i6, i7`, always clauses `1`
- Data helpers: `floor_reached`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = i9[t]:sbf) && (o2[t]:sbf = i10[t]:sbf) && (o3[t]:sbf = 1:sbf <-> burn_floor_ok(i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o4[t]:sbf = i11[t]:sbf) && (o5[t]:sbf = o1[t] & o2...`

## tdex_buyback_floor_v2

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `i8, i9`, bv inputs `i3, i4, i5, i6, i7`, always clauses `1`
- Data helpers: `floor_reached`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = i8[t]:sbf) && (o2[t]:sbf = i9[t]:sbf) && (o3[t]:sbf = 1:sbf <-> burn_floor_ok(i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o4[t]:sbf = o1[t] & o2[t] & o3[t])`

## test_orchestrator_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `010`
- Control surface: sbf inputs `(none)`, bv inputs `i1`, always clauses `1`
- Control helpers: `range_ok`
- Data helpers: `lower_ok, max_value, min_value, upper_ok`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> lower_ok(i1[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> upper_ok(i1[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> range_ok(i1[t]:bv[32]))`

## timelock_enforcement_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `params_ok, timelock_valid`
- Data helpers: `criticality_ok, delay_factor, delay_ok, delay_positive, delay_safe_ok, max_safe_delay, multiplier_ok, timestamps_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> delay_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32])) && (o3[...`

## token_archetype_activity_reward_32_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `010`
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3, i5`, always clauses `1`
- Data helpers: `activity_ok, is_positive_32, reward_ok`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> activity_ok(i1[t]:bv[32], i2[t]:bv[32], i4[t]:sbf, i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> reward_ok(i3[t]:bv[32], i5[t]:bv[32])) && (o3[t]:sbf = o1[t] & o2[t])`

## token_archetype_lock_weighted_rewards_32_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `111`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Data helpers: `max_safe_32, rate_ok, reward_ok, safe_range_ok, weight_calc_ok`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> (rate_ok(i2[t]:bv[32]) && weight_calc_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32]))) && (o2[t]:sbf = 1:sbf <-> reward_ok(i3[t]:bv[32], i4[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> ((o1[t]:sbf = 1:sb...`

## token_archetype_lock_weighted_rewards_32_v2

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `110`
- Control surface: sbf inputs `i5, i6`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> (i2[t]:bv[16] <= { 10000 }:bv[16])) && (o2[t]:sbf = 1:sbf <-> (i3[t]:bv[16] <= i4[t]:bv[16])) && (o3[t]:sbf = 1:sbf <-> ((o1[t]:sbf = 1:sbf) && (o2[t]:sbf = 1:sbf) && ((i1[t]:bv[16]) <= { 65534 ...`

## token_archetype_soulbound_v2

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1110`
- Control surface: sbf inputs `i4, i5, i6`, bv inputs `i1, i2, i3`, always clauses `1`
- Control helpers: `burn_allowed, issuer_involved, mint_allowed, one_hot_3, transfer_allowed`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> transfer_allowed(i4[t]:sbf, i1[t]:bv[16], i2[t]:bv[16], i3[t]:bv[16])) && (o2[t]:sbf = 1:sbf <-> mint_allowed(i5[t]:sbf, i1[t]:bv[16], i3[t]:bv[16])) && (o3[t]:sbf = 1:sbf <-> burn_allowed(i6[t]...`

## token_archetype_vesting_cliff_32_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `111`
- Control surface: sbf inputs `i4`, bv inputs `i1, i2, i3, i5, i6`, always clauses `1`
- Data helpers: `bounds_ok, cap_ok, cliff_ok, max_safe_32, rate_ok, safe_range_ok`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> cliff_ok(i4[t]:sbf, i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (bounds_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32]) && cap_ok(i1[t]:bv[32], i5[t]:bv[32], i6[t]:bv[32]))) && (o3[t]:sb...`

## token_archetype_vesting_cliff_32_v2

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `010`
- Control surface: sbf inputs `i4, i7, i8`, bv inputs `i1, i2, i3, i5, i6`, always clauses `1`
- Equation surface: extractable `True`, equations `3`, covered outputs `o1, o2, o3`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i4[t]:sbf = 1:sbf) && (i3[t]:bv[16] <= i2[t]:bv[16]))) && (o2[t]:sbf = 1:sbf <-> ((i2[t]:bv[16] <= i1[t]:bv[16]) && (i3[t]:bv[16] <= i1[t]:bv[16]) && (i6[t]:bv[16] <= { 10000 }:bv[16]) && (i3[...`

## token_composite_v2

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = i1[t]:sbf) && (o2[t]:sbf = i2[t]:sbf) && (o3[t]:sbf = i3[t]:sbf) && (o4[t]:sbf = i1[t]:sbf & i2[t]:sbf & i3[t]:sbf & i4[t]:sbf & i5[t]:sbf)`

## tokenomics_buyback_burn_v2

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1`
- Control surface: sbf inputs `i5`, bv inputs `i1, i2, i3, i4, i6, i7`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = 1:sbf <-> ( (i1[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i2[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i3[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i4[t]:bv[32] <= { #x0000FFFF }:bv[32]) && (i6[t]:bv[32] <= { #...`

## tokenomics_buyback_floor_32_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Data helpers: `burn_amount_ok, buyback_calc_ok, floor_ok, max_safe_32, safe_range_ok, supply_update_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> buyback_calc_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> burn_amount_ok(i4[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> (supply_update_ok(i5[t]:bv[32], i6[t]:b...`

## tokenomics_fee_split_32_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Data helpers: `component_ok, max_safe_32, safe_range_ok, shares_sum_ok, split_sum_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> shares_sum_ok(i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (component_ok(i1[t]:bv[32], i2[t]:bv[32], i5[t]:bv[32]) && component_ok(i1[t]:bv[32], i3[t]:bv[32], i6[t]:bv[32...`

## tokenomics_rate_bps_32_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Data helpers: `caps_ok, max_safe_32, rate_calc_ok, rate_in_range, safe_range_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> rate_in_range(i2[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> rate_calc_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> caps_ok(i1[t]:bv[32], i3[t]:bv[32], i4[t]:b...`

## tokenomics_usage_rebate_32_v1

- Profile: `exact_combinational_guard`
- Rule: `token_and_protocol_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau did not create output file: o1`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Data helpers: `cap_ok, max_safe_32, rate_ok, rebate_calc_ok, safe_range_ok, usage_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> usage_ok(i4[t]:bv[32], i2[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (rate_ok(i3[t]:bv[32]) && rebate_calc_ok(i1[t]:bv[32], i3[t]:bv[32], i5[t]:bv[32]))) && (o3[t]:sbf = 1:sbf <-> cap_o...`

## transfer_hook_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1100`
- Control surface: sbf inputs `i6`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `hook_ok, transfer_hook_valid`
- Data helpers: `balances_positive, conservation_ok, receiver_ok, sender_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> balances_positive(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> (sender_ok(i1[t]:bv[32], i2[t]:bv[32], i5[t]:bv[32]) && receiver_ok(i3[t]:bv[32], i4[t]:bv[32...`

## treasury_spend_categories_v2

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `i8`, bv inputs `i1, i2, i3, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `cap_ok, category_valid, treasury_v2_valid`
- Data helpers: `cap_for_audits, cap_for_grants, cap_for_ops, cap_for_other, cat_audits, cat_grants, cat_ops, cat_other, service_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> category_valid(i2[t]:bv[8])) && (o2[t]:sbf = 1:sbf <-> cap_ok(i1[t]:bv[32], i2[t]:bv[8], i3[t]:bv[32], i4[t]:bv[32], i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> service_...`

## treasury_spend_policy_32_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `i5, i6, i7, i8`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Data helpers: `amount_ok, cat_audits, cat_grants, cat_ops, category_ok, is_positive_32, proof_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> category_ok(i4[t]:bv[8], i5[t]:sbf, i6[t]:sbf, i7[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> amount_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> proof_ok(i1[t]:bv[32], i8[t]:s...`

## usage_rebate_tiered_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, always clauses `1`
- Control helpers: `tier_match_ok, usage_rebate_valid`
- Data helpers: `is_tier0, is_tier1, is_tier2, is_tier3, rates_ok, thresholds_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> thresholds_ok(i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> rates_ok(i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32], i8[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> tier_match_ok(i1[t]...`

## volume_anomaly_guard_v1

- Profile: `exact_combinational_guard`
- Rule: `amm_and_orderflow_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `params_ok, volume_anomaly_valid`
- Data helpers: `cumulative_ok, max_safe_32, max_safe_32_2x, rate_ok, ref_ok, safe_ok, single_trade_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> single_trade_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> cumulative_ok(i4[t]:bv[32], i5...`

## vote_weight_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `False`
- Execution: `error` via ``
- Execution errors: `tau failed (rc=-1): tau timed out`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `params_ok, vote_weight_valid, weight_math_ok`
- Data helpers: `duration_ok, lock_capped, lock_max_ok, lock_zero_ok, max_safe_32, max_safe_32_mult, multiplier_ok, safe_range_ok, tokens_ok, weight_max_ok, weight_min_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i4[t]:bv[32], i3[t]:bv[32], i5[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> multiplier_ok(i3[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> weight_math_ok(i1[t]:bv[32], i4[t]:bv[32], i3[...`

## wallet_recovery_envelope_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `frontier_backfill_stateful_gates`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9, i10`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `2`, covered outputs `o1, o2`
- Always: `(o1[t]:sbf = 1:sbf <-> ((i1[t]:sbf = 1:sbf) && (i2[t]:sbf = 1:sbf) && (i3[t]:sbf = 1:sbf) && (i4[t]:sbf = 1:sbf) && (i5[t]:sbf = 1:sbf) && (i6[t]:sbf = 1:sbf) && (i7[t]:sbf = 1:sbf) && (i8[t]:sbf = 1:sbf))) && (o2[t]:...`

## withdrawal_dispute_window_gate_v1

- Profile: `stateful_policy_guard`
- Rule: `governance_and_policy_suite`
- Temporal: `True`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2`, bv inputs `(none)`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o1`
- Always: `(o1[t]:sbf = (i1[t]:sbf & (i2[t-1]:sbf)' & (i2[t-2]:sbf)'))`

## zusd_cross_module_oracle_sync_gate_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3`, bv inputs `(none)`, always clauses `1`
- Control helpers: `env_ok, sync_gate_ok`
- Equation surface: extractable `True`, equations `2`, covered outputs `o1, o2`
- Always: `(o1[t]:sbf = 1:sbf <-> env_ok(i1[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> sync_gate_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf))`

## zusd_deposit_sp_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0100`
- Control surface: sbf inputs `i6`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `deposit_sp_allowed`
- Data helpers: `amount_pos, free_bound_ok, free_delta_ok, sp_delta_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> (amount_pos(i1[t]:bv[64]) && free_bound_ok(i2[t]:bv[64], i1[t]:bv[64]))) && (o2[t]:sbf = 1:sbf <-> (free_delta_ok(i2[t]:bv[64], i4[t]:bv[64], i1[t]:bv[64]) && sp_delta_ok(i3[t]:bv[64], i5[t]:bv[...`

## zusd_liquidation_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1100`
- Control surface: sbf inputs `i1, i3`, bv inputs `i2, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `liq_preconditions_ok, liquidation_allowed`
- Data helpers: `coll_cap_ok, debt_absorbable, positive_debt, safe_u32`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> debt_absorbable(i2[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> coll_cap_ok(i5[t]:bv[32], i6[t]:bv[32], i7[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> liq_preconditions_ok(i1[t]:sbf, i2[t]:bv[3...`

## zusd_liquidation_guard_v2

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1100`
- Control surface: sbf inputs `i1, i3`, bv inputs `i2, i4, i5, i6, i7`, always clauses `1`
- Control helpers: `liquidation_allowed, pre_ok`
- Data helpers: `coll_cap_ok, debt_absorbable, positive_debt`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> debt_absorbable(i2[t]:bv[64], i4[t]:bv[64])) && (o2[t]:sbf = 1:sbf <-> coll_cap_ok(i5[t]:bv[64], i6[t]:bv[64], i7[t]:bv[64])) && (o3[t]:sbf = 1:sbf <-> pre_ok(i1[t]:sbf, i2[t]:bv[64], i3[t]:sbf)...`

## zusd_mint_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0`
- Control surface: sbf inputs `i6, i7, i8, i9, i10`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Equation surface: extractable `True`, equations `1`, covered outputs `o4`
- Always: `(o4[t]:sbf = 1:sbf <-> ((i1[t]:bv[64] > { #x0000000000000000 }:bv[64]) && (i4[t]:bv[64] >= i2[t]:bv[64]) && ((i4[t]:bv[64] - i2[t]:bv[64]) = i1[t]:bv[64]) && (i5[t]:bv[64] >= i3[t]:bv[64]) && ((i5[t]:bv[64] - i3[t]:bv...`

## zusd_oracle_commit_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0000`
- Control surface: sbf inputs `i1, i2, i5, i6`, bv inputs `i3, i4`, always clauses `1`
- Control helpers: `freshness_ok, oracle_commit_ok, vault_ok`
- Data helpers: `pending_order_ok, price_pos`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> pending_order_ok(i3[t]:bv[32], i4[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> freshness_ok(i1[t]:sbf, i5[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> vault_ok(i2[t]:sbf, i6[t]:sbf)) && (o4[t]:sbf = 1:sbf <-> or...`

## zusd_oracle_commit_guard_v2

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5`, bv inputs `(none)`, always clauses `1`
- Control helpers: `env_ok, oracle_commit_ok, policy_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> env_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> policy_ok(i4[t]:sbf, i5[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> policy_ok(i4[t]:sbf, i5[t]:sbf)) && (o4[t]:sbf = 1:sbf <-> oracle_co...`

## zusd_oracle_recovery_lifecycle_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `missing` via ``
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6, i7, i8`, bv inputs `(none)`, always clauses `1`
- Control helpers: `healthy_now, outcome_total, reenabled_requires_healthy, rejection_total, zusd_oracle_recovery_lifecycle_ok`
- Equation surface: extractable `True`, equations `5`, covered outputs `o1, o2, o3, o4, o5`
- Always: `(o1[t]:sbf = 1:sbf <-> healthy_now(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> reenabled_requires_healthy(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> ou...`

## zusd_recovery_mode_gate_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0001`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6`, bv inputs `(none)`, always clauses `1`
- Control helpers: `action_allowed, blocked_by_recovery, env_ok, risky_ops_allowed`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> env_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> risky_ops_allowed(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> blocked_by_recov...`

## zusd_redeem_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1000`
- Control surface: sbf inputs `i10, i11, i12`, bv inputs `i1, i2, i3, i4, i5, i6, i7, i8, i9`, always clauses `1`
- Control helpers: `redeem_allowed`
- Data helpers: `amount_pos, coll_delta_ok, debt_delta_ok, debt_pre_ok, fee_shape_ok, free_delta_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> (debt_pre_ok(i2[t]:bv[64], i3[t]:bv[64], i1[t]:bv[64]) && debt_delta_ok(i2[t]:bv[64], i5[t]:bv[64], i1[t]:bv[64]) && free_delta_ok(i3[t]:bv[64], i6[t]:bv[64], i1[t]:bv[64]))) && (o2[t]:sbf = 1:s...`

## zusd_repay_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1110`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `repay_allowed`
- Data helpers: `amount_pos, debt_delta_ok, free_delta_ok, pre_bounds_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> pre_bounds_ok(i2[t]:bv[64], i3[t]:bv[64], i1[t]:bv[64])) && (o2[t]:sbf = 1:sbf <-> debt_delta_ok(i2[t]:bv[64], i4[t]:bv[64], i1[t]:bv[64])) && (o3[t]:sbf = 1:sbf <-> free_delta_ok(i3[t]:bv[64], ...`

## zusd_supply_conservation_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1111`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Control helpers: `safe_range_ok, supply_conserved`
- Data helpers: `after_ok, before_ok, safe_u32`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> before_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32])) && (o2[t]:sbf = 1:sbf <-> after_ok(i4[t]:bv[32], i5[t]:bv[32], i6[t]:bv[32])) && (o3[t]:sbf = 1:sbf <-> safe_range_ok(i1[t]:bv[32], i2[t]:bv[...`

## zusd_supply_conservation_v2

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `1111`
- Control surface: sbf inputs `(none)`, bv inputs `i1, i2, i3, i4, i5, i6`, always clauses `1`
- Control helpers: `supply_conserved`
- Data helpers: `after_ok, before_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> before_ok(i1[t]:bv[64], i2[t]:bv[64], i3[t]:bv[64])) && (o2[t]:sbf = 1:sbf <-> after_ok(i4[t]:bv[64], i5[t]:bv[64], i6[t]:bv[64])) && (o3[t]:sbf = 1:sbf <-> supply_conserved(i1[t]:bv[64], i2[t]:...`

## zusd_transfer_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0000`
- Control surface: sbf inputs `i1, i2, i3, i4, i5, i6`, bv inputs `(none)`, always clauses `1`
- Control helpers: `policy_ok, structural_ok, transfer_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> structural_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf)) && (o2[t]:sbf = 1:sbf <-> policy_ok(i4[t]:sbf, i5[t]:sbf, i6[t]:sbf)) && (o3[t]:sbf = 1:sbf <-> transfer_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]...`

## zusd_withdraw_collateral_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0100`
- Control surface: sbf inputs `i5, i6`, bv inputs `i1, i2, i3, i4`, always clauses `1`
- Control helpers: `withdraw_allowed`
- Data helpers: `amount_pos, coll_delta_ok, enough_coll, risk_gate_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> (amount_pos(i1[t]:bv[64]) && enough_coll(i2[t]:bv[64], i1[t]:bv[64]) && coll_delta_ok(i2[t]:bv[64], i3[t]:bv[64], i1[t]:bv[64]))) && (o2[t]:sbf = 1:sbf <-> risk_gate_ok(i4[t]:bv[64], i5[t]:sbf))...`

## zusd_withdraw_sp_guard_v1

- Profile: `stateful_policy_guard`
- Rule: `zusd_suite`
- Temporal: `False`
- Execution: `ok` via `repl`
- Observed output signatures: `0100`
- Control surface: sbf inputs `i6, i7`, bv inputs `i1, i2, i3, i4, i5`, always clauses `1`
- Control helpers: `policy_ok, withdraw_sp_allowed`
- Data helpers: `amount_pos, free_delta_ok, sp_bound_ok, sp_delta_ok`
- Equation surface: extractable `True`, equations `4`, covered outputs `o1, o2, o3, o4`
- Always: `(o1[t]:sbf = 1:sbf <-> (amount_pos(i1[t]:bv[64]) && sp_bound_ok(i3[t]:bv[64], i1[t]:bv[64]))) && (o2[t]:sbf = 1:sbf <-> (sp_delta_ok(i3[t]:bv[64], i5[t]:bv[64], i1[t]:bv[64]) && free_delta_ok(i2[t]:bv[64], i4[t]:bv[64...`
