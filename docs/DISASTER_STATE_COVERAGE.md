# Disaster State Coverage

This document records the current bounded disaster-state search coverage for this
checkout.

## Current receipt

As of 2026-04-25, the current disaster-search expansion plan contains 125 named
what-if axes. The latest full replay completed with:

```text
selected_axis_count = 125
unreachable_count = 125
failed_count = 0
inconclusive_count = 0
```

Standard reading: every selected axis in the current plan replayed under the
declared bounded harnesses, and none failed or timed out inconclusively.

The claim is intentionally bounded:

```text
Covered(axis) := axis is named in DISASTER_SEARCH_EXPANSION_AXES
ReceiptOK(axis) := every command for axis passes under --timeout-s 240

CurrentClaim := forall axis, Covered(axis) -> ReceiptOK(axis)
```

Standard reading: for every named axis in the current disaster-search plan, the
current replay evidence passes under the configured timeout. This is not a claim
that all possible future or unbounded disaster states are formally impossible.

## Replay

Build the current plan:

```bash
python3 tools/build_stateful_disaster_search_expansion_plan.py --format text
```

Run the full receipt:

```bash
python3 tools/run_stateful_disaster_search_expansion_plan.py \
  --timeout-s 240 \
  --output internal/stateful_disaster_search_expansion_receipt.latest.json \
  --format text
```

The `internal/` receipt path is intentionally local and git-ignored. The public
source of the axis definitions is `tools/stateful_scenario_bridge.py`.

Focused checks used for this update:

```bash
pytest -q tests/integration/test_stateful_scenario_bridge.py
python3 -m py_compile \
  tools/stateful_scenario_bridge.py \
  tools/build_stateful_disaster_search_expansion_plan.py \
  tools/run_stateful_disaster_search_expansion_plan.py \
  tests/integration/test_stateful_scenario_bridge.py
.venv/bin/python -m mypy \
  tools/stateful_scenario_bridge.py \
  tools/build_stateful_disaster_search_expansion_plan.py \
  tools/run_stateful_disaster_search_expansion_plan.py \
  tests/integration/test_stateful_scenario_bridge.py
git diff --check -- \
  tools/stateful_scenario_bridge.py \
  tools/build_stateful_disaster_search_expansion_plan.py \
  tools/run_stateful_disaster_search_expansion_plan.py \
  tests/integration/test_stateful_scenario_bridge.py \
  tests/kernels/data/perp_epoch_isolated_v3_ml_bva_cases.json
```

## Covered axes

The current plan covers these 125 axes:

1. `epoch_split_brain`
2. `identity_registry_drift`
3. `canonicalization_equivocation`
4. `serialization_width_aliasing`
5. `resource_budget_abort`
6. `repair_after_tamper`
7. `external_state_drift`
8. `atomicity_partial_side_effect`
9. `restart_replay_persistence`
10. `dependency_outage_fail_closed`
11. `numeric_boundary_coupling`
12. `advisory_cache_receipt_coherence`
13. `market_namespace_version_isolation`
14. `reciprocal_netting_pair_forgery`
15. `bounded_advisory_search_envelope`
16. `exact_out_candidate_domain_explosion`
17. `tau_gate_policy_aliasing`
18. `zusd_oracle_recovery_split_brain`
19. `confidential_receipt_attestation_drift`
20. `strategy_session_capability_replay`
21. `fire_registry_proof_tree_supply_chain`
22. `batch_clearing_fragmentation_ordering`
23. `intent_auth_shape_replay`
24. `perp_funding_liquidation_oracle_window`
25. `proof_mining_packet_envelope_replay`
26. `sealed_bid_reveal_commitment_binding`
27. `curve_registry_dispatch_aliasing`
28. `vault_reward_carry_spendability`
29. `tau_net_client_transport_boundary`
30. `tau_operator_policy_supply_chain`
31. `settlement_proof_recompute_gate`
32. `operations_parser_canonical_envelope`
33. `resource_load_shedding_chaos_boundary`
34. `cantor_region_partition_invariance`
35. `autotrader_policy_artifact_replay`
36. `state_accounting_size_boundary`
37. `zusd_api_token_policy_surface`
38. `dex_engine_sequence_anomaly_surface`
39. `quote_receipt_gate_decomposition_consistency`
40. `settlement_witness_lifecycle_value_drift`
41. `dex_core_ref_parity_drift`
42. `confidential_request_admission_gate_decomposition`
43. `boundary_concolic_wrapper_consistency`
44. `runtime_shell_adapter_consistency`
45. `perp_submission_surface_gate_composition`
46. `perp_v2_ref_oracle_parity_boundary`
47. `exact_out_prefilter_winner_repair_boundary`
48. `batch_refinement_mci_parity_boundary`
49. `agent_policy_signing_artifact_boundary`
50. `tau_runner_api_lifecycle_fail_closed`
51. `fire_runtime_receipt_replay_boundary`
52. `exact_in_route_certificate_guarded_key_boundary`
53. `quote_receipt_transport_intent_boundary`
54. `oracle_funding_clock_commitment_boundary`
55. `intent_normal_form_nonce_gate_boundary`
56. `zenograph_krr_policy_state_boundary`
57. `zusd_native_accounting_gate_boundary`
58. `proof_mining_manager_slot_control_boundary`
59. `strategy_native_policy_guard_surface`
60. `autotrader_policy_toolchain_state_boundary`
61. `confidential_core_verifier_binding_boundary`
62. `cantor_shapeforge_morphism_bridge_boundary`
63. `fire_cli_supply_chain_receipt_boundary`
64. `settlement_formal_packet_contract_boundary`
65. `exact_out_formal_packet_contract_boundary`
66. `strategy_residual_guard_binding_boundary`
67. `perp_core_legacy_ref_hazard_boundary`
68. `perp_engine_integration_oracle_bootstrap_boundary`
69. `tau_witness_autotrader_binding_surface`
70. `fire_registry_deployment_sync_boundary`
71. `tla_queue_lifecycle_model_boundary`
72. `exact_out_shadow_runtime_prefilter_boundary`
73. `tau_runner_subprocess_transport_boundary`
74. `settlement_apply_witness_native_boundary`
75. `tau_operator_policy_receipt_symbolic_boundary`
76. `settlement_price_provenance_semantic_boundary`
77. `fire_kernel_release_verifier_boundary`
78. `quote_receipt_native_adapter_parity_boundary`
79. `perp_native_adapter_oracle_bva_boundary`
80. `intent_nonce_confidential_state_native_boundary`
81. `tla_perp_settlement_queue_model_boundary`
82. `exact_in_lean_rank_projection_boundary`
83. `exact_out_lean_certificate_boundary`
84. `settlement_lean_price_oracle_boundary`
85. `ltl_oracle_recovery_schedule_boundary`
86. `exact_out_lean_concrete_recursion_boundary`
87. `exact_out_lean_ordered_presentation_boundary`
88. `exact_out_lean_repaired_key_cover_boundary`
89. `permissionless_proof_mining_tooling_boundary`
90. `claims_falsifier_inventory_boundary`
91. `tau_semantic_proof_gate_split_boundary`
92. `tau_autotrader_spec_guard_boundary`
93. `fire_formal_runtime_note_boundary`
94. `numeric_kernel_ml_history_boundary`
95. `proof_mining_native_permissionless_boundary`
96. `exact_out_lean_stream_support_boundary`
97. `cross_module_tool_checker_boundary`
98. `stateful_report_bridge_ranking_boundary`
99. `tau_operator_library_artifact_boundary`
100. `tau_exact_out_resource_spec_boundary`
101. `dex_settlement_recovery_proof_unit_boundary`
102. `acceptance_tcb_minimized_witness_boundary`
103. `rc1_release_readiness_artifact_boundary`
104. `advisory_swap_sandwich_preflight_boundary`
105. `functional_core_split_parity_branch_boundary`
106. `fire_cal_package_claim_boundary`
107. `tokenomics_wash_budget_boundary`
108. `decision_tau_witness_runner_boundary`
109. `optimizer_liveness_prompt_boundary`
110. `chaos_regret_campaign_boundary`
111. `autotrader_krr_import_supply_chain_boundary`
112. `amm_curve_il_parity_boundary`
113. `lean_amm_canonical_math_boundary`
114. `lean_repair_economics_boundary`
115. `lean_autotrader_solver_policy_boundary`
116. `krr_region_ba_reasoner_boundary`
117. `tool_guard_lint_symbolic_boundary`
118. `zusd_support_native_selector_boundary`
119. `lean_cross_surface_composition_boundary`
120. `operator_environment_tooling_boundary`
121. `stateful_bounty_catalog_feedback_boundary`
122. `batch_settler_greedy_adapter_boundary`
123. `exact_out_adaptive_region_boundary`
124. `shapeforge_release_ratchet_artifact_boundary`
125. `zenograph_autotrader_ranking_artifact_boundary`

## Residual backlog

The plan references 800 of 846 discovered `tests/**/test_*.py` files. The
remaining 46 files were not promoted into the current unreachable claim because
they are stale, skipped, timeout-prone, environment-dependent, failing, or not
yet classified as disaster-state evidence.

Residual groups:

- Tau governance, inventory, review-doc, semantic parity, execution-census, and
  spec-assurance files. These need refreshed artifacts and cleaner no-skip
  receipts before promotion.
- Exact-out adaptive/repaired benchmark files. The region lane is covered, but
  benchmark lanes timed out under the 240 second disaster-runner cap.
- Tau runner and Tau network chaos paths that require external binaries or
  Toxiproxy services.
- Autotrader live expectation drift. The current live-strategy/text-summary
  behavior does not match stale test expectations.
- ShapeForge target-eval support-count expectations. Release, ratchet,
  explorer, compare, and validation lanes are covered; target-eval counts are
  stale.
- Morph/SMT/ML miner files. These need split receipts and tooling cleanup
  before they can be treated as disaster-state coverage.
- Root hygiene/security posture/trace-to-facts checks. These are useful release
  hygiene, but they are not currently folded into the disaster-state plan.

## Interpretation

This coverage materially improves regression assurance:

- disaster states are named explicitly instead of implied by broad test suites
- each axis has replay commands and a timeout bound
- timeouts, skips, and stale expectations are excluded rather than counted as
  safety evidence
- the README claim stays at bounded receipt strength, not universal proof

The remaining path to a stronger public claim is to convert the residual backlog
into clean no-skip receipts or promote the highest-value invariants into Lean,
ESSO, Tau, or TLA proof lanes.
