# ZenoDEX `SHAPE_V1`

`SHAPE_V1` is the release contract for the currently achieved audited-domain
ShapeForge candidate targets.

It is intentionally narrower than a universal “the DEX is solved” claim.

## Scope

`D_v1` means the currently promoted audited domain in the ShapeForge world model:

- `shape_pp_candidate_v1 = 10/10`, `blocked = 0`
- `dex_kernel_candidate_v1 = 6/6`, `blocked = 0`
- `runtime_boundary_candidate_v1 = 5/5`, `blocked = 0`

Important scope limits:

- exact-out canonicality is promoted on the repaired bounded audited lane, not as a proof of unrestricted global generator completeness
- settlement safety is promoted on the settlement-certificate posture with replayable end-to-end packet checks
- oracle-divergence safety is promoted on explicit fail-closed contract boundaries, not as a universal kernel-backed theorem for every deployment

Authoritative machine-readable sources:

- `docs/zenodex/shapeforge_promoted/zenodex_target_shapes.seed.json`
- `docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json`
- `docs/zenodex/shapeforge_promoted/zenodex_negative_knowledge.seed.json`

## Release Gate

The minimum release ratchet for `SHAPE_V1` is:

```bash
python3 tools/check_shape_v1_ratchet.py
```

That gate must remain green before widening any public assurance claim.

The operational release decision checklist for this claim is:

- `docs/zenodex/SHAPE_V1_RELEASE_CHECKLIST.md`

## Clause Manifest

### `cbc_validity`

- Primary artifact:
  - `lean-mathlib/Proofs/BatchOptimality.lean`
  - `lean-mathlib/Proofs/BatchCPMMUnification.lean`
- Checker:
  - `cd lean-mathlib && lake build Proofs.BatchOptimality Proofs.BatchCPMMUnification`
- Replay artifact:
  - `pytest -q tests/core/test_batch_clearing.py tests/core/test_batch_clearing_properties.py`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - batch valid-outcome and batch-to-settlement safety surface

### `unique_canonical_winner_everywhere`

- Primary artifact:
  - `lean-mathlib/Proofs/ZenoDEXUniqueCanonicalWinnerEverywhere.lean`
  - `lean-mathlib/Proofs/ZenoDEXExactInTrueKeyWinner.lean`
  - `lean-mathlib/Proofs/ZenoDEXExactOutManyPoolRepairedKeyCoverInterpretationSemanticBridge.lean`
- Checker:
  - `cd lean-mathlib && lake build Proofs.ZenoDEXUniqueCanonicalWinnerEverywhere Proofs.ZenoDEXExactInTrueKeyWinner Proofs.ZenoDEXExactOutManyPoolRepairedKeyCoverInterpretationSemanticBridge`
- Replay artifact:
  - `pytest -q tests/formal/test_lean_unique_canonical_winner_everywhere.py tests/formal/test_lean_exact_in_true_key_winner.py tests/formal/test_lean_exact_out_many_pool_repaired_key_cover_interpretation_semantic_bridge.py`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - exact-in canonical winners and exact-out repaired bounded audited winners

### `exact_fee_aware_accounting`

- Primary artifact:
  - `lean-mathlib/Proofs/FeeAwareBatchKGap.lean`
  - `lean-mathlib/Proofs/FeeAwareAntiFragmentation.lean`
- Checker:
  - `cd lean-mathlib && lake build Proofs.FeeAwareBatchKGap Proofs.FeeAwareAntiFragmentation`
- Replay artifact:
  - `pytest -q tests/formal/test_lean_fee_aware_batch_k_gap.py tests/formal/test_lean_fee_aware_anti_fragmentation.py`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - fee-aware K-gap accounting and fee-aware same-pool anti-fragmentation theorems

### `value_aware_settlement_safety`

- Primary artifact:
  - `src/integration/settlement_end_to_end_certificate_packet.py`
  - `lean-mathlib/Proofs/ZenoDEXSettlementEndToEndCertificatePacket.lean`
  - `src/kernels/dex/settlement_end_to_end_certificate_packet_v1.yaml`
- Checker:
  - `cd lean-mathlib && lake build Proofs.ZenoDEXSettlementEndToEndCertificatePacket`
  - `pytest -q tests/formal/test_lean_settlement_end_to_end_certificate_packet.py tests/formal/test_esso_settlement_end_to_end_certificate_packet.py`
- Replay artifact:
  - `pytest -q tests/integration/test_settlement_end_to_end_certificate_packet.py tests/integration/test_settlement_strong_certificate.py`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - settlement-certificate posture with replay-bound strong certificate, feature-extension packet, value lane, and full price rails

### `proof_carrying_optimizer_certificates`

- Primary artifact:
  - `src/integration/exact_in_route_certificate.py`
  - `src/integration/exact_out_route_certificate.py`
  - `src/integration/settlement_end_to_end_certificate_packet.py`
- Checker:
  - `pytest -q tests/integration/test_exact_in_route_certificate.py tests/integration/test_exact_out_route_certificate.py tests/integration/test_settlement_end_to_end_certificate_packet.py`
- Replay artifact:
  - `pytest -q tests/integration/test_api_server_dex_api.py -k 'exact_in_route or exact_out_many_pool or settlement_end_to_end_certificate_packet'`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - public replayable optimizer and settlement certificate surfaces on the promoted audited boundary

### `anti_fragmentation_by_theorem`

- Primary artifact:
  - `lean-mathlib/Proofs/AntiFragmentation.lean`
  - `lean-mathlib/Proofs/FeeAwareAntiFragmentation.lean`
- Checker:
  - `cd lean-mathlib && lake build Proofs.AntiFragmentation Proofs.FeeAwareAntiFragmentation`
- Replay artifact:
  - `pytest -q tests/formal/test_lean_fee_aware_anti_fragmentation.py`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - zero-fee same-pool same-direction and fee-aware same-pool fragmentation surfaces

### `non_commutativity_quarantine`

- Primary artifact:
  - `lean-mathlib/Proofs/OppositeDirectionNoncommutativity.lean`
- Checker:
  - `cd lean-mathlib && lake build Proofs.OppositeDirectionNoncommutativity`
- Replay artifact:
  - `pytest -q tests/formal/test_lean_opposite_direction_noncommutativity.py`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - opposite-direction shared-reserve steps require explicit order quarantine

### `oracle_divergence_safety`

- Primary artifact:
  - `src/integration/zusd_oracle_contracts.py`
  - `src/tau_specs/recommended/zusd_cross_module_oracle_sync_gate_v1.tau`
- Checker:
  - `pytest -q tests/integration/test_zusd_oracle_contracts.py`
- Replay artifact:
  - `pytest -q tests/integration/test_settlement_price_provenance.py tests/integration/test_zusd_tau_gate.py`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - explicit divergence-and-lag oracle sync contract where deployments share oracle-world assumptions

### `liquidation_spiral_containment`

- Primary artifact:
  - `src/tau_specs/recommended/perp_risk_envelope_proof_gate_v1.tau`
  - `lean-mathlib/Proofs/PerpLiquidationInsuranceBound.lean`
- Checker:
  - `bash tests/tau/test_specs_syntax.sh`
  - `cd lean-mathlib && lake build Proofs.PerpLiquidationInsuranceBound`
- Replay artifact:
  - `python3 tools/tau_resource_load_bench.py --include-perp-risk-envelope`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - bounded-move solvency and risk-envelope containment posture

### `cross_layer_replay_parity`

- Primary artifact:
  - `tools/build_tau_active_semantic_parity_contract.py`
- Checker:
  - `pytest -q tests/tools/test_tau_active_semantic_parity_contract.py`
- Replay artifact:
  - `python3 tools/check_tau_active_semantic_parity.py --require-level semantic_contract`
- Release gate:
  - `python3 tools/check_shape_v1_ratchet.py`
- Domain:
  - active Tau specs and declared semantic source rank at the runtime boundary

## Public Claim

The public assurance statement for this release should be read as:

```text
On audited domain D_v1,
Shape++ is enforced by
(theorem set T, contract set C, replay set R, witness/checker set W),
and releases that regress those gates are rejected.
```

It should not be widened beyond `D_v1` without a new manifest revision.
