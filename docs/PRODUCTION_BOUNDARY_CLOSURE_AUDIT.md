---
title: Production Boundary Closure Audit
type: note
permalink: autonomous-tau-dex-review/docs/production-boundary-closure-audit
---

# Production Boundary Closure Audit

Date: 2026-05-17

This audit maps the production-boundary backlog item to replayable local
evidence. The gate is:

```bash
python3 tools/check_production_boundary.py --json
```

Current schema:

```text
zenodex/production_boundary_audit/v0
```

Current result:

```text
ok = true
```

## Requirement Map

| Backlog requirement | Audit requirement id | Required checks |
| --- | --- | --- |
| Confirm value-moving paths all go through safe profile. | `value_moving_paths_use_safe_profile` | `dex_engine_defaults_fail_closed`, `core_dex_defaults_use_strong_settlement_profile`, `named_safe_profiles_force_production_closure`, `public_operator_node_preflight_blocks_unsigned_testnet_mutation` |
| No production nonce-free path. | `no_production_nonce_free_path` | `dex_engine_defaults_fail_closed`, `named_safe_profiles_force_production_closure`, `nonce_free_value_moving_batch_rejected`, `public_operator_node_preflight_blocks_unsigned_testnet_mutation` |
| No legacy settlement validation in production. | `no_legacy_settlement_validation_in_production` | `core_dex_defaults_use_strong_settlement_profile`, `integration_validation_uses_strong_settlement_validator`, `production_src_has_no_legacy_settlement_profile_literals` |
| No `require_settlement_match=false` in production. | `no_require_settlement_match_false_in_production` | `dex_engine_defaults_fail_closed`, `named_safe_profiles_force_production_closure`, `production_src_has_no_unsafe_dex_config_literals` |
| No direct pure-core ingress accidentally exposed. | `no_direct_pure_core_ingress_exposed` | `direct_settlement_apply_helper_unexposed`, `api_server_does_not_expose_direct_value_moving_core_ingress` |
| Classify the declared historical Tau projection without authority promotion. | `retired_tau_declared_projection_classified` | `retired_tau_bridge_classified_without_production_authority` |

The historical Tau plugin no longer receives positive production credit. The
separate bounded check replays the O-003B dependency classification,
requires all three dispositions, requires zero added import edges, and requires
all production, release, settlement, and value-movement authority fields to
remain `NONE`. It does not satisfy the broad safe-profile or direct-ingress
requirements. Its static scope and later O-007B/C obligations are recorded in
the certificate nonclaims.

## Safe Profile Evidence

`named_safe_profiles_force_production_closure` force-checks the named strict
UPBA and fail-closed ZenoOracle profiles even when unsafe override parameters
are supplied. The strict UPBA facts include:

```text
allow_uniform_batch_certificate = true
require_uniform_batch_certificate_for_supported_swaps = true
require_uniform_batch_optimality_certificate = true
require_uniform_batch_v2_bounded_grid_optimality = true
require_uniform_batch_v3_exact_out_grid_optimality = true
```

This binds the production-boundary audit to the v2 bounded-grid and v3 exact-out
grid evidence paths.

## Replay Commands

```bash
python3 tools/check_production_boundary.py
pytest -q tests/test_check_production_boundary.py
pytest -q tests/test_security_posture_files.py
```

The release gate also runs the production-boundary checker:

```bash
bash tools/run_release_gate.sh
```

## Boundary

This audit is a local production-boundary closure check. It does not replace a
fresh two-machine latest-main run, network evidence archive, dependency
ratchet, ZK coverage, TEE privacy verification, or counsel review.
