#!/usr/bin/env python3
"""Build source-bound P4B1 evidence for mounted LP metadata refinement.

P4B0 compared the exact FCIS evaluator with ``src.core.dex.step``.  The core
step cannot observe consensus time, while the mounted integration applies LP
duration metadata immediately after the settlement balances.  This bounded
checkpoint compares that complete mounted sequence with the exact evaluator.

The tool is evidence-only.  It does not mount FCIS authority or modify runtime
dispatch.
"""

# ruff: noqa: E402 -- executable tools add the repository root before src imports

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.core.batch_clearing import apply_settlement_pure, is_cow_pair_netting_ordering
from src.core.dex import DexState
from src.core.fcis_legacy_refinement_admission import (
    decode_canonical_evidence_artifact_bytes_v1,
)
from src.core.fcis_legacy_refinement_values import CanonicalParseRejectV1
from src.core.fees import split_fee_with_dust_carry
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.fcis_spot_shadow import (
    FCISSpotShadowContextV1,
    FCISStepShadowContextV1,
    FCISStepShadowReceiptV1,
    evaluate_fcis_step_shadow_v1,
)
from src.integration.lp_position_age_gate import apply_lp_mint_timestamps_after_settlement
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch
from tools.build_fcis_m5_p4a_baseline import (
    _build_fixture_inputs,
    _canonical_bytes,
    _execution_context_projection,
    _FixtureInput,
    _intent_dict,
    _settlement_op_dict,
    _snapshot_bytes,
)
from tools.run_fcis_m5_p4a_differential_replay import _candidate_settlement

P4B1_SCHEMA_V1 = "zenodex/fcis-m5-p4b1-mounted-lp-refinement/v1"
P4B1_PROFILE_ID_V1 = "mounted_spot_v1"
P4B1_TIMESTAMP_MAX_V1 = (1 << 63) - 1
P4B1_TIMESTAMPS_V1 = (0, 1, 700, P4B1_TIMESTAMP_MAX_V1)
P4B1_FIXTURE_IDS_V1 = (
    "add_liquidity_boundary_valid",
    "add_liquidity_smallest_accepted",
    "create_pool_smallest_accepted",
    "remove_liquidity_boundary_valid",
    "remove_liquidity_smallest_accepted",
    "swap_exact_in_smallest_accepted",
)
P4B1_ARTIFACT_PATH_V1 = Path("docs/research/FCIS_M5_P4B1_MOUNTED_LP_REFINEMENT_V1.json")
P4B1_SOURCE_PATHS_V1 = (
    Path("src/core/batch_clearing.py"),
    Path("src/core/fcis_step_evaluator.py"),
    Path("src/integration/dex_engine.py"),
    Path("src/integration/fcis_spot_shadow.py"),
    Path("src/integration/lp_position_age_gate.py"),
    Path("src/state/lp_duration_transitions.py"),
    Path("tools/build_fcis_m5_p4a_baseline.py"),
    Path("tools/run_fcis_m5_p4a_differential_replay.py"),
    Path("tools/build_fcis_m5_p4b1_mounted_lp_refinement.py"),
    Path("tests/integration/test_fcis_m5_p4b1_mounted_lp_refinement.py"),
)

_LOGICAL_STATE_FIELDS_V1 = (
    "balances",
    "pools",
    "lp_balances",
    "nonces",
    "vault",
    "oracle",
    "fee_accumulator",
    "perps",
)


def _digest(domain: str, payload: bytes) -> str:
    return sha256_hex(domain_sep_bytes(domain, version=1) + payload)


def _source_hashes(repo_root: Path) -> dict[str, str]:
    return {
        path.as_posix(): sha256_hex((repo_root / path).read_bytes())
        for path in P4B1_SOURCE_PATHS_V1
    }


def _selected_fixtures() -> dict[str, _FixtureInput]:
    inventory = {fixture.fixture_id: fixture for fixture in _build_fixture_inputs()}
    missing = sorted(set(P4B1_FIXTURE_IDS_V1).difference(inventory))
    if missing:
        raise ValueError(f"P4B1 fixture inventory missing: {missing}")
    return {fixture_id: inventory[fixture_id] for fixture_id in P4B1_FIXTURE_IDS_V1}


def _context_source(fixture: _FixtureInput, now: int) -> dict[str, object]:
    return {
        "comparison_profile": P4B1_PROFILE_ID_V1,
        "now": now,
        "core_context": _execution_context_projection(fixture.config),
        "lp_duration_policy": None,
    }


def _input_binding(fixture: _FixtureInput, now: int) -> dict[str, object]:
    command_bytes = tuple(_canonical_bytes(_intent_dict(intent)) for intent in fixture.intents)
    state_bytes = _snapshot_bytes(fixture.state)
    context_bytes = canonical_json_bytes(_context_source(fixture, now))
    return {
        "command_hash": _digest("fcis_p4b1_command", b"".join(command_bytes)),
        "context_hash": _digest("fcis_p4b1_context", context_bytes),
        "pre_state_root": snapshot_from_state(fixture.state, version=4).commitment_hex(),
        "input_hash": _digest(
            "fcis_p4b1_input",
            b"".join(command_bytes) + state_bytes + context_bytes,
        ),
    }


def _shadow_context(fixture: _FixtureInput, now: int) -> FCISStepShadowContextV1:
    config = fixture.config
    return FCISStepShadowContextV1(
        settlement=FCISSpotShadowContextV1(
            now=now,
            min_lp_position_age_seconds=0,
            mode=config.settlement_validation,
            allow_cow_netting=is_cow_pair_netting_ordering(config.swap_ordering),
            allow_snapshot_bound_quote_bindings=config.allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=config.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=config.protocol_fee_recipient_pubkey,
        ),
        require_all_nonces=config.requires_complete_nonce_coverage(),
        reject_settlements_with_rejected_intents=(config.reject_settlements_with_rejected_intents),
        fee_split_params=config.fee_split_params,
        snapshot_version=4,
    )


def _mounted_next_state(
    fixture: _FixtureInput,
    settlement: object,
    now: int,
) -> DexState:
    from src.core.settlement import Settlement

    if type(settlement) is not Settlement:
        raise TypeError("P4B1 settlement must be exact")
    admitted_settlement = cast(Settlement, settlement)
    nonce_ok, nonce_error, next_nonces = validate_and_apply_intent_nonce_batch(
        nonces=fixture.state.nonces,
        intents=fixture.intents,
        require_all_nonces=fixture.config.requires_complete_nonce_coverage(),
    )
    if not nonce_ok or nonce_error is not None or type(next_nonces) is not NonceTable:
        raise ValueError(f"P4B1 mounted nonce transition rejected: {nonce_error}")
    next_balances, next_pools, next_lp = apply_settlement_pure(
        settlement=admitted_settlement,
        balances=fixture.state.balances,
        pools=fixture.state.pools,
        lp_balances=fixture.state.lp_balances,
    )
    duration_error = apply_lp_mint_timestamps_after_settlement(
        lp_balances=next_lp,
        settlement=admitted_settlement,
        block_timestamp=now,
        duration_risk_policy=None,
    )
    if duration_error is not None:
        raise ValueError(f"P4B1 mounted LP duration transition rejected: {duration_error}")
    next_fees = fixture.state.fee_accumulator
    if fixture.config.fee_split_params is not None:
        total_fees = sum(int(fill.fee_paid or 0) for fill in admitted_settlement.fills)
        _allocation, next_fees = split_fee_with_dust_carry(
            total_fees,
            fixture.config.fee_split_params,
            fixture.state.fee_accumulator,
        )
    return DexState(
        balances=next_balances,
        pools=next_pools,
        lp_balances=next_lp,
        nonces=next_nonces,
        vault=fixture.state.vault,
        oracle=fixture.state.oracle,
        fee_accumulator=next_fees,
        perps=fixture.state.perps,
    )


def _decoded_snapshot(payload: bytes) -> dict[str, object]:
    decoded = decode_canonical_evidence_artifact_bytes_v1(payload)
    if type(decoded) is CanonicalParseRejectV1 or type(decoded) is not dict:
        raise ValueError("P4B1 exact evaluator emitted a noncanonical snapshot")
    return cast(dict[str, object], decoded)


def _logical_field_sources(snapshot: dict[str, object]) -> dict[str, object]:
    required = {
        "balances",
        "pools",
        "lp_balances",
        "lp_mint_timestamps",
        "lp_duration_risk",
        "nonces",
        "vault",
        "oracle",
        "fee_accumulator",
        "perps",
    }
    if not required.issubset(snapshot):
        missing = sorted(required.difference(snapshot))
        raise ValueError(f"P4B1 snapshot missing committed fields: {missing}")
    return {
        "balances": snapshot["balances"],
        "pools": snapshot["pools"],
        "lp_balances": {
            "balances": snapshot["lp_balances"],
            "duration_risk": snapshot["lp_duration_risk"],
            "mint_timestamps": snapshot["lp_mint_timestamps"],
        },
        "nonces": snapshot["nonces"],
        "vault": snapshot["vault"],
        "oracle": snapshot["oracle"],
        "fee_accumulator": snapshot["fee_accumulator"],
        "perps": snapshot["perps"],
    }


def _field_hashes(snapshot: dict[str, object]) -> dict[str, str]:
    sources = _logical_field_sources(snapshot)
    if tuple(sources) != _LOGICAL_STATE_FIELDS_V1:
        raise ValueError("P4B1 logical state-field order drifted")
    return {
        name: _digest(f"fcis_p4b1_state_field_{name}", canonical_json_bytes(value))
        for name, value in sources.items()
    }


def _build_row(
    mounted_fixture: _FixtureInput,
    exact_fixture: _FixtureInput,
    now: int,
) -> dict[str, object]:
    mounted_pre = _snapshot_bytes(mounted_fixture.state)
    exact_pre = _snapshot_bytes(exact_fixture.state)
    mounted_binding = _input_binding(mounted_fixture, now)
    exact_binding = _input_binding(exact_fixture, now)
    mounted_settlement = _candidate_settlement(mounted_fixture)
    exact_settlement = _candidate_settlement(exact_fixture)
    settlement_equal = canonical_json_bytes(_settlement_op_dict(mounted_settlement)) == (
        canonical_json_bytes(_settlement_op_dict(exact_settlement))
    )
    mounted_state = _mounted_next_state(mounted_fixture, mounted_settlement, now)
    exact_result = evaluate_fcis_step_shadow_v1(
        state=exact_fixture.state,
        settlement=exact_settlement,
        intents=exact_fixture.intents,
        context=_shadow_context(exact_fixture, now),
        lp_duration_policy=None,
    )
    if type(exact_result) is not FCISStepShadowReceiptV1:
        raise ValueError(
            f"P4B1 exact evaluator rejected {exact_fixture.fixture_id}@{now}: "
            f"{getattr(exact_result, 'reason', 'unknown rejection')}"
        )
    mounted_snapshot = snapshot_from_state(mounted_state, version=4)
    exact_snapshot = _decoded_snapshot(exact_result.canonical_snapshot_bytes)
    mounted_field_hashes = _field_hashes(cast(dict[str, object], mounted_snapshot.data))
    exact_field_hashes = _field_hashes(exact_snapshot)
    mounted_root = mounted_snapshot.commitment_hex()
    parity = (
        mounted_binding == exact_binding
        and settlement_equal
        and mounted_snapshot.canonical_bytes() == exact_result.canonical_snapshot_bytes
        and mounted_root == exact_result.snapshot_commitment == exact_result.state_root
        and mounted_field_hashes == exact_field_hashes
    )
    if _snapshot_bytes(mounted_fixture.state) != mounted_pre:
        raise RuntimeError("P4B1 mounted comparison mutated its pre-state")
    if _snapshot_bytes(exact_fixture.state) != exact_pre:
        raise RuntimeError("P4B1 exact comparison mutated its pre-state")
    return {
        "fixture_id": mounted_fixture.fixture_id,
        "command_kind": mounted_fixture.command_kind,
        "now": now,
        "input_binding": mounted_binding,
        "same_input_binding": mounted_binding == exact_binding,
        "settlement_equal": settlement_equal,
        "mounted_state_root": mounted_root,
        "exact_state_root": exact_result.state_root,
        "exact_support_root": exact_result.support_root,
        "mounted_field_hashes": mounted_field_hashes,
        "exact_field_hashes": exact_field_hashes,
        "parity": "REFINES" if parity else "MISMATCH",
    }


def _payload_without_hash(artifact: dict[str, object]) -> dict[str, object]:
    return {key: value for key, value in artifact.items() if key != "artifact_sha256"}


def _build_artifact(repo_root: Path = _REPO_ROOT) -> dict[str, object]:
    mounted_fixtures = _selected_fixtures()
    exact_fixtures = _selected_fixtures()
    rows = [
        _build_row(mounted_fixtures[fixture_id], exact_fixtures[fixture_id], now)
        for fixture_id in P4B1_FIXTURE_IDS_V1
        for now in P4B1_TIMESTAMPS_V1
    ]
    refine_count = sum(row["parity"] == "REFINES" for row in rows)
    payload: dict[str, object] = {
        "schema": P4B1_SCHEMA_V1,
        "comparison_profile": P4B1_PROFILE_ID_V1,
        "timestamp_max": P4B1_TIMESTAMP_MAX_V1,
        "timestamps": list(P4B1_TIMESTAMPS_V1),
        "fixture_ids": list(P4B1_FIXTURE_IDS_V1),
        "logical_state_fields": list(_LOGICAL_STATE_FIELDS_V1),
        "row_count": len(rows),
        "refine_count": refine_count,
        "mismatch_count": len(rows) - refine_count,
        "verdict": "READY_FOR_P4B2" if refine_count == len(rows) else "BLOCKED",
        "mount_authorized": False,
        "source_hashes": _source_hashes(repo_root),
        "rows": rows,
    }
    artifact = dict(payload)
    artifact["artifact_sha256"] = sha256_hex(canonical_json_bytes(payload))
    return artifact


def check_artifact_bytes_v1(
    raw: bytes,
    *,
    repo_root: Path = _REPO_ROOT,
) -> tuple[bool, str]:
    decoded = decode_canonical_evidence_artifact_bytes_v1(raw)
    if type(decoded) is CanonicalParseRejectV1 or type(decoded) is not dict:
        return False, "artifact_decode_rejected"
    observed = cast(dict[str, object], decoded)
    stored_hash = observed.get("artifact_sha256")
    if stored_hash != sha256_hex(canonical_json_bytes(_payload_without_hash(observed))):
        return False, "artifact_self_hash_mismatch"
    expected = _build_artifact(repo_root)
    if canonical_json_bytes(observed) != canonical_json_bytes(expected):
        return False, "artifact_semantic_or_source_drift"
    if observed.get("mismatch_count") != 0 or observed.get("verdict") != "READY_FOR_P4B2":
        return False, "mounted_lp_refinement_incomplete"
    if observed.get("mount_authorized") is not False:
        return False, "artifact_must_not_authorize_mount"
    return True, "ok"


def _write_artifact(artifact: dict[str, object], repo_root: Path) -> None:
    path = repo_root / P4B1_ARTIFACT_PATH_V1
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(artifact))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    artifact = _build_artifact()
    path = _REPO_ROOT / P4B1_ARTIFACT_PATH_V1
    if args.check:
        if not path.exists():
            print("ERROR: P4B1 artifact missing", file=sys.stderr)
            return 1
        ok, reason = check_artifact_bytes_v1(path.read_bytes())
        if not ok:
            print(f"ERROR: P4B1 artifact rejected: {reason}", file=sys.stderr)
            return 1
        print(
            "OK: P4B1 mounted LP refinement "
            f"({artifact['refine_count']}/{artifact['row_count']} refine; mount_authorized=false)"
        )
        return 0
    _write_artifact(artifact, _REPO_ROOT)
    print(
        f"OK: wrote {P4B1_ARTIFACT_PATH_V1} "
        f"({artifact['refine_count']}/{artifact['row_count']} refine; mount_authorized=false)"
    )
    return 0 if artifact["mismatch_count"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
