#!/usr/bin/env python3
"""Replay the frozen legacy baseline through the unmounted exact FCIS path.

The harness is evidence tooling only. It reconstructs independent input graphs,
binds both sides to the checked legacy artifact, derives an exact DecisionV1 and
CommitBundleV1, and compares one closed observable document. Any difference is
reported with the first canonical field path and blocks mount readiness.
"""

# ruff: noqa: E402 -- the executable tool must add the repository root before src imports

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, NoReturn

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.core.batch_clearing import compute_settlement
from src.core.fcis_authority_admission import (
    CanonicalAuthorityClaimBytesV1,
    encode_fcis_authority_claim_v1,
)
from src.core.fcis_commit_bundle_derivation import (
    CommitBundleV1,
    build_commit_bundle_v1,
)
from src.core.fcis_decision_derivation import (
    FCIS_SPOT_TRANSITION_BUDGET_V1,
    AcceptV1,
    CommittedFailureV1,
    RejectV1,
    evaluate_fcis_decision_v1,
)
from src.core.fcis_decision_values import (
    FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
    FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
    FCISRejectCodeV1,
    RejectionPathIndexPartV1,
    RejectionPathTextPartV1,
    RejectionReceiptClaimV1,
)
from src.core.fcis_outbox_values import FCIS_OUTBOX_PLAN_SCHEMA_ID_V1
from src.core.fcis_step_evaluation_values import FCISFeeAllocationV1, FCISStepEvaluationPhaseV1
from src.core.fcis_transition_values import (
    FCIS_COMMIT_PLAN_SCHEMA_ID_V1,
    FCIS_DEX_PATCH_SCHEMA_ID_V1,
    FCIS_EFFECTS_SCHEMA_ID_V1,
    FCIS_REPLAY_UPDATE_SCHEMA_ID_V1,
)
from src.core.settlement_snapshots import (
    canonical_owned_settlement_bytes_v1,
    snapshot_settlement,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from src.state.committed_dex_snapshot import canonical_committed_state_root_binding_v1
from src.state.fcis_committed_state_values import FCISCommittedStateSourceV1
from src.state.fcis_execution_context_values import (
    FCISFeeSplitPolicySourceV1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementModeV1,
    FCISStepExecutionContextSourceV1,
)
from src.state.intent_snapshots import admit_intent_batch
from src.state.legacy_state_snapshots import (
    admit_legacy_balance_for_differential_v1,
    admit_legacy_lp_for_differential_v1,
    admit_legacy_nonce_for_differential_v1,
    admit_legacy_pool_map_for_differential_v1,
)
from src.state.state_snapshots import (
    snapshot_fee_accumulator,
    snapshot_oracle,
    snapshot_perps,
    snapshot_vault,
)
from tools.build_fcis_m5_p4a_baseline import (
    _build_artifact as _build_legacy_artifact,
)
from tools.build_fcis_m5_p4a_baseline import (
    _build_fixture_inputs,
    _canonical_bytes,
    _execute_legacy,
    _execution_context_projection,
    _FixtureInput,
    _intent_dict,
    _snapshot_bytes,
    _snapshot_root,
)

_BASELINE_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_LEGACY_BASELINE_V1.json"
_REPORT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json"
_SCHEMA = "zenodex/fcis-m5-p4a-differential-replay/v1"
_UNAVAILABLE_LEGACY = "UNAVAILABLE_IN_LEGACY_V1"


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load_json_strict(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_bytes(), object_pairs_hook=_reject_duplicate_keys)
    if type(value) is not dict:
        raise ValueError(f"{path.name} must contain one JSON object")
    return value


def _fail(message: str) -> NoReturn:
    raise RuntimeError(message)


def _hex_claim(schema_id: str, value: object) -> str:
    encoded = encode_fcis_authority_claim_v1(schema_id, value)
    if type(encoded) is not CanonicalAuthorityClaimBytesV1:
        _fail(f"canonical claim encoding rejected for {schema_id}")
    return encoded.payload.hex()


def _digest_bytes(domain: str, payload: bytes) -> str:
    return sha256_hex(domain_sep_bytes(domain, version=1) + payload)


def _input_binding(fixture: _FixtureInput) -> dict[str, Any]:
    command_bytes = tuple(_canonical_bytes(_intent_dict(intent)) for intent in fixture.intents)
    context_bytes = _canonical_bytes(_execution_context_projection(fixture.config))
    state_bytes = _snapshot_bytes(fixture.state)
    return {
        "command_bytes": [value.hex() for value in command_bytes],
        "command_hash": sha256_hex(b"".join(command_bytes)),
        "state_snapshot_bytes": state_bytes.hex(),
        "state_snapshot_root": _snapshot_root(fixture.state),
        "context_bytes": context_bytes.hex(),
        "context_hash": _digest_bytes("fcis_p4a_execution_context", context_bytes),
    }


def _state_source(fixture: _FixtureInput) -> FCISCommittedStateSourceV1:
    state = fixture.state
    return FCISCommittedStateSourceV1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        vault=snapshot_vault(state.vault),
        oracle=snapshot_oracle(state.oracle),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
        perps=snapshot_perps(state.perps),
    )


def _context_source(fixture: _FixtureInput) -> FCISStepExecutionContextSourceV1:
    config = fixture.config
    fee_policy = None
    if config.fee_split_params is not None:
        fee_policy = FCISFeeSplitPolicySourceV1(
            config.fee_split_params.buyback_bps,
            config.fee_split_params.treasury_bps,
            config.fee_split_params.rewards_bps,
        )
    return FCISStepExecutionContextSourceV1(
        settlement=FCISSettlementExecutionContextSourceV1(
            now=700,
            min_lp_position_age_seconds=0,
            mode=FCISSettlementModeV1(config.settlement_validation),
            allow_cow_netting=_execution_context_projection(config)["allow_cow_netting"],
            allow_snapshot_bound_quote_bindings=(config.allow_snapshot_bound_quote_bindings),
            protocol_fee_share_bps=config.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=config.protocol_fee_recipient_pubkey,
        ),
        require_all_nonces=config.requires_complete_nonce_coverage(),
        reject_settlements_with_rejected_intents=(config.reject_settlements_with_rejected_intents),
        fee_split_policy=fee_policy,
        lp_duration_policy=None,
        snapshot_version=4,
    )


def _candidate_settlement(fixture: _FixtureInput) -> object:
    if fixture.candidate_settlement is not None:
        return fixture.candidate_settlement
    return compute_settlement(
        intents=fixture.intents,
        pools=fixture.state.pools,
        balances=fixture.state.balances,
        lp_balances=fixture.state.lp_balances,
        swap_ordering=fixture.config.swap_ordering,
        protocol_fee_share_bps=fixture.config.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=(fixture.config.protocol_fee_recipient_pubkey),
    )


def _legacy_observation(record: dict[str, Any]) -> dict[str, Any]:
    accepted = bool(record["accepted"])
    marker = {"status": _UNAVAILABLE_LEGACY}
    return {
        "result_kind": "accept" if accepted else "reject",
        "rejection": record["rejection"],
        "next_state_snapshot_bytes": (record["next_state_snapshot_bytes"] if accepted else None),
        "next_state_snapshot_root": (record["next_state_snapshot_root"] if accepted else None),
        "settlement_bytes": record["settlement_bytes"] if accepted else None,
        "total_swap_fees": record["total_swap_fees"] if accepted else None,
        "fee_allocation": record["fee_split"] if accepted else None,
        "next_nonce_table_hash": record["next_nonces_hash"] if accepted else None,
        "patch_bytes": dict(marker) if accepted else None,
        "commit_plan_bytes": dict(marker) if accepted else None,
        "effects_bytes": dict(marker) if accepted else None,
        "replay_bytes": dict(marker) if accepted else None,
        "receipt_bytes": dict(marker),
        "receipt_root": dict(marker),
        "outbox_bytes": dict(marker) if accepted else None,
        "outbox_identities": dict(marker) if accepted else None,
        "bundle_bytes": dict(marker) if accepted else None,
        "bundle_root": dict(marker) if accepted else None,
        "algorithm_id": "legacy_dex_step",
        "algorithm_version": 1,
        "schema_version": 1,
        "codec_version": 1,
        "snapshot_version": 4,
        "support_root_version": 4,
        "support_root": record["next_support_root_v4"] if accepted else None,
    }


def _path_projection(receipt: RejectionReceiptClaimV1) -> list[str | int]:
    result: list[str | int] = []
    for part in receipt.path:
        if type(part) is RejectionPathTextPartV1:
            result.append(part.text)
        elif type(part) is RejectionPathIndexPartV1:
            result.append(part.index)
        else:
            _fail("exact rejection path escaped its closed grammar")
    return result


def _exact_rejection(decision: RejectV1) -> dict[str, Any]:
    receipt = decision.receipt
    phase = tuple(FCISStepEvaluationPhaseV1)[receipt.phase.member_ordinal].value
    code = tuple(FCISRejectCodeV1)[receipt.code.member_ordinal].value
    return {
        "code": code,
        "path": _path_projection(receipt),
        "precedence": phase,
        "public_reason": receipt.public_reason,
        "unavailable_fields": [],
    }


def _fee_projection(fee: FCISFeeAllocationV1 | None) -> dict[str, int] | None:
    if fee is None:
        return None
    return {
        "buyback_amount": fee.buyback_amount,
        "treasury_amount": fee.treasury_amount,
        "rewards_amount": fee.rewards_amount,
        "dust_carried": fee.dust_carried,
    }


def _nonce_table_hash(entries: tuple[tuple[str, int], ...]) -> str:
    payload = canonical_json_bytes([[pubkey, nonce] for pubkey, nonce in entries])
    return _digest_bytes("fcis_nonce_table", payload)


def _exact_observation(fixture: _FixtureInput) -> dict[str, Any]:
    decision = evaluate_fcis_decision_v1(
        state_source=_state_source(fixture),
        settlement=snapshot_settlement(_candidate_settlement(fixture)),
        intents=admit_intent_batch(fixture.intents),
        context=_context_source(fixture),
        budget=FCIS_SPOT_TRANSITION_BUDGET_V1,
    )
    if type(decision) is RejectV1:
        receipt = decision.receipt
        return {
            "result_kind": "reject",
            "rejection": _exact_rejection(decision),
            "next_state_snapshot_bytes": None,
            "next_state_snapshot_root": None,
            "settlement_bytes": None,
            "total_swap_fees": None,
            "fee_allocation": None,
            "next_nonce_table_hash": None,
            "patch_bytes": None,
            "commit_plan_bytes": None,
            "effects_bytes": None,
            "replay_bytes": None,
            "receipt_bytes": _hex_claim(FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1, receipt),
            "receipt_root": _digest_bytes(
                FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
                bytes.fromhex(_hex_claim(FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1, receipt)),
            ),
            "outbox_bytes": None,
            "outbox_identities": None,
            "bundle_bytes": None,
            "bundle_root": None,
            "algorithm_id": receipt.algorithm_id,
            "algorithm_version": receipt.algorithm_version,
            "schema_version": receipt.schema_version,
            "codec_version": receipt.codec_version,
            "snapshot_version": None,
            "support_root_version": None,
            "support_root": None,
        }
    if type(decision) is CommittedFailureV1:
        _fail("current spot profile unexpectedly emitted CommittedFailureV1")
    if type(decision) is not AcceptV1:
        _fail(f"unexpected exact decision: {type(decision).__name__}")
    bundle = build_commit_bundle_v1(decision)
    if type(bundle) is not CommitBundleV1:
        _fail("accepted exact decision did not derive one commit bundle")
    plan = decision.commit_plan
    settlement_bytes = canonical_owned_settlement_bytes_v1(plan.effects.settlement)
    snapshot_bytes, _preimage, snapshot_root = canonical_committed_state_root_binding_v1(
        decision.next_state,
        decision.receipt.binding.snapshot_version,
    )
    receipt_bytes = _hex_claim(FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1, decision.receipt)
    outbox_identities = [
        {
            "effect_index": record.effect_index,
            "effect_identity": record.effect_identity,
            "idempotency_key": record.idempotency_key,
        }
        for record in bundle.outbox_plan.records
    ]
    binding = decision.receipt.binding
    return {
        "result_kind": "accept",
        "rejection": None,
        "next_state_snapshot_bytes": snapshot_bytes.hex(),
        "next_state_snapshot_root": snapshot_root,
        "settlement_bytes": settlement_bytes.hex(),
        "total_swap_fees": plan.effects.total_swap_fees,
        "fee_allocation": _fee_projection(plan.effects.fee_allocation),
        "next_nonce_table_hash": _nonce_table_hash(decision.next_state.nonces.entries),
        "patch_bytes": _hex_claim(FCIS_DEX_PATCH_SCHEMA_ID_V1, plan.patch),
        "replay_bytes": _hex_claim(FCIS_REPLAY_UPDATE_SCHEMA_ID_V1, plan.replay),
        "receipt_bytes": receipt_bytes,
        "receipt_root": bundle.receipt_root,
        "outbox_bytes": _hex_claim(FCIS_OUTBOX_PLAN_SCHEMA_ID_V1, bundle.outbox_plan),
        "outbox_identities": outbox_identities,
        "bundle_bytes": bundle.canonical_bundle_bytes.hex(),
        "bundle_root": bundle.bundle_root,
        "algorithm_id": binding.algorithm_id,
        "algorithm_version": binding.algorithm_version,
        "schema_version": binding.schema_version,
        "codec_version": binding.codec_version,
        "snapshot_version": binding.snapshot_version,
        "support_root_version": binding.support_root_version,
        "support_root": binding.support_root,
        "commit_plan_bytes": _hex_claim(FCIS_COMMIT_PLAN_SCHEMA_ID_V1, plan),
        "effects_bytes": _hex_claim(FCIS_EFFECTS_SCHEMA_ID_V1, plan.effects),
    }


def _first_difference(left: Any, right: Any, path: str = "$") -> str | None:
    if type(left) is not type(right):
        return path
    if type(left) is dict:
        left_keys = set(left)
        right_keys = set(right)
        for key in sorted(left_keys | right_keys):
            next_path = f"{path}.{key}"
            if key not in left_keys or key not in right_keys:
                return next_path
            difference = _first_difference(left[key], right[key], next_path)
            if difference is not None:
                return difference
        return None
    if type(left) is list:
        if len(left) != len(right):
            return f"{path}.length"
        for index, (left_item, right_item) in enumerate(zip(left, right, strict=True)):
            difference = _first_difference(left_item, right_item, f"{path}[{index}]")
            if difference is not None:
                return difference
        return None
    return None if left == right else path


def compare_observations_v1(legacy: dict[str, Any], exact: dict[str, Any]) -> dict[str, Any]:
    first_difference = _first_difference(legacy, exact)
    return {
        "parity": "MATCH" if first_difference is None else "DIVERGENCE",
        "first_difference_path": first_difference,
        "legacy": legacy,
        "exact": exact,
    }


def _checked_baseline() -> dict[str, Any]:
    stored = _load_json_strict(_BASELINE_PATH)
    regenerated = _build_legacy_artifact()
    if canonical_json_bytes(stored) != canonical_json_bytes(regenerated):
        _fail("stored legacy baseline is stale or was not produced by the legacy builder")
    return stored


def _verify_fixture_binding(
    baseline: dict[str, Any], legacy: _FixtureInput, exact: _FixtureInput
) -> dict[str, Any]:
    expected = {
        "command_bytes": baseline["canonical_command_bytes"],
        "command_hash": baseline["canonical_command_hash"],
        "state_snapshot_bytes": baseline["pre_state_snapshot_bytes"],
        "state_snapshot_root": baseline["pre_state_snapshot_root"],
        "context_bytes": baseline["execution_context_bytes"],
        "context_hash": baseline["execution_context_hash"],
    }
    legacy_binding = _input_binding(legacy)
    exact_binding = _input_binding(exact)
    return {
        "same_input_binding": legacy_binding == exact_binding == expected,
        "expected": expected,
        "legacy": legacy_binding,
        "exact": exact_binding,
    }


def _build_report() -> dict[str, Any]:
    baseline_artifact = _checked_baseline()
    baseline_by_id = {fixture["fixture_id"]: fixture for fixture in baseline_artifact["fixtures"]}
    legacy_inputs = {fixture.fixture_id: fixture for fixture in _build_fixture_inputs()}
    exact_inputs = {fixture.fixture_id: fixture for fixture in _build_fixture_inputs()}
    if set(baseline_by_id) != set(legacy_inputs) or set(legacy_inputs) != set(exact_inputs):
        _fail("fixture inventories differ between baseline, legacy, and exact replay")

    results: list[dict[str, Any]] = []
    for fixture_id in sorted(baseline_by_id):
        baseline = baseline_by_id[fixture_id]
        legacy_fixture = legacy_inputs[fixture_id]
        exact_fixture = exact_inputs[fixture_id]
        binding = _verify_fixture_binding(baseline, legacy_fixture, exact_fixture)
        legacy_record = _execute_legacy(legacy_fixture)
        if canonical_json_bytes(legacy_record) != canonical_json_bytes(baseline):
            _fail(f"legacy replay diverged from frozen baseline: {fixture_id}")
        legacy_observation = _legacy_observation(legacy_record)
        exact_observation = _exact_observation(exact_fixture)
        comparison = compare_observations_v1(legacy_observation, exact_observation)
        if not binding["same_input_binding"]:
            comparison["parity"] = "DIVERGENCE"
            comparison["first_difference_path"] = "$.input_binding"
        results.append(
            {
                "fixture_id": fixture_id,
                "command_kind": baseline["command_kind"],
                "input_binding": binding,
                "comparison": comparison,
            }
        )
    match_count = sum(result["comparison"]["parity"] == "MATCH" for result in results)
    divergence_count = len(results) - match_count
    report: dict[str, Any] = {
        "schema": _SCHEMA,
        "baseline_artifact_sha256": baseline_artifact["artifact_sha256"],
        "baseline_generator_hash": baseline_artifact["generator_hash"],
        "baseline_source_tree_hash": baseline_artifact["source_tree_hash"],
        "observable_fields": sorted(_legacy_observation(baseline_artifact["fixtures"][0])),
        "fixtures": results,
        "fixture_count": len(results),
        "match_count": match_count,
        "divergence_count": divergence_count,
        "parity_complete": divergence_count == 0,
        "reviewed_expected_difference_allowlist": [],
    }
    report["artifact_sha256"] = "0x" + hashlib.sha256(canonical_json_bytes(report)).hexdigest()
    return report


def _write_report(report: dict[str, Any]) -> None:
    _REPORT_PATH.write_bytes(canonical_json_bytes(report))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--require-parity", action="store_true")
    args = parser.parse_args()
    report = _build_report()
    rendered = canonical_json_bytes(report)
    if args.check:
        if not _REPORT_PATH.exists() or _REPORT_PATH.read_bytes() != rendered:
            print("ERROR: differential replay artifact is stale", file=sys.stderr)
            return 1
    else:
        _write_report(report)
    if args.require_parity and not report["parity_complete"]:
        print(
            f"BLOCKED: {report['divergence_count']} differential divergences",
            file=sys.stderr,
        )
        return 1
    print(
        "OK: differential artifact current "
        f"(matches={report['match_count']}, divergences={report['divergence_count']})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
