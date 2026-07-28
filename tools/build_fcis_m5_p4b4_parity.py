#!/usr/bin/env python3
"""Build source-pinned direct parity evidence for unmounted FCIS P4B4."""

# ruff: noqa: E402 -- executable tools add the repository root before imports

from __future__ import annotations

import argparse
import dataclasses
import enum
import subprocess
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.core.fcis_settlement_strong_validator import (
    evaluate_settlement_strong_exact_v1,
)
from src.core.fcis_settlement_strong_values import (
    ExactSpotPreStateV1,
    ExactStrongSettlementCandidateV1,
    ExactStrongSettlementRejectV1,
    StrongSettlementContextV1,
)
from src.core.settlement_snapshots import (
    OwnedSettlementV1,
    canonical_owned_settlement_bytes_v1,
)
from src.core.settlement_strong_validator import (
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
    _evaluate_settlement_strong_admitted_observed_v5,
)
from src.state.canonical import canonical_json_bytes, sha256_hex
from src.state.fcis_execution_context_values import settlement_mode_label_v1
from src.state.intent_snapshots import OwnedIntentV1, canonical_owned_intent_bytes_v1
from src.state.intents import IntentKind
from src.state.owned_collections import OwnedEnumV1, OwnedMapV1
from src.state.owned_json import snapshot_owned_json_object
from tests.core.test_fcis_settlement_strong_parity import _empty_settlement
from tests.core.test_fcis_settlement_strong_routes import (
    _cow_context,
    _cow_pre_state,
    _cow_settlement,
    _route_context,
    _route_fixture,
    route_pools,
)
from tests.core.test_fcis_settlement_strong_validator import (
    SWAP_AMOUNT_OUT,
    _add_liquidity_intent,
    _add_liquidity_settlement,
    _context,
    _create_pool_intent,
    _create_pool_pre_state,
    _create_pool_settlement,
    _empty_pre_state,
    _exact_out_intent,
    _exact_out_settlement,
    _liquidity_pre_state,
    _ordinary_reject_settlement,
    _proof_carrying_context,
    _protocol_fee_context,
    _protocol_fee_exact_out_settlement,
    _protocol_fee_settlement,
    _recipient_swap_intent,
    _recipient_swap_settlement,
    _remove_liquidity_intent,
    _remove_liquidity_settlement,
    _swap_intent,
    _swap_pre_state,
    _swap_settlement,
)

ARTIFACT_SCHEMA_V1 = "zenodex/fcis-m5-p4b4-direct-parity/v1"
ARTIFACT_PATH_V1 = Path("docs/research/FCIS_M5_P4B4_DIRECT_PARITY_V1.json")
REVIEWED_START_SHA_V1 = "99da842b6606e6f10ce8ab6b2c94c2d36f2e169f"
EXACT_ALGORITHM_V1 = "fcis-settlement-strong-exact-v1"
LEGACY_ALGORITHM_V1 = "settlement-strong-observed-v5"
SOURCE_PATHS_V1 = (
    Path("src/core/fcis_amm_dispatch.py"),
    Path("src/core/fcis_create_pool_event.py"),
    Path("src/core/fcis_liquidity_kernels.py"),
    Path("src/core/fcis_pool_fingerprint.py"),
    Path("src/core/fcis_settlement_index.py"),
    Path("src/core/fcis_settlement_strong_validator.py"),
    Path("src/core/fcis_settlement_strong_values.py"),
    Path("src/kernels/python/cpmm_exact_out_policy_v1.py"),
    Path("src/state/fcis_curve_config.py"),
    Path("src/state/fcis_pool_identity.py"),
    Path("src/state/fcis_spot_replay.py"),
    Path("tests/core/test_fcis_settlement_strong_parity.py"),
    Path("tests/core/test_fcis_settlement_strong_routes.py"),
    Path("tests/core/test_fcis_settlement_strong_validator.py"),
    Path("tools/build_fcis_m5_p4b4_parity.py"),
    Path("tools/check_fcis_m5_p4b4_parity.py"),
)
RUNTIME_SOURCE_PATHS_V1 = SOURCE_PATHS_V1[:11]


@dataclass(frozen=True, slots=True)
class _ParityFixtureV1:
    fixture_id: str
    settlement: OwnedSettlementV1
    intents: tuple[OwnedIntentV1, ...]
    pre_state: ExactSpotPreStateV1
    context: StrongSettlementContextV1


def _canonical_source(value: object) -> object:
    if value is None or type(value) in (bool, int, str):
        return value
    if type(value) is bytes:
        return "0x" + value.hex()
    if type(value) is tuple:
        return [_canonical_source(item) for item in cast(tuple[object, ...], value)]
    if type(value) is list:
        return [_canonical_source(item) for item in cast(list[object], value)]
    if type(value) is dict:
        mapping = cast(dict[str, object], value)
        return {key: _canonical_source(mapping[key]) for key in sorted(mapping)}
    if type(value) is OwnedEnumV1:
        exact = cast(OwnedEnumV1, value)
        return {
            "enum_tag_ordinal": exact.enum_tag_ordinal,
            "member_ordinal": exact.member_ordinal,
            "schema_revision": exact.schema_revision,
        }
    if type(value) is OwnedMapV1:
        exact_map = cast(OwnedMapV1[object, object], value)
        return {
            "entries": _canonical_source(exact_map.entries),
            "schema_id": exact_map.schema_id,
            "schema_revision": exact_map.schema_revision,
        }
    if isinstance(value, enum.Enum):
        return _canonical_source(value.value)
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return {
            field.name: _canonical_source(object.__getattribute__(value, field.name))
            for field in dataclasses.fields(value)
        }
    raise TypeError(f"unsupported parity projection type: {type(value).__name__}")


def _result_source(value: object) -> dict[str, object]:
    if type(value) in (ExactStrongSettlementCandidateV1, StrongSettlementStateCandidateV1):
        candidate = cast(
            ExactStrongSettlementCandidateV1 | StrongSettlementStateCandidateV1,
            value,
        )
        return {
            "balance_patch": _canonical_source(candidate.balance_patch),
            "balances": _canonical_source(candidate.balances),
            "kind": "ACCEPT",
            "lp_balances": _canonical_source(candidate.lp_balances),
            "lp_patch": _canonical_source(candidate.lp_patch),
            "pool_patch": _canonical_source(candidate.pool_patch),
            "pools": _canonical_source(candidate.pools),
        }
    if type(value) in (ExactStrongSettlementRejectV1, StrongSettlementRejectV1):
        reject = cast(ExactStrongSettlementRejectV1 | StrongSettlementRejectV1, value)
        return {"kind": "REJECT", "reason": reject.reason}
    raise TypeError("unsupported strong-settlement result")


def _trace_source(value: object) -> dict[str, object]:
    return cast(dict[str, object], _canonical_source(value))


def _first_mismatch_v1(
    legacy: object,
    exact: object,
    path: tuple[str | int, ...] = (),
) -> str:
    if type(legacy) is not type(exact):
        return "/".join(map(str, path)) or "$"
    if type(legacy) is dict:
        legacy_map = cast(dict[str, object], legacy)
        exact_map = cast(dict[str, object], exact)
        if tuple(sorted(legacy_map)) != tuple(sorted(exact_map)):
            return "/".join(map(str, path)) or "$"
        for key in sorted(legacy_map):
            mismatch = _first_mismatch_v1(
                legacy_map[key],
                exact_map[key],
                path + (key,),
            )
            if mismatch != "REFINE":
                return mismatch
        return "REFINE"
    if type(legacy) is list:
        legacy_list = cast(list[object], legacy)
        exact_list = cast(list[object], exact)
        if len(legacy_list) != len(exact_list):
            return "/".join(map(str, path)) or "$"
        for index, (legacy_item, exact_item) in enumerate(
            zip(legacy_list, exact_list, strict=True)
        ):
            mismatch = _first_mismatch_v1(
                legacy_item,
                exact_item,
                path + (index,),
            )
            if mismatch != "REFINE":
                return mismatch
        return "REFINE"
    return "REFINE" if legacy == exact else ("/".join(map(str, path)) or "$")


def _evaluate_fixture_v1(fixture: _ParityFixtureV1) -> dict[str, object]:
    exact = evaluate_settlement_strong_exact_v1(
        settlement=fixture.settlement,
        intents=fixture.intents,
        pre_state=fixture.pre_state,
        context=fixture.context,
    )
    settlement_context = fixture.context.settlement
    legacy = _evaluate_settlement_strong_admitted_observed_v5(
        settlement=fixture.settlement,
        intents=fixture.intents,
        pre_balances=fixture.pre_state.balances,
        pre_pools=fixture.pre_state.pools,
        pre_lp_balances=fixture.pre_state.lp_balances,
        now=settlement_context.now,
        min_lp_position_age_seconds=settlement_context.min_lp_position_age_seconds,
        lp_duration_policy=fixture.context.lp_duration_policy,
        mode=settlement_mode_label_v1(settlement_context.mode),
        allow_cow_netting=settlement_context.allow_cow_netting,
        allow_snapshot_bound_quote_bindings=(
            settlement_context.allow_snapshot_bound_quote_bindings
        ),
        protocol_fee_share_bps=settlement_context.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=(settlement_context.protocol_fee_recipient_pubkey),
    )
    exact_result = _result_source(exact.result)
    legacy_result = _result_source(legacy.result)
    exact_trace = _trace_source(exact.state_read_trace)
    legacy_trace = _trace_source(legacy.state_read_trace)
    mismatch = _first_mismatch_v1(
        {"result": legacy_result, "trace": legacy_trace},
        {"result": exact_result, "trace": exact_trace},
    )
    command_bytes = canonical_json_bytes(
        {
            "intents": [
                "0x" + canonical_owned_intent_bytes_v1(intent).hex() for intent in fixture.intents
            ]
        }
    )
    settlement_bytes = canonical_owned_settlement_bytes_v1(fixture.settlement)
    pre_state_bytes = canonical_json_bytes(_canonical_source(fixture.pre_state))
    context_bytes = canonical_json_bytes(_canonical_source(fixture.context))
    return {
        "canonical_command_bytes": "0x" + command_bytes.hex(),
        "canonical_settlement_bytes": "0x" + settlement_bytes.hex(),
        "context_bytes": "0x" + context_bytes.hex(),
        "context_hash": sha256_hex(context_bytes),
        "exact_observed_reads": exact_trace,
        "exact_result_projection": exact_result,
        "first_mismatch_path": mismatch,
        "fixture_id": fixture.fixture_id,
        "legacy_observed_reads": legacy_trace,
        "legacy_result_projection": legacy_result,
        "pre_state_root": sha256_hex(pre_state_bytes),
        "status": "REFINE" if mismatch == "REFINE" else "MISMATCH",
    }


def _fixtures_v1() -> tuple[_ParityFixtureV1, ...]:
    base_context = _context()
    swap = _swap_settlement()
    malformed_fill = replace(
        swap,
        fills=(replace(swap.fills[0], amount_out_filled=SWAP_AMOUNT_OUT + 1),),
    )
    malformed_delta = replace(
        swap,
        balance_deltas=(
            swap.balance_deltas[0],
            replace(swap.balance_deltas[1], delta_add=SWAP_AMOUNT_OUT - 1),
        ),
    )
    malformed_event = replace(
        swap,
        events=(snapshot_owned_json_object({"type": "UNEXPECTED"}),),
    )
    fixtures: list[_ParityFixtureV1] = [
        _ParityFixtureV1("empty_accept", _empty_settlement(), (), _empty_pre_state(), base_context),
        _ParityFixtureV1(
            "exact_in_accept", swap, (_swap_intent(),), _swap_pre_state(), base_context
        ),
        _ParityFixtureV1(
            "exact_out_accept",
            _exact_out_settlement(),
            (_exact_out_intent(),),
            _swap_pre_state(),
            base_context,
        ),
        _ParityFixtureV1(
            "create_pool_accept",
            _create_pool_settlement(),
            (_create_pool_intent(),),
            _create_pool_pre_state(),
            base_context,
        ),
        _ParityFixtureV1(
            "add_liquidity_accept",
            _add_liquidity_settlement(),
            (_add_liquidity_intent(),),
            _liquidity_pre_state(),
            base_context,
        ),
        _ParityFixtureV1(
            "remove_liquidity_accept",
            _remove_liquidity_settlement(),
            (_remove_liquidity_intent(),),
            _liquidity_pre_state(),
            base_context,
        ),
        _ParityFixtureV1(
            "ordinary_reject",
            _ordinary_reject_settlement(),
            (_swap_intent(),),
            _swap_pre_state(),
            base_context,
        ),
        _ParityFixtureV1(
            "malformed_fill_reject",
            malformed_fill,
            (_swap_intent(),),
            _swap_pre_state(),
            base_context,
        ),
        _ParityFixtureV1(
            "delta_mismatch_reject",
            malformed_delta,
            (_swap_intent(),),
            _swap_pre_state(),
            base_context,
        ),
        _ParityFixtureV1(
            "event_mismatch_reject",
            malformed_event,
            (_swap_intent(),),
            _swap_pre_state(),
            base_context,
        ),
        _ParityFixtureV1(
            "proof_witness_accept",
            _exact_out_settlement(reserve_witnesses=True),
            (_exact_out_intent(),),
            _swap_pre_state(),
            _proof_carrying_context(),
        ),
        _ParityFixtureV1(
            "protocol_fee_exact_in",
            _protocol_fee_settlement(),
            (_swap_intent(),),
            _swap_pre_state(),
            _protocol_fee_context(),
        ),
        _ParityFixtureV1(
            "protocol_fee_exact_out",
            _protocol_fee_exact_out_settlement(),
            (_exact_out_intent(),),
            _swap_pre_state(),
            _protocol_fee_context(),
        ),
        _ParityFixtureV1(
            "distinct_recipient",
            _recipient_swap_settlement(),
            (_recipient_swap_intent(),),
            _swap_pre_state(),
            base_context,
        ),
    ]
    for kind in (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT):
        settlement, intent, pre_state, _replay = _route_fixture(kind, route_pools())
        fixtures.append(
            _ParityFixtureV1(
                "route_exact_in" if kind is IntentKind.ROUTE_EXACT_IN else "route_exact_out",
                settlement,
                (intent,),
                pre_state,
                _route_context(),
            )
        )
    for symmetric in (True, False):
        settlement, intents = _cow_settlement(symmetric=symmetric)
        fixtures.append(
            _ParityFixtureV1(
                "cow_symmetric_accept" if symmetric else "cow_asymmetric_reject",
                settlement,
                intents,
                _cow_pre_state(),
                _cow_context(enabled=True),
            )
        )
    return tuple(fixtures)


def _source_manifest_v1(repo_root: Path) -> dict[str, str]:
    return {
        path.as_posix(): sha256_hex((repo_root / path).read_bytes()) for path in SOURCE_PATHS_V1
    }


def _implementation_source_sha_v1(repo_root: Path) -> str:
    completed = subprocess.run(
        [
            "git",
            "log",
            "-1",
            "--format=%H",
            "--",
            *(path.as_posix() for path in RUNTIME_SOURCE_PATHS_V1),
        ],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    )
    value = completed.stdout.strip()
    if not value:
        fallback = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo_root,
            check=True,
            capture_output=True,
            text=True,
        )
        value = fallback.stdout.strip()
    if len(value) != 40:
        raise ValueError("implementation source SHA is unavailable")
    return value


def artifact_source_v1(repo_root: Path) -> dict[str, object]:
    manifest = _source_manifest_v1(repo_root)
    rows = [_evaluate_fixture_v1(fixture) for fixture in _fixtures_v1()]
    refine_count = sum(row["status"] == "REFINE" for row in rows)
    mismatch_count = len(rows) - refine_count
    payload: dict[str, object] = {
        "algorithm_versions": {
            "exact": EXACT_ALGORITHM_V1,
            "legacy": LEGACY_ALGORITHM_V1,
        },
        "implementation_source_sha": _implementation_source_sha_v1(repo_root),
        "mount_authorized": False,
        "result_counts": {"mismatch": mismatch_count, "refine": refine_count},
        "reviewed_start_sha": REVIEWED_START_SHA_V1,
        "row_count": len(rows),
        "rows": rows,
        "schema": ARTIFACT_SCHEMA_V1,
        "source_manifest": manifest,
        "source_manifest_sha256": sha256_hex(canonical_json_bytes(manifest)),
        "verdict": "REFINES" if mismatch_count == 0 else "BLOCKED_MISMATCH",
    }
    payload["artifact_sha256"] = sha256_hex(canonical_json_bytes(payload))
    return payload


def artifact_bytes_v1(repo_root: Path) -> bytes:
    return canonical_json_bytes(artifact_source_v1(repo_root)) + b"\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes_v1(_REPO_ROOT)
    artifact_path = _REPO_ROOT / ARTIFACT_PATH_V1
    if args.check:
        if not artifact_path.exists() or artifact_path.read_bytes() != expected:
            print("P4B4 direct parity artifact is stale", file=sys.stderr)
            return 1
        print("P4B4 direct parity artifact is current")
        return 0
    artifact_path.write_bytes(expected)
    artifact = artifact_source_v1(_REPO_ROOT)
    row_count = artifact["row_count"]
    verdict = artifact["verdict"]
    print(f"wrote {artifact_path}: {row_count} rows, {verdict}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
