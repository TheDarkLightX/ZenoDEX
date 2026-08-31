#!/usr/bin/env python3
"""Render or check V2 asset-lane coordinator Python/Rust golden vectors.

The packet fixes aggregate state, one transfer, one managed issue, and exact
coordinator/leaf rejection behavior. It grants no RISC0, runtime, settlement,
release, migration, UI, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.asset_lane_coordinator_v2 import (  # noqa: E402
    AssetLaneAcceptedV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    transition_asset_lane_v2,
)
from src.core.asset_lane_coordinator_values_v2 import (  # noqa: E402
    AssetLaneCommandV2,
)
from src.core.asset_lane_state_v2 import (  # noqa: E402
    MAX_ASSET_LANE_ASSETS_V2,
    MAX_ASSET_LANE_BALANCE_ROWS_V2,
    MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2,
    AssetLaneContextV2,
    AssetLaneStateV2,
)
from src.core.asset_origin_registry_types_v2 import (  # noqa: E402
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistryStateV2,
)
from src.core.asset_origin_registry_v2 import (  # noqa: E402
    asset_transfer_policy_root_v2,
    managed_asset_policy_root_v2,
)
from src.core.asset_transfer_types_v2 import (  # noqa: E402
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    AssetClassV2,
    AssetTransferCommandV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2  # noqa: E402
from src.core.global_settlement_types_v2 import (  # noqa: E402
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from src.core.managed_asset_lifecycle_types_v2 import (  # noqa: E402
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2,
)

FIXTURE_SCHEMA_V2: Final = (
    "zenodex/global-settlement-abi-v2-asset-lane-coordinator-golden/v1"
)
FIXTURE_PATH_V2: Final = Path(
    REPO_ROOT / "tests/data/global_settlement_abi_v2_asset_lane_coordinator_golden.json"
)
PLAN_PATH_V2: Final = Path("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json")
EXPECTED_PLAN_SHA256_V2: Final = (
    "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f"
)
SOURCE_PATHS_V2: Final = (
    Path("src/core/asset_lane_state_v2.py"),
    Path("src/core/asset_lane_coordinator_values_v2.py"),
    Path("src/core/asset_lane_coordinator_v2.py"),
    Path("src/core/asset_origin_registry_v2.py"),
    Path("src/core/asset_transfer_module_v2.py"),
    Path("src/core/managed_asset_lifecycle_module_v2.py"),
)


def _root(value: int) -> str:
    if not 0 < value < 1 << 256:
        raise ValueError("fixture root ordinal is out of range")
    return f"0x{value:064x}"


def _vector(value: object, *, expected_root: str) -> dict[str, object]:
    canonical_bytes = canonical_global_bytes_v2(value)
    return {
        "canonical": json.loads(canonical_bytes),
        "canonical_bytes_sha256": hashlib.sha256(canonical_bytes).hexdigest(),
        "expected_root": expected_root,
    }


def _policies() -> tuple[AssetTransferPolicyV2, ManagedAssetLifecyclePolicyV2]:
    transfer = AssetTransferPolicyV2(
        asset="USD",
        fee_owner="treasury",
        transfer_fee_atoms=2,
        enabled=True,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(6),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )
    managed = ManagedAssetLifecyclePolicyV2(
        asset="USD",
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(6),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
        issue_authority_subject="issuer",
        issue_authorization_root=_root(5),
        burn_authorization_root=_root(4),
        enabled=True,
    )
    return transfer, managed


def _registry(
    transfer: AssetTransferPolicyV2,
    managed: ManagedAssetLifecyclePolicyV2,
    *,
    transfer_policy_root_override: str | None = None,
) -> AssetOriginRegistryStateV2:
    record = AssetOriginRecordV2(
        asset="USD",
        origin_kind=AssetOriginKindV2.TAU_ORIGINATED,
        origin_root=_root(6),
        transfer_policy_root=(
            asset_transfer_policy_root_v2(transfer)
            if transfer_policy_root_override is None
            else transfer_policy_root_override
        ),
        issue_policy_root=managed_asset_policy_root_v2(managed),
        decimals=ASSET_ATOM_DECIMALS_V2,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    )
    return AssetOriginRegistryStateV2(
        module_release_id=_root(3),
        policy=AssetOriginRegistrationPolicyV2(
            authority_subject="governance",
            authority_grant_root=_root(10),
            allow_native=True,
            allow_tau_originated=True,
        ),
        assets=(record,),
    )


def _state(*, transfer_policy_root_override: str | None = None) -> AssetLaneStateV2:
    transfer, managed = _policies()
    return AssetLaneStateV2(
        module_release_id=_root(3),
        origin_registry=_registry(
            transfer,
            managed,
            transfer_policy_root_override=transfer_policy_root_override,
        ),
        transfer_policies=(transfer,),
        managed_policies=(managed,),
        balances=(
            EconomicAmountV2("alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 1_000),
        ),
        supplies=(AssetSupplyV2("USD", 1_000),),
    )


def _transfer_command() -> AssetTransferCommandV2:
    return AssetTransferCommandV2(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
        asset="USD",
        sender="alice",
        recipient="bob",
        amount_atoms=100,
        max_fee_atoms=2,
        asset_origin_root=_root(6),
    )


def _managed_command() -> ManagedAssetLifecycleCommandV2:
    return ManagedAssetLifecycleCommandV2(
        command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
        asset="USD",
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(6),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
        authorization_root=_root(5),
        account_owner="alice",
        amount_atoms=50,
    )


def _context(
    command: AssetLaneCommandV2,
    *,
    subject_id: str,
    grant_root: str,
    nonce: int,
) -> AssetLaneContextV2:
    occurrence = EconomicCommandOccurrenceV2(
        chain_id="zeno-v2-asset-lane-golden-chain",
        deployment_root=_root(1),
        height=42,
        tx_index=2,
        op_index=nonce,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root(2),
        subject_id=subject_id,
        grant_root=grant_root,
        nonce=nonce,
        profile_root=_root(8),
        pre_state_root=_root(7),
        consumed_object_ids=(),
    )
    return AssetLaneContextV2(
        writer_epoch=7,
        module_release_id=_root(3),
        global_pre_state_root=occurrence.pre_state_root,
        occurrence=occurrence,
    )


def _context_vector(context: AssetLaneContextV2) -> dict[str, object]:
    canonical_context = context.transfer_context()
    return _vector(
        canonical_context,
        expected_root=hash_global_v2(
            "asset-lane-context-vector-v2",
            canonical_context,
        ),
    )


def _accepted_case(
    state: AssetLaneStateV2,
    context: AssetLaneContextV2,
    command: AssetLaneCommandV2,
) -> dict[str, object]:
    result = transition_asset_lane_v2(context, state, command)
    if not isinstance(result, AssetLaneAcceptedV2):
        raise RuntimeError("V2 golden asset-lane command unexpectedly rejected")
    return {
        "route": result.route.value,
        "command_type": (
            "transfer"
            if isinstance(command, AssetTransferCommandV2)
            else "managed_lifecycle"
        ),
        "source_leaf_journal_root": result.source_leaf_journal_root,
        "receipt_root": result.receipt_root,
        "vectors": {
            "context": _context_vector(context),
            "pre_state": _vector(state, expected_root=state.state_root),
            "command": _vector(command, expected_root=command.command_body_hash),
            "post_state": _vector(
                result.post_state,
                expected_root=result.post_state.state_root,
            ),
            "effect_plan": _vector(
                result.effects,
                expected_root=result.effects.effect_plan_root,
            ),
            "module_journal": _vector(
                result.module_journal,
                expected_root=result.module_journal.journal_root,
            ),
        },
    }


def _rejection_case(
    state: AssetLaneStateV2,
    context: AssetLaneContextV2,
    command: AssetLaneCommandV2,
) -> dict[str, object]:
    result = transition_asset_lane_v2(context, state, command)
    if not isinstance(result, AssetLaneRejectedV2):
        raise RuntimeError("V2 golden asset-lane rejection unexpectedly accepted")
    if result.pre_state_root != result.post_state_root or not result.effects.is_empty:
        raise RuntimeError("V2 golden asset-lane rejection is not an exact no-op")
    return {
        "expected_route": result.route.value,
        "expected_code": result.code.value,
        "command_type": (
            "transfer"
            if isinstance(command, AssetTransferCommandV2)
            else "managed_lifecycle"
        ),
        "vectors": {
            "context": _context_vector(context),
            "pre_state": _vector(state, expected_root=state.state_root),
            "command": _vector(command, expected_root=command.command_body_hash),
        },
    }


def _accepted_cases() -> dict[str, object]:
    state = _state()
    transfer = _transfer_command()
    managed = _managed_command()
    return {
        "managed_issue": _accepted_case(
            state,
            _context(managed, subject_id="issuer", grant_root=_root(5), nonce=2),
            managed,
        ),
        "transfer": _accepted_case(
            state,
            _context(transfer, subject_id="alice", grant_root=_root(9), nonce=1),
            transfer,
        ),
    }


def _rejection_cases() -> dict[str, object]:
    transfer = _transfer_command()
    managed = _managed_command()
    registry_first_context = _context(
        transfer,
        subject_id="mallory",
        grant_root=_root(9),
        nonce=3,
    )
    return {
        "01_registry_binding_precedes_transfer_leaf": _rejection_case(
            _state(transfer_policy_root_override=_root(99)),
            registry_first_context,
            transfer,
        ),
        "02_transfer_leaf_unauthorized": _rejection_case(
            _state(),
            registry_first_context,
            transfer,
        ),
        "03_managed_leaf_authorization_root": _rejection_case(
            _state(),
            _context(managed, subject_id="issuer", grant_root=_root(11), nonce=4),
            managed,
        ),
    }


def build_vectors_v2() -> dict[str, object]:
    plan_sha256 = hashlib.sha256((REPO_ROOT / PLAN_PATH_V2).read_bytes()).hexdigest()
    if plan_sha256 != EXPECTED_PLAN_SHA256_V2:
        raise RuntimeError("V2 whole-program plan hash differs from the pinned coordinator plan")
    return {
        "fixture_schema": FIXTURE_SCHEMA_V2,
        "authority": "NONE",
        "profile_authentication": "SHADOW",
        "plan_sha256": plan_sha256,
        "limits": {
            "max_assets": MAX_ASSET_LANE_ASSETS_V2,
            "max_balance_rows": MAX_ASSET_LANE_BALANCE_ROWS_V2,
            "max_state_canonical_bytes": MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2,
        },
        "python_source_sha256": {
            str(path): hashlib.sha256((REPO_ROOT / path).read_bytes()).hexdigest()
            for path in SOURCE_PATHS_V2
        },
        "coordinator_reject_codes": [
            code.value for code in AssetLaneCoordinatorRejectCodeV2
        ],
        "transfer_reject_codes": [code.value for code in AssetTransferRejectCodeV2],
        "managed_reject_codes": [
            code.value for code in ManagedAssetLifecycleRejectCodeV2
        ],
        "accepted": _accepted_cases(),
        "rejections": _rejection_cases(),
        "nonclaims": [
            "no RISC0 circuit or receipt",
            "no runtime mount, migration, or UI",
            "no settlement, release, or production authority",
        ],
    }


def render_vectors_v2() -> str:
    return json.dumps(build_vectors_v2(), indent=2, sort_keys=True) + "\n"


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--check", type=Path, metavar="PATH")
    output.add_argument("--write", type=Path, metavar="PATH")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    rendered = render_vectors_v2()
    if args.write is not None:
        args.write.write_text(rendered, encoding="utf-8")
        print(f"global ABI V2 asset-lane coordinator fixture written: {args.write}")
        return 0
    if args.check is None:
        sys.stdout.write(rendered)
        return 0
    try:
        observed = args.check.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"global ABI V2 asset-lane coordinator fixture check failed: {exc}", file=sys.stderr)
        return 1
    if observed != rendered:
        print(f"global ABI V2 asset-lane coordinator fixture drift: {args.check}", file=sys.stderr)
        return 1
    print(f"global ABI V2 asset-lane coordinator fixture match: {args.check}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
