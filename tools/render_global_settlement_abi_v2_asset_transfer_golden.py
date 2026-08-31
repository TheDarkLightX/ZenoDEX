#!/usr/bin/env python3
"""Render or check the isolated ABI V2 asset-transfer parity vectors.

The fixture is source-generated research evidence for Python/Rust parity.  It
does not authenticate the policy snapshot, mount a route, verify a proof, or
grant settlement authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Final

from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    AssetClassV2,
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferStateV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)

FIXTURE_SCHEMA_V2: Final = "zenodex/global-settlement-abi-v2-asset-transfer-golden/v1"
FIXTURE_PATH_V2: Final = Path("tests/data/global_settlement_abi_v2_asset_transfer_golden.json")
FROZEN_V1_GOLDEN_SHA256: Final = "9e2b233076a0724635dffb3d7f06f1cb26b7b4ac3c79b3ae4f02420e5877c9e4"
_U64_NEIGHBOR_ATOMS: Final = (1 << 64) + 100


def _root(value: int) -> str:
    if not 0 < value < 1 << 256:
        raise ValueError("fixture root ordinal is out of range")
    return f"0x{value:064x}"


def _canonical(value: object) -> object:
    return json.loads(canonical_global_bytes_v2(value))


def _vector(value: object, *, expected_root: str) -> dict[str, object]:
    canonical_bytes = canonical_global_bytes_v2(value)
    return {
        "canonical": json.loads(canonical_bytes),
        "canonical_bytes_sha256": hashlib.sha256(canonical_bytes).hexdigest(),
        "expected_root": expected_root,
    }


def build_vectors_v2() -> dict[str, object]:
    command = AssetTransferCommandV2(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
        asset="USD",
        sender="alice",
        recipient="bob",
        amount_atoms=25,
        max_fee_atoms=2,
        asset_origin_root=_root(6),
    )
    occurrence = EconomicCommandOccurrenceV2(
        chain_id="zeno-v2-golden-chain",
        deployment_root=_root(1),
        height=42,
        tx_index=2,
        op_index=1,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root(2),
        subject_id=command.sender,
        grant_root=_root(4),
        nonce=9,
        profile_root=_root(5),
        pre_state_root=_root(7),
        consumed_object_ids=(),
    )
    context = AssetTransferContextV2(
        writer_epoch=7,
        module_release_id=_root(3),
        global_pre_state_root=occurrence.pre_state_root,
        occurrence=occurrence,
    )
    pre_state = AssetTransferStateV2(
        module_release_id=context.module_release_id,
        policies=(
            AssetTransferPolicyV2(
                asset="USD",
                fee_owner="treasury",
                transfer_fee_atoms=2,
                enabled=True,
                asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
                asset_origin_root=command.asset_origin_root,
                atom_decimals=ASSET_ATOM_DECIMALS_V2,
            ),
        ),
        balances=(
            EconomicAmountV2(
                "alice",
                "USD",
                ACCOUNT_CUSTODY_DOMAIN_V2,
                _U64_NEIGHBOR_ATOMS,
            ),
        ),
        supplies=(AssetSupplyV2("USD", _U64_NEIGHBOR_ATOMS),),
    )
    result = transition_asset_transfer_v2(context, pre_state, command)
    if not isinstance(result, AssetTransferAcceptedV2):
        raise RuntimeError("V2 golden transfer unexpectedly rejected")
    context_root = hash_global_v2("asset-transfer-context-vector-v2", context)
    return {
        "fixture_schema": FIXTURE_SCHEMA_V2,
        "authority": "NONE",
        "frozen_v1_golden_sha256": FROZEN_V1_GOLDEN_SHA256,
        "vectors": {
            "command": _vector(command, expected_root=command.command_body_hash),
            "occurrence": _vector(
                occurrence,
                expected_root=occurrence.occurrence_id,
            ),
            "context": _vector(context, expected_root=context_root),
            "pre_state": _vector(pre_state, expected_root=pre_state.state_root),
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
        "receipt_root": result.receipt_root,
    }


def render_vectors_v2() -> str:
    return json.dumps(build_vectors_v2(), indent=2, sort_keys=True) + "\n"


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    output = parser.add_mutually_exclusive_group()
    output.add_argument(
        "--check",
        type=Path,
        metavar="PATH",
        help="fail unless PATH exactly matches the rendered fixture",
    )
    output.add_argument(
        "--write",
        type=Path,
        metavar="PATH",
        help="write the rendered fixture to PATH",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    rendered = render_vectors_v2()
    if args.write is not None:
        args.write.write_text(rendered, encoding="utf-8")
        print(f"global ABI V2 asset-transfer fixture written: {args.write}")
        return 0
    if args.check is None:
        sys.stdout.write(rendered)
        return 0
    try:
        observed = args.check.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"global ABI V2 asset-transfer fixture check failed: {exc}", file=sys.stderr)
        return 1
    if observed != rendered:
        print(f"global ABI V2 asset-transfer fixture drift: {args.check}", file=sys.stderr)
        return 1
    print(f"global ABI V2 asset-transfer fixture match: {args.check}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
