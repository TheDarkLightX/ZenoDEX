#!/usr/bin/env python3
"""Render or check the ABI V2 managed-asset Python/Rust parity vectors.

The source-generated fixture binds issue and self-burn command, state, effect,
and journal bytes. It grants no registry authentication, runtime route, proof,
settlement, publication, or production authority.
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

from src.core.asset_transfer_types_v2 import (  # noqa: E402
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    AssetClassV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2  # noqa: E402
from src.core.global_settlement_types_v2 import (  # noqa: E402
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import (  # noqa: E402
    transition_managed_asset_lifecycle_v2,
)
from src.core.managed_asset_lifecycle_types_v2 import (  # noqa: E402
    MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleContextV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleStateV2,
)

FIXTURE_SCHEMA_V2: Final = "zenodex/global-settlement-abi-v2-managed-asset-golden/v1"
FIXTURE_PATH_V2: Final = Path(
    REPO_ROOT / "tests/data/global_settlement_abi_v2_managed_asset_golden.json"
)
UNREACHABLE_REJECT_CODES_V2: Final = (
    ManagedAssetLifecycleRejectCodeV2.ASSET_DECIMALS_MISMATCH,
    ManagedAssetLifecycleRejectCodeV2.BALANCE_OVERFLOW,
)
SOURCE_PATHS_V2: Final = (
    Path("src/core/managed_asset_lifecycle_state_v2.py"),
    Path("src/core/managed_asset_lifecycle_result_v2.py"),
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


def _build_case_v2(name: str) -> dict[str, object]:
    is_issue = name == "issue"
    command = ManagedAssetLifecycleCommandV2(
        command_kind=(
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V2
            if is_issue
            else MANAGED_ASSET_BURN_COMMAND_KIND_V2
        ),
        asset="USD",
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(6),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
        authorization_root=_root(5 if is_issue else 4),
        account_owner="alice",
        amount_atoms=7 if is_issue else 4,
    )
    occurrence = EconomicCommandOccurrenceV2(
        chain_id="zeno-v2-managed-golden-chain",
        deployment_root=_root(1),
        height=42,
        tx_index=2,
        op_index=1 if is_issue else 2,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root(2),
        subject_id="issuer" if is_issue else command.account_owner,
        grant_root=command.authorization_root or _root(99),
        nonce=9 if is_issue else 10,
        profile_root=_root(8),
        pre_state_root=_root(7),
        consumed_object_ids=(),
    )
    context = ManagedAssetLifecycleContextV2(
        writer_epoch=7,
        module_release_id=_root(3),
        global_pre_state_root=occurrence.pre_state_root,
        occurrence=occurrence,
    )
    pre_state = ManagedAssetLifecycleStateV2(
        module_release_id=context.module_release_id,
        policies=(
            ManagedAssetLifecyclePolicyV2(
                asset="USD",
                asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
                asset_origin_root=command.asset_origin_root,
                atom_decimals=ASSET_ATOM_DECIMALS_V2,
                issue_authority_subject="issuer",
                issue_authorization_root=_root(5),
                burn_authorization_root=_root(4),
                enabled=True,
            ),
        ),
        balances=(
            EconomicAmountV2(
                "alice",
                "USD",
                ACCOUNT_CUSTODY_DOMAIN_V2,
                10,
            ),
        ),
        supplies=(AssetSupplyV2("USD", 10),),
    )
    result = transition_managed_asset_lifecycle_v2(context, pre_state, command)
    if not isinstance(result, ManagedAssetLifecycleAcceptedV2):
        raise RuntimeError(f"V2 golden managed-asset {name} unexpectedly rejected")
    context_root = hash_global_v2("managed-asset-lifecycle-context-vector-v2", context)
    return {
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


def build_vectors_v2() -> dict[str, object]:
    return {
        "fixture_schema": FIXTURE_SCHEMA_V2,
        "authority": "NONE",
        "profile_authentication": "SHADOW",
        "python_source_sha256": {
            str(path): hashlib.sha256((REPO_ROOT / path).read_bytes()).hexdigest()
            for path in SOURCE_PATHS_V2
        },
        "reject_codes": [code.value for code in ManagedAssetLifecycleRejectCodeV2],
        "constructor_or_invariant_unreachable_reject_codes": [
            code.value for code in UNREACHABLE_REJECT_CODES_V2
        ],
        "cases": {name: _build_case_v2(name) for name in ("burn", "issue")},
        "nonclaims": [
            "no registry or profile authentication",
            "no runtime route or RISC0 receipt",
            "no settlement, publication, or production authority",
        ],
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
        print(f"global ABI V2 managed-asset fixture written: {args.write}")
        return 0
    if args.check is None:
        sys.stdout.write(rendered)
        return 0
    try:
        observed = args.check.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"global ABI V2 managed-asset fixture check failed: {exc}", file=sys.stderr)
        return 1
    if observed != rendered:
        print(f"global ABI V2 managed-asset fixture drift: {args.check}", file=sys.stderr)
        return 1
    print(f"global ABI V2 managed-asset fixture match: {args.check}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
