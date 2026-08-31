#!/usr/bin/env python3
"""Render or check the ABI V2 asset-origin Python/Rust parity vectors.

The generated packet binds exact canonical values, roots, policy membership,
and adjacent rejection precedence. It grants no RISC0, runtime, migration, UI,
release, settlement, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.asset_origin_registry_types_v2 import (  # noqa: E402
    ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistrationAcceptedV2,
    AssetOriginRegistrationCommandV2,
    AssetOriginRegistrationContextV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistrationRejectCodeV2,
    AssetOriginRegistryStateV2,
)
from src.core.asset_origin_registry_v2 import (  # noqa: E402
    asset_transfer_policy_root_v2,
    managed_asset_policy_root_v2,
    transition_asset_origin_registration_v2,
    validate_asset_transfer_policy_origin_v2,
    validate_managed_asset_policy_origin_v2,
)
from src.core.asset_transfer_types_v2 import (  # noqa: E402
    ASSET_ATOM_DECIMALS_V2,
    AssetClassV2,
    AssetTransferPolicyV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2  # noqa: E402
from src.core.global_settlement_types_v2 import (  # noqa: E402
    ZERO_ROOT_V2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from src.core.managed_asset_lifecycle_types_v2 import (  # noqa: E402
    ManagedAssetLifecyclePolicyV2,
)
from tools.global_settlement_abi_v2_asset_origin_cases import (  # noqa: E402
    build_rejection_vectors_v2,
)

FIXTURE_SCHEMA_V2: Final = "zenodex/global-settlement-abi-v2-asset-origin-golden/v1"
FIXTURE_PATH_V2: Final = Path(
    REPO_ROOT / "tests/data/global_settlement_abi_v2_asset_origin_golden.json"
)
SOURCE_PATHS_V2: Final = (
    Path("src/core/asset_origin_registry_ownership_v2.py"),
    Path("src/core/asset_origin_registry_types_v2.py"),
    Path("src/core/asset_origin_registry_v2.py"),
    Path("src/core/asset_origin_registry_codec_v2.py"),
    Path("tools/global_settlement_abi_v2_asset_origin_cases.py"),
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
    transfer_policy = AssetTransferPolicyV2(
        asset="USD",
        fee_owner="treasury",
        transfer_fee_atoms=2,
        enabled=True,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(6),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )
    managed_policy = ManagedAssetLifecyclePolicyV2(
        asset="USD",
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(6),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
        issue_authority_subject="issuer",
        issue_authorization_root=_root(5),
        burn_authorization_root=_root(4),
        enabled=True,
    )
    return transfer_policy, managed_policy


def _command(
    transfer_policy: AssetTransferPolicyV2,
    managed_policy: ManagedAssetLifecyclePolicyV2,
) -> AssetOriginRegistrationCommandV2:
    return AssetOriginRegistrationCommandV2(
        command_kind=ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
        asset="USD",
        origin_kind=AssetOriginKindV2.TAU_ORIGINATED,
        origin_root=_root(6),
        transfer_policy_root=asset_transfer_policy_root_v2(transfer_policy),
        issue_policy_root=managed_asset_policy_root_v2(managed_policy),
        decimals=ASSET_ATOM_DECIMALS_V2,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    )


def _state() -> AssetOriginRegistryStateV2:
    return AssetOriginRegistryStateV2(
        module_release_id=_root(3),
        policy=AssetOriginRegistrationPolicyV2(
            authority_subject="governance",
            authority_grant_root=_root(4),
            allow_native=True,
            allow_tau_originated=True,
        ),
        assets=(
            AssetOriginRecordV2(
                asset="EUR",
                origin_kind=AssetOriginKindV2.TAU_ORIGINATED,
                origin_root=_root(20),
                transfer_policy_root=_root(21),
                issue_policy_root=ZERO_ROOT_V2,
                decimals=ASSET_ATOM_DECIMALS_V2,
                asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
            ),
        ),
    )


def _context(
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
) -> AssetOriginRegistrationContextV2:
    occurrence = EconomicCommandOccurrenceV2(
        chain_id="zeno-v2-asset-origin-golden-chain",
        deployment_root=_root(1),
        height=42,
        tx_index=2,
        op_index=1,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root(2),
        subject_id="governance",
        grant_root=_root(4),
        nonce=9,
        profile_root=_root(8),
        pre_state_root=_root(7),
        consumed_object_ids=(),
    )
    return AssetOriginRegistrationContextV2(
        writer_epoch=7,
        module_release_id=state.module_release_id,
        global_pre_state_root=occurrence.pre_state_root,
        occurrence=occurrence,
    )


@dataclass(frozen=True, slots=True)
class _GoldenSubjectV2:
    transfer_policy: AssetTransferPolicyV2
    managed_policy: ManagedAssetLifecyclePolicyV2
    command: AssetOriginRegistrationCommandV2
    pre_state: AssetOriginRegistryStateV2
    context: AssetOriginRegistrationContextV2
    occurrence: EconomicCommandOccurrenceV2
    result: AssetOriginRegistrationAcceptedV2
    record: AssetOriginRecordV2


def _build_subject_v2() -> _GoldenSubjectV2:
    transfer_policy, managed_policy = _policies()
    command = _command(transfer_policy, managed_policy)
    pre_state = _state()
    context = _context(pre_state, command)
    result = transition_asset_origin_registration_v2(context, pre_state, command)
    if not isinstance(result, AssetOriginRegistrationAcceptedV2):
        raise RuntimeError("V2 golden asset-origin registration unexpectedly rejected")
    record = result.post_state.record_for(command.asset)
    if record is None:
        raise RuntimeError("V2 golden asset-origin record is absent")
    if validate_asset_transfer_policy_origin_v2(result.post_state, transfer_policy) != record:
        raise RuntimeError("V2 golden transfer policy binding failed")
    if validate_managed_asset_policy_origin_v2(result.post_state, managed_policy) != record:
        raise RuntimeError("V2 golden managed policy binding failed")
    occurrence = context.occurrence
    if occurrence is None:
        raise RuntimeError("V2 golden occurrence is absent")
    return _GoldenSubjectV2(
        transfer_policy,
        managed_policy,
        command,
        pre_state,
        context,
        occurrence,
        result,
        record,
    )


def _accepted_packet_v2(subject: _GoldenSubjectV2) -> dict[str, object]:
    result = subject.result
    return {
        "vectors": {
            "transfer_policy": _vector(
                subject.transfer_policy,
                expected_root=asset_transfer_policy_root_v2(subject.transfer_policy),
            ),
            "managed_policy": _vector(
                subject.managed_policy,
                expected_root=managed_asset_policy_root_v2(subject.managed_policy),
            ),
            "command": _vector(
                subject.command,
                expected_root=subject.command.command_body_hash,
            ),
            "occurrence": _vector(
                subject.occurrence,
                expected_root=subject.occurrence.occurrence_id,
            ),
            "context": _vector(
                subject.context,
                expected_root=hash_global_v2(
                    "asset-origin-registration-context-vector-v2",
                    subject.context,
                ),
            ),
            "pre_state": _vector(
                subject.pre_state,
                expected_root=subject.pre_state.state_root,
            ),
            "post_state": _vector(
                result.post_state,
                expected_root=result.post_state.state_root,
            ),
            "record": _vector(subject.record, expected_root=subject.record.record_root),
            "effect_plan": _vector(
                result.effects,
                expected_root=result.effects.effect_plan_root,
            ),
            "module_journal": _vector(
                result.module_journal,
                expected_root=result.module_journal.journal_root,
            ),
        },
        "receipt_root": result.module_journal.receipt_root,
    }


def build_vectors_v2() -> dict[str, object]:
    subject = _build_subject_v2()
    return {
        "fixture_schema": FIXTURE_SCHEMA_V2,
        "authority": "NONE",
        "profile_authentication": "SHADOW",
        "python_source_sha256": {
            str(path): hashlib.sha256((REPO_ROOT / path).read_bytes()).hexdigest()
            for path in SOURCE_PATHS_V2
        },
        "reject_codes": [code.value for code in AssetOriginRegistrationRejectCodeV2],
        "accepted": _accepted_packet_v2(subject),
        "rejections": build_rejection_vectors_v2(
            subject.context,
            subject.pre_state,
            subject.command,
        ),
        "nonclaims": [
            "no RISC0 circuit or receipt",
            "no runtime mount or migration",
            "no UI, release, settlement, or production authority",
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
        print(f"global ABI V2 asset-origin fixture written: {args.write}")
        return 0
    if args.check is None:
        sys.stdout.write(rendered)
        return 0
    try:
        observed = args.check.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"global ABI V2 asset-origin fixture check failed: {exc}", file=sys.stderr)
        return 1
    if observed != rendered:
        print(f"global ABI V2 asset-origin fixture drift: {args.check}", file=sys.stderr)
        return 1
    print(f"global ABI V2 asset-origin fixture match: {args.check}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
