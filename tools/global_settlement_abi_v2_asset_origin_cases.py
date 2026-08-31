"""Adjacent-precedence cases for the Asset Origin Registry V2 golden packet."""

from __future__ import annotations

import hashlib
import json
from dataclasses import replace

from src.core.asset_origin_registry_types_v2 import (
    ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistrationCommandV2,
    AssetOriginRegistrationContextV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistrationRejectCodeV2,
    AssetOriginRegistrationRejectedV2,
    AssetOriginRegistryStateV2,
)
from src.core.asset_origin_registry_v2 import transition_asset_origin_registration_v2
from src.core.asset_transfer_types_v2 import (
    ASSET_ATOM_DECIMALS_V2,
    AssetClassV2,
)
from src.core.global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    canonical_global_bytes_v2,
    hash_global_v2,
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


def _record_for(command: AssetOriginRegistrationCommandV2) -> AssetOriginRecordV2:
    return AssetOriginRecordV2(
        asset=command.asset,
        origin_kind=command.origin_kind,
        origin_root=command.origin_root,
        transfer_policy_root=command.transfer_policy_root,
        issue_policy_root=command.issue_policy_root,
        decimals=command.decimals,
        asset_class=command.asset_class,
    )


def _context_for_command(
    context: AssetOriginRegistrationContextV2,
    command: AssetOriginRegistrationCommandV2,
    **occurrence_changes: object,
) -> AssetOriginRegistrationContextV2:
    occurrence = context.occurrence
    if occurrence is None:
        raise RuntimeError("fixture base occurrence is absent")
    return replace(
        context,
        occurrence=replace(
            occurrence,
            command_kind=command.command_kind,
            command_body_hash=command.command_body_hash,
            **occurrence_changes,
        ),
    )


def _state_with(
    state: AssetOriginRegistryStateV2,
    *,
    policy: AssetOriginRegistrationPolicyV2 | None = None,
    assets: tuple[AssetOriginRecordV2, ...] | None = None,
) -> AssetOriginRegistryStateV2:
    return AssetOriginRegistryStateV2(
        module_release_id=state.module_release_id,
        policy=state.policy if policy is None else policy,
        assets=(
            state.assets if assets is None else tuple(sorted(assets, key=lambda row: row.asset))
        ),
    )


def _native_command() -> AssetOriginRegistrationCommandV2:
    return AssetOriginRegistrationCommandV2(
        command_kind=ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
        asset="TAU",
        origin_kind=AssetOriginKindV2.NATIVE,
        origin_root=_root(40),
        transfer_policy_root=_root(41),
        issue_policy_root=ZERO_ROOT_V2,
        decimals=ASSET_ATOM_DECIMALS_V2,
        asset_class=AssetClassV2.TAU_NATIVE_COIN,
    )


def _reject_vector(
    context: AssetOriginRegistrationContextV2,
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
    expected: AssetOriginRegistrationRejectCodeV2,
) -> dict[str, object]:
    result = transition_asset_origin_registration_v2(context, state, command)
    if not isinstance(result, AssetOriginRegistrationRejectedV2) or result.code is not expected:
        raise RuntimeError(f"asset-origin rejection vector did not produce {expected.value}")
    if result.pre_state_root != result.post_state_root or not result.effects.is_empty:
        raise RuntimeError("asset-origin rejection vector is not an exact no-op")
    return {
        "context": _vector(
            context,
            expected_root=hash_global_v2("asset-origin-registration-context-vector-v2", context),
        ),
        "pre_state": _vector(state, expected_root=state.state_root),
        "command": _vector(command, expected_root=command.command_body_hash),
        "expected_code": expected.value,
    }


_RejectCaseV2 = tuple[
    str,
    AssetOriginRegistrationContextV2,
    AssetOriginRegistryStateV2,
    AssetOriginRegistrationCommandV2,
    AssetOriginRegistrationRejectCodeV2,
]


def _occurrence_binding_cases(
    context: AssetOriginRegistrationContextV2,
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
) -> tuple[_RejectCaseV2, ...]:
    unknown = replace(command, command_kind="unknown_asset_origin_command")
    return (
        (
            "01_missing_occurrence",
            replace(context, occurrence=None, module_release_id=_root(30)),
            state,
            command,
            AssetOriginRegistrationRejectCodeV2.MISSING_OCCURRENCE,
        ),
        (
            "02_occurrence_binding_mismatch",
            replace(
                context,
                global_pre_state_root=_root(31),
                module_release_id=_root(30),
            ),
            state,
            command,
            AssetOriginRegistrationRejectCodeV2.OCCURRENCE_BINDING_MISMATCH,
        ),
        (
            "03_release_mismatch",
            replace(context, module_release_id=_root(30)),
            state,
            unknown,
            AssetOriginRegistrationRejectCodeV2.RELEASE_MISMATCH,
        ),
    )


def _command_binding_cases(
    context: AssetOriginRegistrationContextV2,
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
) -> tuple[_RejectCaseV2, ...]:
    occurrence = context.occurrence
    if occurrence is None:
        raise RuntimeError("fixture base occurrence is absent")
    unknown = replace(command, command_kind="unknown_asset_origin_command")
    return (
        (
            "04_unknown_command",
            context,
            state,
            unknown,
            AssetOriginRegistrationRejectCodeV2.UNKNOWN_COMMAND,
        ),
        (
            "05_occurrence_command_mismatch",
            replace(
                context,
                occurrence=replace(
                    occurrence,
                    command_body_hash=_root(32),
                    subject_id="mallory",
                ),
            ),
            state,
            command,
            AssetOriginRegistrationRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH,
        ),
    )


def _authority_cases(
    context: AssetOriginRegistrationContextV2,
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
) -> tuple[_RejectCaseV2, ...]:
    bad_decimals = replace(command, decimals=7)
    disabled_tau_state = _state_with(
        state,
        policy=replace(state.policy, allow_tau_originated=False),
    )
    return (
        (
            "06_unauthorized_subject",
            _context_for_command(
                context,
                command,
                subject_id="mallory",
                grant_root=_root(33),
            ),
            state,
            command,
            AssetOriginRegistrationRejectCodeV2.UNAUTHORIZED_SUBJECT,
        ),
        (
            "07_grant_mismatch",
            _context_for_command(context, bad_decimals, grant_root=_root(33)),
            state,
            bad_decimals,
            AssetOriginRegistrationRejectCodeV2.GRANT_MISMATCH,
        ),
        (
            "08_decimal_scale_mismatch",
            _context_for_command(context, bad_decimals),
            disabled_tau_state,
            bad_decimals,
            AssetOriginRegistrationRejectCodeV2.DECIMAL_SCALE_MISMATCH,
        ),
    )


def _registry_cases(
    context: AssetOriginRegistrationContextV2,
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
) -> tuple[_RejectCaseV2, ...]:
    native = _native_command()
    disabled_native_state = _state_with(
        state,
        policy=replace(state.policy, allow_native=False),
    )
    native_state = _state_with(state, assets=(*state.assets, _record_for(native)))
    duplicate_asset_state = _state_with(state, assets=(*state.assets, _record_for(command)))
    duplicate_origin_state = _state_with(
        state,
        assets=(replace(state.assets[0], origin_root=command.origin_root),),
    )
    return (
        (
            "09_disabled_origin_kind",
            _context_for_command(context, native),
            disabled_native_state,
            native,
            AssetOriginRegistrationRejectCodeV2.DISABLED_ORIGIN_KIND,
        ),
        (
            "10_native_accounting_unimplemented",
            _context_for_command(context, native),
            native_state,
            native,
            AssetOriginRegistrationRejectCodeV2.NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
        ),
        (
            "11_duplicate_asset",
            context,
            duplicate_asset_state,
            command,
            AssetOriginRegistrationRejectCodeV2.DUPLICATE_ASSET,
        ),
        (
            "12_duplicate_origin",
            context,
            duplicate_origin_state,
            command,
            AssetOriginRegistrationRejectCodeV2.DUPLICATE_ORIGIN,
        ),
    )


def build_rejection_vectors_v2(
    context: AssetOriginRegistrationContextV2,
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
) -> dict[str, object]:
    """Build one case per guard, with the following guard also defective."""

    cases = (
        *_occurrence_binding_cases(context, state, command),
        *_command_binding_cases(context, state, command),
        *_authority_cases(context, state, command),
        *_registry_cases(context, state, command),
    )
    return {
        name: _reject_vector(selected_context, selected_state, selected_command, expected)
        for name, selected_context, selected_state, selected_command, expected in cases
    }


__all__ = ["build_rejection_vectors_v2"]
