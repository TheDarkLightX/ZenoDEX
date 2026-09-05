"""Custody-complete successor execution over unchanged V1 wire values.

This pure entry is not mounted in release admission or any guest. A future
release must bind these execution semantics and its measured image explicitly.
Legacy leaf/wrapper behavior and historical receipts retain their old subject.
"""

from __future__ import annotations

from dataclasses import replace

from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleResultV1,
    _receipt_root,
    _snapshot_asset_transfer_lane_module_accepted_v1,
    _snapshot_asset_transfer_lane_module_input_v1,
    _transition_owned_asset_transfer_lane_module_v1,
)
from .asset_transfer_types_v1 import AssetTransferRejectedV1


def _complete_owned_result_v1(
    legacy: AssetTransferLaneModuleAcceptedV1,
) -> AssetTransferLaneModuleAcceptedV1:
    port = legacy.private_port
    effects = replace(
        legacy.effects,
        asset_conservation=tuple(
            replace(
                row,
                owned_and_custodied_pre_atoms=port.pre_state.owned_and_custodied_atoms(row.asset),
                owned_and_custodied_post_atoms=port.post_state.owned_and_custodied_atoms(row.asset),
            )
            for row in legacy.effects.asset_conservation
        ),
    )
    port = replace(port, module_effect_plan_root=effects.effect_plan_root)
    journal = replace(
        legacy.module_journal,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=port.port_root,
        receipt_root=_receipt_root(legacy.statement_root, legacy.module_journal, port, effects),
    )
    return AssetTransferLaneModuleAcceptedV1(
        legacy.statement_root, legacy.post_state, effects, journal, port
    )


def transition_asset_transfer_lane_module_custody_v1(
    module_input: AssetTransferLaneModuleInputV1,
) -> AssetTransferLaneModuleResultV1:
    """Derive complete physical totals; return unchanged leaf rejection or data.

    Exact input snapshots validate balances plus custody against bounded supply.
    The legacy wrapper constructs identical pre/post custody; completing each
    projection separately preserves that frame without assuming caller totals.
    No cryptographic witness or publication capability is constructed here.
    """
    owned = _snapshot_asset_transfer_lane_module_input_v1(module_input)
    legacy = _transition_owned_asset_transfer_lane_module_v1(owned)
    if isinstance(legacy, AssetTransferRejectedV1):
        return legacy
    return _complete_owned_result_v1(legacy)


def recompute_asset_transfer_lane_module_custody_v1(
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> AssetTransferLaneModuleAcceptedV1:
    """Return the freshly recomputed exact value; this conveys no authority."""
    expected = transition_asset_transfer_lane_module_custody_v1(module_input)
    if type(expected) is not AssetTransferLaneModuleAcceptedV1:
        raise ValueError("custody-complete supplied acceptance recomputes to rejection")
    supplied = _snapshot_asset_transfer_lane_module_accepted_v1(accepted)
    if supplied != expected:
        raise ValueError("custody-complete supplied acceptance differs from recomputation")
    return expected


__all__ = [
    "transition_asset_transfer_lane_module_custody_v1",
    "recompute_asset_transfer_lane_module_custody_v1",
]
