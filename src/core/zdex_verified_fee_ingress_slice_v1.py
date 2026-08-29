"""Opaque fee-ingress projection derived only after receipt verification.

The slice removes ``fee_charged_atoms`` from caller control for the atomic
buyback path. Its amount is the exact fee-ingress balance in the committed
tokenomics pre-state bound to one command occurrence, profile, authority head,
and verifier deployment. It carries no publication authority and does not make
the surrounding SHADOW route production-ready.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_settlement_types_v1 import _require_atoms_u128, _require_root, hash_global_v1
from .zdex_fee_allocation_types_v1 import ZDEXFeeStateV1

VERIFIED_ZDEX_FEE_INGRESS_SLICE_SCHEMA_V1: Final = (
    "zenodex/verified-zdex-fee-ingress-slice/v1"
)
_VERIFIED_ZDEX_FEE_INGRESS_SLICE_TOKEN_V1 = object()


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXFeeIngressSliceFieldsV1:
    command_occurrence_id: str
    global_pre_state_root: str
    profile_root: str
    fee_state_root: str
    fee_asset_id: str
    fee_ingress_atoms: int
    authority_head_root: str
    verifier_binding_root: str

    def __post_init__(self) -> None:
        for name in (
            "command_occurrence_id",
            "global_pre_state_root",
            "profile_root",
            "fee_state_root",
            "fee_asset_id",
            "authority_head_root",
            "verifier_binding_root",
        ):
            _require_root(getattr(self, name), name=f"verified fee ingress {name}")
        _require_atoms_u128(
            self.fee_ingress_atoms,
            name="verified fee ingress amount",
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": VERIFIED_ZDEX_FEE_INGRESS_SLICE_SCHEMA_V1,
            "command_occurrence_id": self.command_occurrence_id,
            "global_pre_state_root": self.global_pre_state_root,
            "profile_root": self.profile_root,
            "fee_state_root": self.fee_state_root,
            "fee_asset_id": self.fee_asset_id,
            "fee_ingress_atoms": self.fee_ingress_atoms,
            "authority_head_root": self.authority_head_root,
            "verifier_binding_root": self.verifier_binding_root,
        }


class VerifiedZDEXFeeIngressSliceV1:
    """Process-local witness for one receipt-bound committed fee ingress."""

    _fields: _VerifiedZDEXFeeIngressSliceFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _VerifiedZDEXFeeIngressSliceFieldsV1,
    ) -> None:
        if token is not _VERIFIED_ZDEX_FEE_INGRESS_SLICE_TOKEN_V1:
            raise TypeError("VerifiedZDEXFeeIngressSliceV1 is verifier-constructed")
        if type(fields) is not _VerifiedZDEXFeeIngressSliceFieldsV1:
            raise TypeError("verified fee ingress fields must be exact typed data")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedZDEXFeeIngressSliceV1 is immutable")

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def global_pre_state_root(self) -> str:
        return self._fields.global_pre_state_root

    @property
    def profile_root(self) -> str:
        return self._fields.profile_root

    @property
    def fee_state_root(self) -> str:
        return self._fields.fee_state_root

    @property
    def fee_asset_id(self) -> str:
        return self._fields.fee_asset_id

    @property
    def fee_ingress_atoms(self) -> int:
        return self._fields.fee_ingress_atoms

    @property
    def authority_head_root(self) -> str:
        return self._fields.authority_head_root

    @property
    def verifier_binding_root(self) -> str:
        return self._fields.verifier_binding_root

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-zdex-fee-ingress-slice-v1",
            self._fields.to_canonical(),
        )


def _derive_verified_zdex_fee_ingress_slice_v1(
    *,
    command_occurrence_id: str,
    global_pre_state_root: str,
    profile_root: str,
    fee_state: ZDEXFeeStateV1,
    authority_head_root: str,
    verifier_binding_root: str,
) -> VerifiedZDEXFeeIngressSliceV1:
    """Construct the slice inside a verifier-owned post-verification path."""

    if type(fee_state) is not ZDEXFeeStateV1:
        raise TypeError("verified fee ingress state must be exact typed data")
    fee_state.validate()
    return VerifiedZDEXFeeIngressSliceV1(
        _VERIFIED_ZDEX_FEE_INGRESS_SLICE_TOKEN_V1,
        _VerifiedZDEXFeeIngressSliceFieldsV1(
            command_occurrence_id=command_occurrence_id,
            global_pre_state_root=global_pre_state_root,
            profile_root=profile_root,
            fee_state_root=fee_state.state_root,
            fee_asset_id=fee_state.fee_asset_id,
            fee_ingress_atoms=fee_state.fee_ingress_atoms,
            authority_head_root=authority_head_root,
            verifier_binding_root=verifier_binding_root,
        ),
    )


__all__ = [
    "VERIFIED_ZDEX_FEE_INGRESS_SLICE_SCHEMA_V1",
    "VerifiedZDEXFeeIngressSliceV1",
]
