"""Exact value-carrying ports for one same-occurrence ZDEX buy-and-burn."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    _require_atoms_u128,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    GovernedVerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXBurnV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    ZDEXAMMPurchaseJournalV2,
    ZDEXBurnJournalV1,
    zdex_occurrence_burn_port_v1,
)

ZDEX_ATOMIC_BUYBACK_LANE_PORT_CONTEXT_SCHEMA_V1: Final = (
    "zenodex/zdex-atomic-buyback-lane-port-context/v1"
)
ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1: Final = (
    "zenodex/zdex-atomic-buyback-lane-ports/v1"
)


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackLanePortContextV1:
    """Exact authority, release, policy, resource, journal, and receipt context."""

    authority_head_root: str
    policy_registry_root: str
    verifier_binding_root: str
    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    spot_module_release_id: str
    tokenomics_module_release_id: str
    issue_burn_policy_root: str
    buyback_execution_policy_root: str
    price_safety_policy_root: str
    oracle_occurrence_root: str
    quote_asset_id: str
    zdex_asset_id: str
    quote_source_bucket_id: str
    quote_pool_bucket_id: str
    zdex_pool_bucket_id: str
    burn_port_identity_root: str
    purchase_journal_root: str
    burn_journal_root: str
    purchase_leaf_binding_root: str
    burn_leaf_binding_root: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        root_fields = (
            "authority_head_root",
            "policy_registry_root",
            "verifier_binding_root",
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "spot_module_release_id",
            "tokenomics_module_release_id",
            "issue_burn_policy_root",
            "buyback_execution_policy_root",
            "price_safety_policy_root",
            "oracle_occurrence_root",
            "quote_asset_id",
            "zdex_asset_id",
            "quote_pool_bucket_id",
            "zdex_pool_bucket_id",
            "burn_port_identity_root",
            "purchase_journal_root",
            "burn_journal_root",
            "purchase_leaf_binding_root",
            "burn_leaf_binding_root",
        )
        for name in root_fields:
            value = getattr(self, name)
            if type(value) is not str:
                raise TypeError(f"atomic buyback lane-port context {name} must be exact str")
            _require_root(value, name=f"atomic buyback lane-port context {name}")
        if type(self.quote_source_bucket_id) is not str:
            raise TypeError(
                "atomic buyback lane-port context quote source must be exact str"
            )
        _require_token(
            self.quote_source_bucket_id,
            name="atomic buyback lane-port context quote source",
        )
        if self.quote_asset_id == self.zdex_asset_id:
            raise ValueError("atomic buyback lane-port assets must differ")

    @property
    def context_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-atomic-buyback-lane-port-context-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_ATOMIC_BUYBACK_LANE_PORT_CONTEXT_SCHEMA_V1,
            "authority_head_root": self.authority_head_root,
            "policy_registry_root": self.policy_registry_root,
            "verifier_binding_root": self.verifier_binding_root,
            "profile_root": self.profile_root,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "spot_module_release_id": self.spot_module_release_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "issue_burn_policy_root": self.issue_burn_policy_root,
            "buyback_execution_policy_root": self.buyback_execution_policy_root,
            "price_safety_policy_root": self.price_safety_policy_root,
            "oracle_occurrence_root": self.oracle_occurrence_root,
            "quote_asset_id": self.quote_asset_id,
            "zdex_asset_id": self.zdex_asset_id,
            "quote_source_bucket_id": self.quote_source_bucket_id,
            "quote_pool_bucket_id": self.quote_pool_bucket_id,
            "zdex_pool_bucket_id": self.zdex_pool_bucket_id,
            "burn_port_identity_root": self.burn_port_identity_root,
            "purchase_journal_root": self.purchase_journal_root,
            "burn_journal_root": self.burn_journal_root,
            "purchase_leaf_binding_root": self.purchase_leaf_binding_root,
            "burn_leaf_binding_root": self.burn_leaf_binding_root,
        }


def zdex_atomic_buyback_quote_flow_root_v1(
    context: ZDEXAtomicBuybackLanePortContextV1,
    quote_amount_atoms: int,
) -> str:
    """Bind the tokenomics-to-Spot quote role to exact context and value."""

    if type(context) is not ZDEXAtomicBuybackLanePortContextV1:
        raise TypeError("atomic buyback quote flow requires exact context")
    context.validate()
    amount = _require_atoms_u128(
        quote_amount_atoms,
        name="atomic buyback quote flow amount",
    )
    if amount == 0 or amount > MAX_DELTA_ATOMS_V1:
        raise ValueError("atomic buyback quote flow amount is outside effect bounds")
    return hash_global_v1(
        "zdex-atomic-buyback-quote-flow-v1",
        {
            "schema": ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1,
            "context_root": context.context_root,
            "quote_asset_id": context.quote_asset_id,
            "quote_source_bucket_id": context.quote_source_bucket_id,
            "quote_pool_bucket_id": context.quote_pool_bucket_id,
            "quote_amount_atoms": amount,
        },
    )


def zdex_atomic_buyback_purchased_zdex_flow_root_v1(
    context: ZDEXAtomicBuybackLanePortContextV1,
    purchased_zdex_atoms: int,
) -> str:
    """Bind the Spot-to-tokenomics burn role to exact context and value."""

    if type(context) is not ZDEXAtomicBuybackLanePortContextV1:
        raise TypeError("atomic buyback purchased-ZDEX flow requires exact context")
    context.validate()
    amount = _require_atoms_u128(
        purchased_zdex_atoms,
        name="atomic buyback purchased-ZDEX flow amount",
    )
    if amount == 0 or amount > MAX_DELTA_ATOMS_V1:
        raise ValueError("atomic buyback purchased-ZDEX flow amount is outside effect bounds")
    return hash_global_v1(
        "zdex-atomic-buyback-purchased-zdex-flow-v1",
        {
            "schema": ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1,
            "context_root": context.context_root,
            "zdex_asset_id": context.zdex_asset_id,
            "zdex_pool_bucket_id": context.zdex_pool_bucket_id,
            "burn_port_identity_root": context.burn_port_identity_root,
            "purchased_zdex_atoms": amount,
        },
    )


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackLanePortsV1:
    """The exact two value-carrying dependency roles between tokenomics and Spot."""

    context: ZDEXAtomicBuybackLanePortContextV1
    quote_flow_root: str
    purchased_zdex_flow_root: str
    tokenomics_quote_out_atoms: int
    spot_quote_in_atoms: int
    spot_zdex_out_atoms: int
    tokenomics_burn_in_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.context) is not ZDEXAtomicBuybackLanePortContextV1:
            raise TypeError("atomic buyback lane ports require exact context")
        self.context.validate()
        for name in ("quote_flow_root", "purchased_zdex_flow_root"):
            value = getattr(self, name)
            if type(value) is not str:
                raise TypeError(f"atomic buyback lane port {name} must be exact str")
            _require_root(value, name=f"atomic buyback lane port {name}")
        for name in (
            "tokenomics_quote_out_atoms",
            "spot_quote_in_atoms",
            "spot_zdex_out_atoms",
            "tokenomics_burn_in_atoms",
        ):
            value = getattr(self, name)
            _require_atoms_u128(value, name=f"atomic buyback lane port {name}")
            if value == 0 or value > MAX_DELTA_ATOMS_V1:
                raise ValueError(f"atomic buyback lane port {name} is outside effect bounds")
        if self.tokenomics_quote_out_atoms != self.spot_quote_in_atoms:
            raise ValueError("atomic buyback quote ports do not pair exactly")
        if self.spot_zdex_out_atoms != self.tokenomics_burn_in_atoms:
            raise ValueError("atomic buyback ZDEX ports do not pair exactly")
        if self.quote_flow_root != zdex_atomic_buyback_quote_flow_root_v1(
            self.context,
            self.tokenomics_quote_out_atoms,
        ):
            raise ValueError("atomic buyback quote-flow identity mismatch")
        if self.purchased_zdex_flow_root != (
            zdex_atomic_buyback_purchased_zdex_flow_root_v1(
                self.context,
                self.spot_zdex_out_atoms,
            )
        ):
            raise ValueError("atomic buyback purchased-ZDEX flow identity mismatch")

    @property
    def binding_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-atomic-buyback-lane-ports-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1,
            "context": self.context.to_canonical(),
            "quote_flow_root": self.quote_flow_root,
            "purchased_zdex_flow_root": self.purchased_zdex_flow_root,
            "tokenomics_quote_out_atoms": self.tokenomics_quote_out_atoms,
            "spot_quote_in_atoms": self.spot_quote_in_atoms,
            "spot_zdex_out_atoms": self.spot_zdex_out_atoms,
            "tokenomics_burn_in_atoms": self.tokenomics_burn_in_atoms,
        }


def _require_journal_pair_v1(
    purchase: ZDEXAMMPurchaseJournalV2,
    burn: ZDEXBurnJournalV1,
    expected_burn_port: str,
) -> None:
    if (
        burn.chain_id != purchase.chain_id
        or burn.deployment_root != purchase.deployment_root
        or burn.profile_root != purchase.profile_root
        or burn.writer_epoch != purchase.writer_epoch
        or burn.route_release_id != purchase.route_release_id
        or burn.command_occurrence_id != purchase.command_occurrence_id
        or burn.issue_burn_policy_root != purchase.issue_burn_policy_root
        or burn.buyback_budget_occurrence_root != purchase.buyback_budget_occurrence_root
        or burn.zdex_asset_id != purchase.zdex_asset_id
        or burn.purchase_occurrence_root != purchase.journal_root
        or burn.authorized_quote_input_atoms != purchase.quote_amount_in_atoms
        or burn.burned_zdex_atoms != purchase.purchased_zdex_atoms
        or purchase.burn_bucket_id != expected_burn_port
        or burn.burn_bucket_id != expected_burn_port
        or purchase.burn_bucket_post_atoms != burn.burn_bucket_pre_atoms
    ):
        raise ValueError("atomic buyback purchase and burn ports do not bind")


def _require_receipt_pair_v1(
    purchase: ZDEXAMMPurchaseJournalV2,
    burn: ZDEXBurnJournalV1,
    verified_purchase: GovernedVerifiedZDEXAMMPurchaseV2,
    verified_burn: VerifiedZDEXBurnV1,
) -> None:
    purchase_leaf = verified_purchase.verified_leaf
    if (
        purchase_leaf.route_release_id != purchase.route_release_id
        or purchase_leaf.module_release_id != purchase.spot_module_release_id
        or purchase_leaf.command_occurrence_id != purchase.command_occurrence_id
        or purchase_leaf.profile_root != purchase.profile_root
        or purchase_leaf.writer_epoch != purchase.writer_epoch
        or purchase_leaf.journal_root != purchase.journal_root
        or purchase_leaf.effect_plan_root != purchase.effect_plan_root
        or verified_burn.route_release_id != burn.route_release_id
        or verified_burn.module_release_id != burn.tokenomics_module_release_id
        or verified_burn.command_occurrence_id != burn.command_occurrence_id
        or verified_burn.profile_root != burn.profile_root
        or verified_burn.writer_epoch != burn.writer_epoch
        or verified_burn.journal_root != burn.journal_root
        or verified_burn.effect_plan_root != burn.effect_plan_root
        or verified_purchase.authority_head_root != verified_burn.authority_head_root
        or verified_purchase.verifier_binding_root != verified_burn.verifier_binding_root
    ):
        raise ValueError("atomic buyback purchase and burn ports do not bind")


def _build_lane_port_context_v1(
    purchase: ZDEXAMMPurchaseJournalV2,
    burn: ZDEXBurnJournalV1,
    verified_purchase: GovernedVerifiedZDEXAMMPurchaseV2,
    verified_burn: VerifiedZDEXBurnV1,
) -> ZDEXAtomicBuybackLanePortContextV1:
    expected_burn_port = zdex_occurrence_burn_port_v1(
        profile_root=purchase.profile_root,
        route_release_id=purchase.route_release_id,
        command_occurrence_id=purchase.command_occurrence_id,
    )
    return ZDEXAtomicBuybackLanePortContextV1(
        authority_head_root=verified_purchase.authority_head_root,
        policy_registry_root=verified_purchase.policy_registry_root,
        verifier_binding_root=verified_purchase.verifier_binding_root,
        profile_root=purchase.profile_root,
        route_release_id=purchase.route_release_id,
        command_occurrence_id=purchase.command_occurrence_id,
        spot_module_release_id=purchase.spot_module_release_id,
        tokenomics_module_release_id=burn.tokenomics_module_release_id,
        issue_burn_policy_root=purchase.issue_burn_policy_root,
        buyback_execution_policy_root=purchase.buyback_execution_policy_root,
        price_safety_policy_root=purchase.price_safety_policy_root,
        oracle_occurrence_root=purchase.oracle_occurrence_root,
        quote_asset_id=purchase.quote_asset_id,
        zdex_asset_id=purchase.zdex_asset_id,
        quote_source_bucket_id=purchase.quote_source_bucket_id,
        quote_pool_bucket_id=purchase.quote_pool_bucket_id,
        zdex_pool_bucket_id=purchase.zdex_pool_bucket_id,
        burn_port_identity_root=expected_burn_port,
        purchase_journal_root=purchase.journal_root,
        burn_journal_root=burn.journal_root,
        purchase_leaf_binding_root=verified_purchase.verified_leaf.leaf_binding_root,
        burn_leaf_binding_root=verified_burn.leaf_binding_root,
    )


def derive_zdex_atomic_buyback_lane_ports_v1(
    purchase: ZDEXAMMPurchaseJournalV2,
    burn: ZDEXBurnJournalV1,
    verified_purchase: GovernedVerifiedZDEXAMMPurchaseV2,
    verified_burn: VerifiedZDEXBurnV1,
) -> ZDEXAtomicBuybackLanePortsV1:
    """Derive exact value ports from closed journals and receipt-bound witnesses."""

    if type(purchase) is not ZDEXAMMPurchaseJournalV2:
        raise TypeError("atomic buyback purchase journal must be exact typed data")
    if type(burn) is not ZDEXBurnJournalV1:
        raise TypeError("atomic buyback burn journal must be exact typed data")
    if type(verified_purchase) is not GovernedVerifiedZDEXAMMPurchaseV2:
        raise TypeError("atomic buyback purchase witness must be verifier-constructed")
    if type(verified_burn) is not VerifiedZDEXBurnV1:
        raise TypeError("atomic buyback burn witness must be verifier-constructed")
    purchase.validate()
    burn.validate()
    expected_burn_port = zdex_occurrence_burn_port_v1(
        profile_root=purchase.profile_root,
        route_release_id=purchase.route_release_id,
        command_occurrence_id=purchase.command_occurrence_id,
    )
    _require_journal_pair_v1(purchase, burn, expected_burn_port)
    _require_receipt_pair_v1(purchase, burn, verified_purchase, verified_burn)
    context = _build_lane_port_context_v1(
        purchase,
        burn,
        verified_purchase,
        verified_burn,
    )
    return ZDEXAtomicBuybackLanePortsV1(
        context=context,
        quote_flow_root=zdex_atomic_buyback_quote_flow_root_v1(
            context,
            purchase.quote_amount_in_atoms,
        ),
        purchased_zdex_flow_root=zdex_atomic_buyback_purchased_zdex_flow_root_v1(
            context,
            purchase.purchased_zdex_atoms,
        ),
        tokenomics_quote_out_atoms=purchase.quote_amount_in_atoms,
        spot_quote_in_atoms=purchase.quote_amount_in_atoms,
        spot_zdex_out_atoms=purchase.purchased_zdex_atoms,
        tokenomics_burn_in_atoms=burn.burned_zdex_atoms,
    )


__all__ = [
    "ZDEXAtomicBuybackLanePortContextV1",
    "ZDEXAtomicBuybackLanePortsV1",
    "ZDEX_ATOMIC_BUYBACK_LANE_PORT_CONTEXT_SCHEMA_V1",
    "ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1",
    "derive_zdex_atomic_buyback_lane_ports_v1",
    "zdex_atomic_buyback_purchased_zdex_flow_root_v1",
    "zdex_atomic_buyback_quote_flow_root_v1",
]
