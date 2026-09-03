"""Receipt admission for the ASSET_TRANSFER allocation fragment (C9a).

``verify_asset_transfer_fragment_receipt_v1`` takes the receipt-verified
module witness (``VerifiedLaneModuleTransitionV1``, mintable only by
``verify_asset_transfer_lane_module_receipt_v1`` after a succinct-receipt
check against the recomputed module journal under an ACTIVE_NEW release
image), rebuilds the caller's accepted value through the exact-typed
snapshot, binds the rebuilt value to the witness at the journal root,
re-runs the wave-B fragment producer on the rebuilt value, and mints the
opaque ``VerifiedLaneAllocationFragmentV1`` witness (defined in the
certificate module, its only consumer, so the two modules do not import
each other; minted here through that module's private token) carrying the
rebuilt journal's header (chain id, deployment root, profile root, writer
epoch) for the certificate's header binding. The certificate check's
witness slots consume it (C9b-2a) and the registry registers ASSET_TRANSFER
receipt-backed (C9b-2b), so an enabled ASSET_TRANSFER fragment is accepted
only through this witness.

Why the snapshot comes first (Opus P28 F1): the journal-root equality binds
nested values only through the roots in the journal preimage, and a root is
read from the object that claims it. An ordinary subclass admitted by an
``isinstance`` gate can override a root-bearing property to report the
genuine root while carrying foreign rows, so the equality would hold for
rows the receipt never proved. The snapshot refuses every nested value that
is not the exact registered class and every scalar that is not an exact
primitive, and re-runs every construction invariant on the rebuilt value,
so the rows the producer reads are the rows whose roots the receipt proved.
Snapshot refusals raise ``TypeError``/``ValueError`` like every type
boundary on this path; every witness reject is a value.

NONCLAIMS. ``claimant_entitlements`` are caller-chosen AT THIS LAYER: the
wave-B producer's coverage fold is keyed on ``(asset, control_domain)`` only,
so claimant identity and the split across claimants are not proved by the
receipt here. They are bound at the certificate layer, whose entitlement
check (``ENTITLEMENT_ROWS_DRIFT``) requires the derived allocation rows to
equal the V1 ``liabilities`` partition of ``GlobalEconomicStateV1`` exactly; since
C9b-2b this producer's rows enter that check through the witness slot, so
the partition equality is what binds claimant identity, and whether that
partition is itself authoritative for
asset-transfer custody is an unresolved policy question (UP-xx), not a claim
of this module. The Rust twin
``zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs``
(C9b-1) declares the same ordered reject family, check order, and detail
strings (pinned mechanically by the admission suite); it refuses malformed
inputs at its boundary with an ``AbiErrorV1``, the Rust analogue of the raise
here, so the producer's ``ACCEPTED_INVALID`` is unreachable through either
admission. The succinct-receipt check itself is inherited from
``lane_module_receipt_verification_v1``; this module adds no cryptographic
claim of its own.

DECLARED RESIDUALS. In-process ``object.__new__`` construction bypasses every
``__post_init__`` in Python; the check (0) rebuild refuses the values it can
re-validate (hostile scalars, subclasses, inconsistent fields), but a forged
witness whose planted scalars are well-formed and mutually consistent is
indistinguishable from a minted one, exactly as for every token-gated witness
on this path. The prior fragment is bound to the journal only through its
``lane_state_root`` (``STALE_JOURNAL``); binding it to its own receipt is
certificate-level chain continuity (C9b), not this admission. Reject-code
divergence, decided: Python refuses malformed or forged inputs at check (0)
by raising ``TypeError``/``ValueError`` at the type boundary, while the Rust
producer returns ``ACCEPTED_INVALID`` as a value because its plain structs
have no construction validation; the parity vectors cover well-formed inputs
only, and the Rust admission twin documents the same split: it validates row
tokens at its boundary and leaves entitlement ordering and zero amounts to the
producer's ``ENTITLEMENT_ROWS_NOT_CANONICAL`` where the snapshot here raises.

Research-only evidence. It grants no writer, verifier, release, or
publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final

from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    _snapshot_asset_transfer_lane_module_accepted_v1,
)
from .global_accounting_allocation_certificate_v1 import (
    _VERIFIED_FRAGMENT_TOKEN,
    ClaimantEntitlementRowV1,
    ControlledLocationRowV1,
    LaneAllocationFragmentV1,
    LaneProducerKindV1,
    PendingExternalObligationRowV1,
    TerminalBindingRowV1,
    UnencumberedReserveRowV1,
    VerifiedLaneAllocationFragmentV1,
    _VerifiedFragmentFieldsV1,
)
from .global_accounting_lane_producers_v1 import (
    ReceiptBackedProducerRejectedV1,
    produce_asset_transfer_fragment_v1,
)
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_dataclass_tuple_v1,
)
from .global_settlement_types_v1 import LaneIdV1, LaneStateRootV1, _require_root
from .lane_module_receipt_verification_v1 import (
    ReceiptKindV1,
    VerifiedLaneModuleTransitionV1,
    require_verified_lane_module_transition_scalars_v1,
)

RECEIPT_ADMISSION_SCHEMA_V1: Final = "zenodex/asset-transfer-receipt-admission/v1"

# Cross-language family pin (Opus P28 F5): the Rust admission twin declares exactly
# this ordered family; test_witness_reject_family_and_check_order_match_the_rust_twin
# pins the variants, the ALL array, the wire strings, and the in-function order.
RECEIPT_WITNESS_REJECT_CODES_V1: Final[tuple[str, ...]] = (
    "WITNESS_KIND_DRIFT",
    "WITNESS_JOURNAL_ROOT_DRIFT",
    "WITNESS_STATEMENT_ROOT_DRIFT",
    "WITNESS_OCCURRENCE_DRIFT",
    "WITNESS_BINDING_ROOT_DRIFT",
)


class ReceiptWitnessRejectCodeV1(str, Enum):
    """Closed witness-binding rejects, checked before the producer runs.

    ``WITNESS_JOURNAL_ROOT_DRIFT`` is the one load-bearing binding. The
    other four are defensive: the kind, statement, and occurrence checks can
    differ only on a forged witness (the mint point derives every witness
    scalar from the recomputed journal), and the binding-root check can
    differ only on a drifted producer (it assigns that very root).
    """

    WITNESS_KIND_DRIFT = "WITNESS_KIND_DRIFT"
    WITNESS_JOURNAL_ROOT_DRIFT = "WITNESS_JOURNAL_ROOT_DRIFT"
    WITNESS_STATEMENT_ROOT_DRIFT = "WITNESS_STATEMENT_ROOT_DRIFT"
    WITNESS_OCCURRENCE_DRIFT = "WITNESS_OCCURRENCE_DRIFT"
    WITNESS_BINDING_ROOT_DRIFT = "WITNESS_BINDING_ROOT_DRIFT"


@dataclass(frozen=True, slots=True)
class ReceiptWitnessRejectedV1:
    """A witness-binding refusal: nothing is minted, every input left unchanged."""

    code: ReceiptWitnessRejectCodeV1
    lane_id: LaneIdV1
    committed_lane_root: str
    detail: str

    def __post_init__(self) -> None:
        if type(self.code) is not ReceiptWitnessRejectCodeV1:
            raise TypeError("receipt witness reject code is not closed")
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("receipt witness lane id is not closed")
        _require_root(
            self.committed_lane_root,
            name="receipt witness committed lane root",
            allow_zero=True,
        )
        if type(self.detail) is not str or not self.detail or len(self.detail) > 200:
            raise ValueError("receipt witness detail must be a short non-empty string")



def _rebuild_prior_fragment_v1(prior: LaneAllocationFragmentV1) -> LaneAllocationFragmentV1:
    """Exact-typed rebuild of the caller's prior fragment (rows and scalars), re-running its invariants."""

    if type(prior) is not LaneAllocationFragmentV1:
        raise TypeError("prior fragment must be the exact typed value")
    families = {
        "controlled_locations": ControlledLocationRowV1,
        "claimant_entitlements": ClaimantEntitlementRowV1,
        "unencumbered_reserves": UnencumberedReserveRowV1,
        "pending_external_obligations": PendingExternalObligationRowV1,
        "terminal_bindings": TerminalBindingRowV1,
    }
    # Explicit scalar checks: the generic helper admits enums only on a fixed field-name set.
    if type(prior.lane_id) is not LaneIdV1 or type(prior.producer_kind) is not LaneProducerKindV1:
        raise TypeError("prior fragment lane id and producer kind must be exact closed members")
    if type(prior.enabled) is not bool:
        raise TypeError("prior fragment enabled flag must be an exact bool")
    for name in ("module_release_id", "lane_state_root", "binding_root"):
        value = getattr(prior, name)
        if type(value) is not str:
            raise TypeError(f"prior fragment {name} must be exact text")
        _require_root(value, name=f"prior fragment {name}", allow_zero=True)
    for name in families:
        if type(getattr(prior, name)) is not tuple:
            raise TypeError(f"prior fragment {name} must be an exact tuple")
    rebuilt = {
        name: _snapshot_dataclass_tuple_v1(getattr(prior, name), row_type, f"prior fragment {name}")
        for name, row_type in families.items()
    }
    return replace(prior, **rebuilt)


def verify_asset_transfer_fragment_receipt_v1(
    witness: VerifiedLaneModuleTransitionV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
    lane_root: LaneStateRootV1,
    prior_fragment: LaneAllocationFragmentV1,
    claimant_entitlements: tuple[ClaimantEntitlementRowV1, ...],
) -> (
    VerifiedLaneAllocationFragmentV1
    | ReceiptWitnessRejectedV1
    | ReceiptBackedProducerRejectedV1
):
    """Admit one fragment only through the receipt-verified module witness.

    Check order: (0) every caller-supplied value is rebuilt at the boundary:
    the witness's exported scalars are validated (exact primitives, well-formed
    roots, closed kind), the committed lane root and the prior fragment are
    rebuilt through their constructors with exact rows and scalars, the
    entitlement rows are rebuilt as exact rows, and ``accepted`` is rebuilt
    through the exact-typed snapshot (every nested value the exact registered
    class, every scalar an exact primitive, every construction invariant re-run
    on the rebuilt value), so a subclass overriding a root-bearing property, a
    validation-bypassed object, or a planted hostile scalar is refused before
    any binding is read; (1) the witness carries a
    succinct receipt (defensive; the mint point enforces it); (2) the
    receipt-verified module journal root equals the rebuilt
    ``module_journal.journal_root`` -- the one equality that binds the
    caller's value to the proof; (3) the statement root and command
    occurrence agree (defensive double-binding: both are pinned by the journal
    preimage, so only a forged witness can differ); then the wave-B producer
    re-runs with its full check family on the rebuilt value, and (4) the
    produced ``binding_root`` must equal the rebuilt journal's receipt root
    (defensive producer-drift protection: the producer assigns that very
    root, so only a drifted producer can differ; the module witness carries
    no receipt root, so this binds nothing to it -- instead it defines the
    ``receipt_root`` the minted fragment witness exports as an independent
    handle for certificate consumption). Every witness reject
    is a value and no input is mutated; the type-boundary refusals of (0)
    raise, as every type boundary on this path does.
    """

    if type(witness) is not VerifiedLaneModuleTransitionV1:
        raise TypeError("fragment admission requires the module receipt witness")
    require_verified_lane_module_transition_scalars_v1(witness)
    if type(lane_root) is not LaneStateRootV1:
        raise TypeError("fragment admission requires the exact LaneStateRootV1")
    _require_exact_dataclass_scalars_v1(lane_root, name="committed lane root")
    lane_root = replace(lane_root)
    prior_fragment = _rebuild_prior_fragment_v1(prior_fragment)
    claimant_entitlements = _snapshot_dataclass_tuple_v1(
        claimant_entitlements, ClaimantEntitlementRowV1, "claimant entitlements"
    )
    owned = _snapshot_asset_transfer_lane_module_accepted_v1(accepted)
    journal = owned.module_journal
    committed = lane_root.state_root
    if witness.receipt_kind is not ReceiptKindV1.SUCCINCT:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_KIND_DRIFT,
            lane_root.lane_id,
            committed,
            "witness kind",
        )
    if witness.module_journal_root != journal.journal_root:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_JOURNAL_ROOT_DRIFT,
            lane_root.lane_id,
            committed,
            "journal root",
        )
    if witness.statement_root != owned.statement_root:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_STATEMENT_ROOT_DRIFT,
            lane_root.lane_id,
            committed,
            "statement root",
        )
    if witness.command_occurrence_id != journal.command_occurrence_id:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_OCCURRENCE_DRIFT,
            lane_root.lane_id,
            committed,
            "command occurrence",
        )
    produced = produce_asset_transfer_fragment_v1(
        owned, lane_root, prior_fragment, claimant_entitlements
    )
    if isinstance(produced, ReceiptBackedProducerRejectedV1):
        return produced
    if produced.binding_root != journal.receipt_root:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_BINDING_ROOT_DRIFT,
            lane_root.lane_id,
            committed,
            "binding root",
        )
    return VerifiedLaneAllocationFragmentV1(
        _VerifiedFragmentFieldsV1(
            fragment=produced,
            module_journal_root=witness.module_journal_root,
            receipt_root=journal.receipt_root,
            receipt_digest=witness.receipt_digest,
            expected_image_id=witness.expected_image_id,
            chain_id=journal.chain_id,
            deployment_root=journal.deployment_root,
            profile_root=journal.profile_root,
            writer_epoch=journal.writer_epoch,
        ),
        _VERIFIED_FRAGMENT_TOKEN,
    )


__all__ = [
    "RECEIPT_ADMISSION_SCHEMA_V1",
    "RECEIPT_WITNESS_REJECT_CODES_V1",
    "ReceiptWitnessRejectCodeV1",
    "ReceiptWitnessRejectedV1",
    "VerifiedLaneAllocationFragmentV1",
    "verify_asset_transfer_fragment_receipt_v1",
]
