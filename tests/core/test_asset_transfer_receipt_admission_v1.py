"""Receipt admission for the ASSET_TRANSFER allocation fragment (C9a)."""

from __future__ import annotations

from dataclasses import replace
from typing import Any

import pytest

from src.core import asset_transfer_receipt_admission_v1 as admission
from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core.asset_lane_projection_v1 import (
    AssetLanePrivatePortV1,
    AssetLaneStateProjectionV1,
)
from src.core.asset_transfer_lane_module_v1 import AssetTransferLaneModuleAcceptedV1
from src.core.asset_transfer_receipt_admission_v1 import (
    ReceiptWitnessRejectCodeV1,
    ReceiptWitnessRejectedV1,
    VerifiedLaneAllocationFragmentV1,
    verify_asset_transfer_fragment_receipt_v1,
)
from src.core.global_accounting_lane_producers_v1 import (
    ReceiptBackedProducerRejectCodeV1,
    ReceiptBackedProducerRejectedV1,
)
from src.core.global_economic_proof_v1 import (
    LaneModuleTransitionJournalV1,
    ReceiptKindV1,
)
from src.core.global_settlement_types_v1 import (
    EconomicAmountV1,
    LaneIdV1,
    LaneStateRootV1,
)
from src.core.lane_module_receipt_verification_v1 import VerifiedLaneModuleTransitionV1
from tests.core.test_global_settlement_abi_v1 import (
    _asset_module_input_for_occurrence,
    _epoch_asset_module_state,
    _global_state_from_asset_module,
    _occurrence,
    _profile,
    _verified_asset_module_for_occurrence,
)

CUSTODIAN_ROW = EconomicAmountV1("custodian", "USD", "vault", 100)
ATTACKER_ROW = EconomicAmountV1("attacker", "USD", "vault", 100)
FOREIGN_ROOT = "0x" + "77" * 32


def _fixture(*, custody: tuple[EconomicAmountV1, ...] = (), authority_epoch: int | None = None):
    """Mint a REAL module witness through the ABI fixture chain.

    With ``custody`` the module state's USD supply grows by the custodied
    total so the projection conserves supply; the witness then proves those
    custody rows through the private-port root inside the journal preimage.
    """

    profile, route = _profile() if authority_epoch is None else _profile(authority_epoch=authority_epoch)
    base_state = _epoch_asset_module_state(profile)
    pre_state = _global_state_from_asset_module(profile, base_state, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    module_input = _asset_module_input_for_occurrence(profile, occurrence, base_state)
    if custody:
        # Swap the supply-bumped state and the custody rows in ONE replace so
        # the input's projection conserves supply at construction.
        extra = sum(row.amount_atoms for row in custody)
        custodied_state = replace(
            base_state,
            supplies=tuple(
                replace(row, amount_atoms=row.amount_atoms + extra) if row.asset == "USD" else row
                for row in base_state.supplies
            ),
        )
        module_input = replace(module_input, pre_state=custodied_state, custody=custody)
    accepted, witness = _verified_asset_module_for_occurrence(profile, occurrence, module_input)
    lane_root = LaneStateRootV1(
        lane_id=LaneIdV1.ASSET_TRANSFER,
        module_release_id=accepted.module_journal.module_release_id,
        enabled=True,
        state_root=accepted.module_journal.post_lane_root,
    )
    prior = cert.LaneAllocationFragmentV1(
        lane_id=LaneIdV1.ASSET_TRANSFER,
        module_release_id=accepted.module_journal.module_release_id,
        enabled=True,
        lane_state_root=accepted.module_journal.pre_lane_root,
        producer_kind=cert.LaneProducerKindV1.RECEIPT_BACKED,
        binding_root=accepted.module_journal.pre_lane_root,
        controlled_locations=(),
        claimant_entitlements=(),
        unencumbered_reserves=(),
        pending_external_obligations=(),
        terminal_bindings=(),
    )
    return accepted, witness, lane_root, prior


def _admission_fixture():
    return _fixture()


def _plant(value: Any, **changes: Any) -> Any:
    """object.__new__ forgery: copy every field, bypassing __post_init__."""

    forged = object.__new__(type(value))
    for field in type(value).__dataclass_fields__:
        object.__setattr__(forged, field, getattr(value, field))
    for field, replacement in changes.items():
        object.__setattr__(forged, field, replacement)
    return forged


def _forge_witness(witness: VerifiedLaneModuleTransitionV1, **changes: Any) -> VerifiedLaneModuleTransitionV1:
    """object.__new__ forgery of the module witness (bypassing the verifier
    token): the only way to vary a witness scalar, since the mint point
    derives every scalar from the recomputed journal."""

    forged = object.__new__(VerifiedLaneModuleTransitionV1)
    object.__setattr__(forged, "_fields", replace(witness._fields, **changes))
    return forged


def _spoofed_port(accepted: AssetTransferLaneModuleAcceptedV1) -> AssetLanePrivatePortV1:
    """The Opus P28 F1 proof of concept: an ordinary subclass whose only
    override reports the genuine port root while the port carries foreign
    custody rows inside a fully valid projection (no validation bypass)."""

    real_port = accepted.private_port

    class SpoofedPort(AssetLanePrivatePortV1):
        @property
        def port_root(self) -> str:  # type: ignore[override]
            return real_port.port_root

    stolen_post = replace(real_port.post_state, custody=(ATTACKER_ROW,))
    spoofed = SpoofedPort(
        producer_module_schema=real_port.producer_module_schema,
        module_release_id=real_port.module_release_id,
        command_occurrence_id=real_port.command_occurrence_id,
        pre_state=real_port.pre_state,
        post_state=stolen_post,
        module_effect_plan_root=real_port.module_effect_plan_root,
        terminal_obligations_root=real_port.terminal_obligations_root,
    )
    assert spoofed.port_root == real_port.port_root
    assert spoofed.post_state.custody == (ATTACKER_ROW,)
    return spoofed


def test_witness_token_is_verifier_only() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedLaneAllocationFragmentV1(object(), None)  # type: ignore[arg-type]


def test_admission_requires_the_module_witness_type() -> None:
    accepted, _witness, lane_root, prior = _admission_fixture()
    with pytest.raises(TypeError, match="module receipt witness"):
        verify_asset_transfer_fragment_receipt_v1(
            object(),  # type: ignore[arg-type]
            accepted,
            lane_root,
            prior,
            (),
        )


def test_receipt_admitted_fragment_carries_the_witness_binding() -> None:
    accepted, witness, lane_root, prior = _admission_fixture()
    admitted = verify_asset_transfer_fragment_receipt_v1(witness, accepted, lane_root, prior, ())
    assert isinstance(admitted, VerifiedLaneAllocationFragmentV1)
    assert admitted.fragment.binding_root == accepted.module_journal.receipt_root
    assert admitted.fragment.controlled_locations == ()
    assert admitted.module_journal_root == accepted.module_journal.journal_root
    assert admitted.expected_image_id == witness.expected_image_id
    assert admitted.receipt_digest == witness.receipt_digest
    with pytest.raises(AttributeError, match="immutable"):
        admitted.fragment = None  # type: ignore[misc,assignment]


def test_admitted_controlled_rows_are_the_receipt_proved_custody_rows() -> None:
    accepted, witness, lane_root, prior = _fixture(custody=(CUSTODIAN_ROW,))
    entitlement = cert.ClaimantEntitlementRowV1("USD", "custodian", "vault", 100)
    admitted = verify_asset_transfer_fragment_receipt_v1(
        witness, accepted, lane_root, prior, (entitlement,)
    )
    assert isinstance(admitted, VerifiedLaneAllocationFragmentV1)
    assert accepted.private_port.post_state.custody == (CUSTODIAN_ROW,)
    assert admitted.fragment.controlled_locations == (
        cert.ControlledLocationRowV1("USD", "custodian", "vault", 100),
    )


def test_foreign_accepted_value_is_rejected_at_the_journal_root() -> None:
    accepted, witness, lane_root, prior = _admission_fixture()
    foreign_accepted, _foreign_witness, _root, _prior = _fixture(authority_epoch=8)
    assert foreign_accepted.module_journal.journal_root != accepted.module_journal.journal_root
    reject = verify_asset_transfer_fragment_receipt_v1(
        witness, foreign_accepted, lane_root, prior, ()
    )
    assert isinstance(reject, ReceiptWitnessRejectedV1)
    assert reject.code is ReceiptWitnessRejectCodeV1.WITNESS_JOURNAL_ROOT_DRIFT
    assert reject.detail == "journal root"


def test_subclassed_private_port_with_a_spoofed_root_is_refused_at_construction() -> None:
    """Opus P28 F1 regression, the reviewer's proof of concept: before C9a' the
    isinstance gate admitted this port and the admission minted a witness that
    reassigned 100 USD atoms of custody from the custodian to the attacker
    under the genuine journal root; the accepted constructor now refuses the
    subclass at its exact-type gate."""

    accepted, _witness, _lane_root, _prior = _fixture(custody=(CUSTODIAN_ROW,))
    spoofed = _spoofed_port(accepted)
    with pytest.raises(TypeError, match="exact typed value"):
        AssetTransferLaneModuleAcceptedV1(
            statement_root=accepted.statement_root,
            post_state=accepted.post_state,
            effects=accepted.effects,
            module_journal=accepted.module_journal,
            private_port=spoofed,
        )


def test_planted_subclass_port_is_refused_by_the_admission_snapshot() -> None:
    """The admission does not lean on the construction gate: the same spoofed
    port planted through object.__new__ (bypassing __post_init__) is refused by
    the exact-typed snapshot before any binding is read, so no witness reject
    and no fragment ever sees the foreign rows."""

    accepted, witness, lane_root, prior = _fixture(custody=(CUSTODIAN_ROW,))
    planted = _plant(accepted, private_port=_spoofed_port(accepted))
    assert planted.module_journal.journal_root == witness.module_journal_root
    with pytest.raises(TypeError, match="exact typed value"):
        verify_asset_transfer_fragment_receipt_v1(
            witness,
            planted,
            lane_root,
            prior,
            (cert.ClaimantEntitlementRowV1("USD", "attacker", "vault", 100),),
        )


def test_subclassed_projection_is_refused_by_the_port_gate() -> None:
    """The port's own projection gates are exact too: a projection subclass
    that skips validation cannot enter a port (the reviewer's first variant)."""

    accepted, _witness, _lane_root, _prior = _fixture(custody=(CUSTODIAN_ROW,))
    real_port = accepted.private_port
    real_post = real_port.post_state

    class LooseProjection(AssetLaneStateProjectionV1):
        def __post_init__(self) -> None:  # skip validation entirely
            pass

    loose = LooseProjection(
        real_post.asset_policy_registry_root,
        real_post.fee_policy_registry_root,
        real_post.balances,
        (EconomicAmountV1("attacker", "USD", "vault", 999),),
        real_post.supplies,
    )
    with pytest.raises(TypeError, match="exact typed value"):
        AssetLanePrivatePortV1(
            producer_module_schema=real_port.producer_module_schema,
            module_release_id=real_port.module_release_id,
            command_occurrence_id=real_port.command_occurrence_id,
            pre_state=real_port.pre_state,
            post_state=loose,
            module_effect_plan_root=real_port.module_effect_plan_root,
            terminal_obligations_root=real_port.terminal_obligations_root,
        )


def test_subclassed_journal_with_a_spoofed_journal_root_is_refused() -> None:
    """The journal is the other root-bearing value the binding reads: a
    subclass reporting the genuine journal root over a foreign post-lane root
    would carry the receipt onto a lane root it never certified. It is refused
    at the accepted constructor's exact-type gate and, when planted through
    object.__new__, by the admission snapshot."""

    accepted, witness, lane_root, prior = _admission_fixture()
    real_journal = accepted.module_journal

    class SpoofedJournal(LaneModuleTransitionJournalV1):
        @property
        def journal_root(self) -> str:  # type: ignore[override]
            return real_journal.journal_root

    fields = {name: getattr(real_journal, name) for name in type(real_journal).__dataclass_fields__}
    fields["post_lane_root"] = FOREIGN_ROOT
    spoofed = SpoofedJournal(**fields)
    assert spoofed.journal_root == witness.module_journal_root
    assert spoofed.post_lane_root != real_journal.post_lane_root
    with pytest.raises(TypeError, match="exact typed value"):
        AssetTransferLaneModuleAcceptedV1(
            statement_root=accepted.statement_root,
            post_state=accepted.post_state,
            effects=accepted.effects,
            module_journal=spoofed,
            private_port=accepted.private_port,
        )
    planted = _plant(accepted, module_journal=spoofed)
    with pytest.raises(TypeError, match="exact typed value"):
        verify_asset_transfer_fragment_receipt_v1(witness, planted, lane_root, prior, ())


def test_validation_bypassed_accepted_is_refused_by_the_snapshot() -> None:
    """A forged accepted value (object.__new__, inconsistent statement root)
    reached check (3) before C9a'; the snapshot now re-runs the construction
    invariants on the rebuilt value and refuses it at the receipt-root
    recomputation, before any binding is read."""

    accepted, witness, lane_root, prior = _admission_fixture()
    forged = _plant(accepted, statement_root=FOREIGN_ROOT)
    with pytest.raises(ValueError, match="receipt root mismatch"):
        verify_asset_transfer_fragment_receipt_v1(witness, forged, lane_root, prior, ())


@pytest.mark.parametrize(
    ("changes", "code", "detail"),
    (
        pytest.param(
            {"receipt_kind": ReceiptKindV1.COMPOSITE},
            ReceiptWitnessRejectCodeV1.WITNESS_KIND_DRIFT,
            "witness kind",
            id="kind",
        ),
        pytest.param(
            {"statement_root": FOREIGN_ROOT},
            ReceiptWitnessRejectCodeV1.WITNESS_STATEMENT_ROOT_DRIFT,
            "statement root",
            id="statement_root",
        ),
        pytest.param(
            {"command_occurrence_id": FOREIGN_ROOT},
            ReceiptWitnessRejectCodeV1.WITNESS_OCCURRENCE_DRIFT,
            "command occurrence",
            id="occurrence",
        ),
    ),
)
def test_defensive_witness_checks_have_forgery_witnesses(
    changes: dict[str, Any], code: ReceiptWitnessRejectCodeV1, detail: str
) -> None:
    """Opus P28 F3: checks (1) and (3) are defensive. The mint point derives
    every witness scalar from the recomputed journal, so only a forged witness
    can vary a scalar while the journal root still matches; each defensive arm
    has exactly this forgery witness and refuses it as a value."""

    accepted, witness, lane_root, prior = _admission_fixture()
    forged = _forge_witness(witness, **changes)
    assert forged.module_journal_root == accepted.module_journal.journal_root
    reject = verify_asset_transfer_fragment_receipt_v1(forged, accepted, lane_root, prior, ())
    assert isinstance(reject, ReceiptWitnessRejectedV1)
    assert reject.code is code
    assert reject.detail == detail
    assert reject.committed_lane_root == lane_root.state_root


def test_binding_root_drift_is_producer_drift_protection(monkeypatch: pytest.MonkeyPatch) -> None:
    """Opus P28 F3/F4: check (4) binds nothing to the witness (the witness
    carries no receipt root). The producer assigns binding_root from the same
    journal, so only a drifted producer can differ; this is that witness."""

    accepted, witness, lane_root, prior = _admission_fixture()
    genuine = admission.produce_asset_transfer_fragment_v1

    def drifted(*args: Any, **kwargs: Any) -> Any:
        produced = genuine(*args, **kwargs)
        return replace(produced, binding_root=FOREIGN_ROOT)

    monkeypatch.setattr(admission, "produce_asset_transfer_fragment_v1", drifted)
    reject = verify_asset_transfer_fragment_receipt_v1(witness, accepted, lane_root, prior, ())
    assert isinstance(reject, ReceiptWitnessRejectedV1)
    assert reject.code is ReceiptWitnessRejectCodeV1.WITNESS_BINDING_ROOT_DRIFT
    assert reject.detail == "binding root"


@pytest.mark.parametrize(
    ("mutate", "code"),
    (
        pytest.param("disabled", ReceiptBackedProducerRejectCodeV1.LANE_DISABLED, id="lane_disabled"),
        pytest.param("release", ReceiptBackedProducerRejectCodeV1.MODULE_RELEASE_DRIFT, id="module_release_drift"),
        pytest.param("post_root", ReceiptBackedProducerRejectCodeV1.JOURNAL_ROOT_DRIFT, id="journal_root_drift"),
    ),
)
def test_producer_rejects_pass_through_unchanged(
    mutate: str, code: ReceiptBackedProducerRejectCodeV1
) -> None:
    accepted, witness, lane_root, prior = _admission_fixture()
    if mutate == "disabled":
        mutated = replace(lane_root, enabled=False)
    elif mutate == "release":
        mutated = replace(lane_root, module_release_id=FOREIGN_ROOT)
    else:
        mutated = replace(lane_root, state_root=FOREIGN_ROOT)
    reject = verify_asset_transfer_fragment_receipt_v1(witness, accepted, mutated, prior, ())
    assert isinstance(reject, ReceiptBackedProducerRejectedV1)
    assert reject.code is code
    assert reject.committed_lane_root == mutated.state_root


def test_witness_reject_family_is_closed_and_ordered() -> None:
    assert [code.name for code in ReceiptWitnessRejectCodeV1] == [
        "WITNESS_KIND_DRIFT",
        "WITNESS_JOURNAL_ROOT_DRIFT",
        "WITNESS_STATEMENT_ROOT_DRIFT",
        "WITNESS_OCCURRENCE_DRIFT",
        "WITNESS_BINDING_ROOT_DRIFT",
    ]
    assert all(code.value == code.name for code in ReceiptWitnessRejectCodeV1)


def test_witness_reject_is_a_no_op_value() -> None:
    accepted, witness, lane_root, prior = _admission_fixture()
    before = accepted.module_journal.journal_root
    foreign_accepted, _w, _r, _p = _fixture(authority_epoch=8)
    verify_asset_transfer_fragment_receipt_v1(witness, foreign_accepted, lane_root, prior, ())
    assert accepted.module_journal.journal_root == before
    assert witness.module_journal_root == before


def test_claimant_identity_is_not_bound_by_the_receipt_until_c9b() -> None:
    """NONCLAIM PIN (Opus P28 F2): claimant_entitlements are caller-chosen and
    covered only per (asset, control_domain) total. The receipt proves the
    custodian's row, yet an entitlement naming any claimant for the same total
    is admitted. C9b binds claimants at certificate consumption and must
    invert this pin."""

    accepted, witness, lane_root, prior = _fixture(custody=(CUSTODIAN_ROW,))
    for claimant in ("custodian", "attacker"):
        admitted = verify_asset_transfer_fragment_receipt_v1(
            witness,
            accepted,
            lane_root,
            prior,
            (cert.ClaimantEntitlementRowV1("USD", claimant, "vault", 100),),
        )
        assert isinstance(admitted, VerifiedLaneAllocationFragmentV1)
        assert admitted.fragment.claimant_entitlements[0].claimant == claimant
        assert admitted.fragment.controlled_locations == (
            cert.ControlledLocationRowV1("USD", "custodian", "vault", 100),
        )
