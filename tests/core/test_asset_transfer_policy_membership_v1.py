"""Governed typed policy-registry membership for asset transfer.

These tests use a synthetic ACTIVE profile solely to exercise fail-closed
membership through release-route binding and receipt verification. They grant
no release, mount, settlement, or publication authority.

The first test is the minimized negative witness written before the repair: a
state row rewritten from ``treasury/2`` to ``mallory/1`` while both opaque
registry roots stay unchanged used to reach transition acceptance,
release-route binding, and the receipt verifier.

Test Quality Contract V2 obligation record (honest oracle grade 2: fixed
vectors and decision tables; no independent executable model is claimed):

1. Dual governed roots and exact row membership. RIPR reaches accepted transfer
   binding, infects a carried row/root, propagates toward witness construction,
   and reveals exact rejection plus zero verifier calls. Mutants killed:
   ``DROP_ASSET_ROOT_CHECK``, ``DROP_FEE_ROOT_CHECK``, and
   ``DROP_MEMBER_EQUALITY``.
2. Release/profile binding and rotation replay. RIPR splices old authentication
   into coherent new-profile roots and reveals
   ``occurrence profile root mismatch`` before witness/verifier authority.
   Mutants killed: ``DROP_RELEASE_BINDING`` and ``DROP_OCCURRENCE_PROFILE``.
3. Exact snapshots and hostile-type closure. RIPR retains or subclasses an
   input, mutates after capture, and reveals exact-type rejection or stable
   owned values. Mutant killed: ``READ_RETAINED_ALIAS``.
4. Witness/verifier mediation and exactly-once recomputation. RIPR mutates the
   accepted result or call order and reveals zero verifier calls or the exact
   recomputation count. Mutants killed: ``VERIFIER_BEFORE_RECOMPUTE`` and
   ``SKIP_OR_DOUBLE_RECOMPUTE``.
5. Canonical Python/Rust vectors. RIPR changes release, row order, or one policy
   field and reveals a changed fixed root or exact rejection. Mutant killed:
   ``OMIT_RELEASE_FROM_POLICY_ROOT``.

Applicable BVA/history lanes cover empty/one/256/257 registries, amount and fee
neighbors, stale roots, coherent profile rotation, and retained-alias history.
Cancellation, recovery, expiry, terminal settlement, crash/restart, CAS,
outbox, and migration are outside this unmounted pure-core obligation and
remain explicit release gaps. These records grant no release, mount,
settlement, publication, or value-movement authority.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, fields, replace
from types import SimpleNamespace

import pytest

import src.core.asset_transfer_lane_module_v1 as transfer_lane_module
import src.core.lane_module_release_route_binding_v1 as binder_module
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_policy_registry_v1 import (
    ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
    ASSET_TRANSFER_FEE_POLICY_KIND_V1,
    MAX_ASSET_TRANSFER_POLICIES_V1,
    AssetTransferPolicyRegistryV1,
    require_asset_transfer_policy_membership_v1,
    require_governed_asset_transfer_policy_registry_v1,
    snapshot_asset_transfer_policy_registry_v1,
)
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferCommandV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    RouteReleaseV1,
)
from src.core.lane_module_receipt_verification_v1 import (
    AssetTransferLaneModuleReceiptCandidateV1,
    LaneModuleReceiptEnvelopeV1,
    verify_asset_transfer_lane_module_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    AssetTransferReleaseRouteBindingCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
    bind_asset_transfer_lane_output_to_release_route_v1,
)
from src.core.managed_asset_policy_registry_v1 import (
    snapshot_exact_economic_policy_registry_v1,
)
from tests.core import test_lane_module_release_route_binding_v1 as support

_TRANSFER = ASSET_TRANSFER_COMMAND_KIND_V1
_TRANSFER_POLICY_KINDS = (
    ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
    ASSET_TRANSFER_FEE_POLICY_KIND_V1,
)
_MEMBER_MISMATCH = "state policy is not a governed registry member"
_RELEASE_MISMATCH = "asset transfer policy registry module release mismatch"
_ASSET_ROOT_MISMATCH = "lane module asset policy root mismatch"
_FEE_ROOT_MISMATCH = "lane module fee policy root mismatch"
_STRUCTURAL_MISMATCH = "lane module structural binding mismatch"
_OTHER_RELEASE_ID = support._root(997)
# Cross-language vectors: the Rust suites assert the same domain-separated
# roots for the same release-bound registries (USD/treasury/2/enabled row).
_FIXED_RELEASE_ASSET_POLICY_ROOT_V1 = (
    "0xddf8513d14116e9f5ef0060c3d93ea37ea8ae68e831f78d36a16726cdbb6d3f5"
)
_FIXED_RELEASE_FEE_POLICY_ROOT_V1 = (
    "0xb4c242d46f2974c7cea8ca99e54112881631264bdc7e1ba32ee8cb20ece1e62f"
)
_OTHER_RELEASE_ASSET_POLICY_ROOT_V1 = (
    "0x841cd037837f1f6542639456083dd48bab63ac9060ca21da092be93df461a49b"
)
_OTHER_RELEASE_FEE_POLICY_ROOT_V1 = (
    "0xeaacbb1844aa90baaf68c76b8710c0aa4d7f05bd0d174d9bb17186a850a0e907"
)
_FIXTURE_ASSET_POLICY_ROOT_V1 = "0x410c0a5f51ec3b51ee53bf95eae3c11df09004bbe60be9b04a45f106c823fda7"
_FIXTURE_FEE_POLICY_ROOT_V1 = "0xeb173aa23a9cbcb7db7e08d255068789dc081a056cac27f51cafa389b966dbd1"
# The governed transfer profile commits both bindings; the Rust route-binding
# suite asserts the same profile and route release ids.
_GOVERNED_PROFILE_ID_V1 = "0x96b4fff45570fc2da3f522030cc06bb140390a99cb1fba7986a34cb11a9f298c"
_GOVERNED_TRANSFER_ROUTE_RELEASE_ID_V1 = (
    "0x2bba8b7eaf9df0e6d28b0f27933995a1872be2c41fed5a7b5ea0ee3f8ba01b1d"
)
_InputEdit = Callable[[AssetTransferLaneModuleInputV1], AssetTransferLaneModuleInputV1]


def _root(value: int) -> str:
    return support._root(value)


def _policy(
    *,
    asset: str = "USD",
    fee_owner: str = "treasury",
    transfer_fee_atoms: int = 2,
    enabled: bool = True,
) -> AssetTransferPolicyV1:
    return AssetTransferPolicyV1(asset, fee_owner, transfer_fee_atoms, enabled)


def _registry(
    policies: tuple[AssetTransferPolicyV1, ...],
    *,
    module_release_id: str | None = None,
) -> AssetTransferPolicyRegistryV1:
    return AssetTransferPolicyRegistryV1(
        support._asset_transfer_release_id_v1() if module_release_id is None else module_release_id,
        policies,
    )


def _command(
    *,
    asset: str = "USD",
    sender: str = "alice",
    recipient: str = "bob",
    amount_atoms: int = 30,
    max_fee_atoms: int = 2,
) -> AssetTransferCommandV1:
    return AssetTransferCommandV1(
        _TRANSFER,
        asset,
        sender,
        recipient,
        amount_atoms,
        max_fee_atoms,
    )


def _occurrence_for(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    command: AssetTransferCommandV1,
) -> EconomicCommandOccurrenceV1:
    """Occurrence whose body hash is the exact canonical command payload."""

    return EconomicCommandOccurrenceV1(
        chain_id="zeno-release-route-test",
        deployment_root=_root(1),
        height=11,
        tx_index=2,
        op_index=3,
        command_kind=route.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=route.route_release_id,
        subject_id=command.sender,
        grant_root=_root(7),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=_root(2),
        consumed_object_ids=(),
    )


@dataclass(frozen=True, slots=True)
class _Executed:
    occurrence: EconomicCommandOccurrenceV1
    module_input: AssetTransferLaneModuleInputV1
    accepted: AssetTransferLaneModuleAcceptedV1


def _execute(
    governance: support._TransferGovernanceV1,
    *,
    edit: _InputEdit | None = None,
    input_registry: AssetTransferPolicyRegistryV1 | None = None,
) -> _Executed:
    """Execute one accepted transfer under the given governance.

    ``input_registry`` selects the rows and roots the lane input carries; it
    defaults to the governed registry so the honest path is exact.
    """

    occurrence = support._occurrence(
        governance.profile,
        governance.routes[_TRANSFER],
        subject_id="alice",
        grant_root=_root(7),
    )
    module_input = support._asset_input(
        governance.profile,
        occurrence,
        asset_policy_registry=(
            governance.asset_policy_registry if input_registry is None else input_registry
        ),
    )
    if edit is not None:
        module_input = edit(module_input)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    return _Executed(occurrence, module_input, accepted)


def _execute_command(
    governance: support._TransferGovernanceV1,
    command: AssetTransferCommandV1,
    *,
    balances: tuple[EconomicAmountV1, ...],
    supplies: tuple[AssetSupplyV1, ...],
) -> _Executed:
    """Execute one transfer of an arbitrary governed command and pre-state."""

    profile = governance.profile
    occurrence = _occurrence_for(profile, governance.routes[_TRANSFER], command)
    base = support._asset_input(
        profile,
        occurrence,
        asset_policy_registry=governance.asset_policy_registry,
    )
    module_input = replace(
        base,
        pre_state=AssetTransferStateV1(
            module_release_id=base.pre_state.module_release_id,
            policies=governance.asset_policy_registry.policies,
            balances=balances,
            supplies=supplies,
        ),
        command=command,
    )
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    return _Executed(occurrence, module_input, accepted)


def _bind(
    governance: support._TransferGovernanceV1,
    executed: _Executed,
) -> ReleaseRouteBoundLaneTransitionV1:
    return bind_asset_transfer_lane_output_to_release_route_v1(
        support._transfer_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
    )


def _with_state_policy(policy: AssetTransferPolicyV1) -> _InputEdit:
    def edit(module_input: AssetTransferLaneModuleInputV1) -> AssetTransferLaneModuleInputV1:
        return replace(
            module_input,
            pre_state=replace(module_input.pre_state, policies=(policy,)),
        )

    return edit


def _with_ungoverned_eur(command_asset: str) -> _InputEdit:
    eur = _policy(asset="EUR")

    def edit(module_input: AssetTransferLaneModuleInputV1) -> AssetTransferLaneModuleInputV1:
        return replace(
            module_input,
            pre_state=replace(
                module_input.pre_state,
                policies=(eur, _policy()),
                balances=(
                    EconomicAmountV1("alice", "EUR", "accounts", 100),
                    *module_input.pre_state.balances,
                ),
                supplies=(AssetSupplyV1("EUR", 100), AssetSupplyV1("USD", 115)),
            ),
            command=replace(module_input.command, asset=command_asset),
        )

    return edit


def _under_module_release(
    module_release_id: str,
    *,
    asset_policy_registry_root: str | None = None,
    fee_policy_registry_root: str | None = None,
) -> _InputEdit:
    """Execute the same command and policy rows under another module release."""

    def edit(module_input: AssetTransferLaneModuleInputV1) -> AssetTransferLaneModuleInputV1:
        edited = replace(
            module_input,
            context=replace(module_input.context, module_release_id=module_release_id),
            pre_state=replace(module_input.pre_state, module_release_id=module_release_id),
        )
        if asset_policy_registry_root is not None:
            edited = replace(edited, asset_policy_registry_root=asset_policy_registry_root)
        if fee_policy_registry_root is not None:
            edited = replace(edited, fee_policy_registry_root=fee_policy_registry_root)
        return edited

    return edit


def _with_roots(asset_root: str, fee_root: str) -> _InputEdit:
    def edit(module_input: AssetTransferLaneModuleInputV1) -> AssetTransferLaneModuleInputV1:
        return replace(
            module_input,
            asset_policy_registry_root=asset_root,
            fee_policy_registry_root=fee_root,
        )

    return edit


def _profile_with_policy_registry(
    template: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
) -> EconomicProfileSnapshotV1:
    return EconomicProfileSnapshotV1.build(
        authority_epoch=template.authority_epoch,
        lane_registry=template.lane_registry,
        lane_coordinator_registry=template.lane_coordinator_registry,
        route_registry=template.route_registry,
        proof_shape_root=template.proof_shape_root,
        root_image_id=template.root_image_id,
        verifier_registry_root=template.verifier_registry_root,
        migration_registry_root=template.migration_registry_root,
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=template.terminal_registry_root,
        status=template.status,
    )


def _structurally_rebind_transfer_statement(
    accepted: AssetTransferLaneModuleAcceptedV1,
    statement_root: str,
) -> AssetTransferLaneModuleAcceptedV1:
    receipt_root = support.hash_global_v1(
        "asset-transfer-lane-module-receipt-v1",
        {
            "statement_root": statement_root,
            "pre_state_root": accepted.module_journal.pre_lane_root,
            "post_state_root": accepted.module_journal.post_lane_root,
            "effect_plan_root": accepted.effects.effect_plan_root,
            "private_port_root": accepted.private_port.port_root,
            "terminal_obligations_root": accepted.private_port.terminal_obligations_root,
        },
    )
    return replace(
        accepted,
        statement_root=statement_root,
        module_journal=replace(accepted.module_journal, receipt_root=receipt_root),
    )


def test_fee_policy_substitution_rejects_before_any_witness_or_verifier() -> None:
    # Arrange: the governed row is treasury/2; Mallory executes under mallory/1
    # while retaining both opaque registry roots and the authenticated command.
    governance = support._transfer_governance_v1()
    honest = _execute(governance)
    executed = _execute(
        governance, edit=_with_state_policy(_policy(fee_owner="mallory", transfer_fee_atoms=1))
    )
    assert executed.accepted.post_state.balance_atoms("mallory", "USD") == 1
    assert executed.module_input.asset_policy_registry_root == (
        honest.module_input.asset_policy_registry_root
    )
    assert executed.module_input.fee_policy_registry_root == (
        honest.module_input.fee_policy_registry_root
    )
    honest_witness = _bind(governance, honest)
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert: release-route binding rejects the ungoverned fee policy
    # before any structural witness exists, and the retained honest witness
    # cannot carry the substituted output to the verifier.
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        _bind(governance, executed)
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        verify_asset_transfer_lane_module_receipt_v1(
            support._transfer_receipt_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                executed.accepted,
                honest_witness,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"mallory-fee-policy"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_registry_roots_are_content_derived_domain_separated_and_lookup_is_exact() -> None:
    # Arrange
    registry = support._asset_transfer_policy_registry_v1()
    rebuilt = _registry(tuple(replace(policy) for policy in registry.policies))
    disabled = _registry((replace(registry.policies[0], enabled=False),))
    repriced = _registry((replace(registry.policies[0], transfer_fee_atoms=1),))
    reowned = _registry((replace(registry.policies[0], fee_owner="mallory"),))

    # Act / Assert: each root commits exactly its projected columns.
    assert registry.asset_policy_root == rebuilt.asset_policy_root
    assert registry.fee_policy_root == rebuilt.fee_policy_root
    assert registry.asset_policy_root != registry.fee_policy_root
    assert disabled.asset_policy_root != registry.asset_policy_root
    assert disabled.fee_policy_root == registry.fee_policy_root
    assert repriced.asset_policy_root == registry.asset_policy_root
    assert repriced.fee_policy_root != registry.fee_policy_root
    assert reowned.asset_policy_root == registry.asset_policy_root
    assert reowned.fee_policy_root != registry.fee_policy_root
    assert len({repriced.fee_policy_root, reowned.fee_policy_root, registry.fee_policy_root}) == 3
    assert registry.policy_for("USD") == _policy()
    assert registry.policy_for("EUR") is None
    with pytest.raises(ValueError, match="must not be empty"):
        registry.policy_for("")


def test_registry_roots_bind_the_module_release_with_cross_language_vectors() -> None:
    # Arrange: identical policy rows under three module releases.
    rows = (_policy(),)
    fixed = _registry(rows, module_release_id=_root(3))
    other = _registry(rows, module_release_id=_OTHER_RELEASE_ID)
    fixture = support._asset_transfer_policy_registry_v1()

    # Act / Assert: the release is part of both roots, so rows cannot be replayed.
    assert fixed.asset_policy_root == _FIXED_RELEASE_ASSET_POLICY_ROOT_V1
    assert fixed.fee_policy_root == _FIXED_RELEASE_FEE_POLICY_ROOT_V1
    assert other.asset_policy_root == _OTHER_RELEASE_ASSET_POLICY_ROOT_V1
    assert other.fee_policy_root == _OTHER_RELEASE_FEE_POLICY_ROOT_V1
    assert fixture.asset_policy_root == _FIXTURE_ASSET_POLICY_ROOT_V1
    assert fixture.fee_policy_root == _FIXTURE_FEE_POLICY_ROOT_V1
    assert fixture.module_release_id == support._asset_transfer_release_id_v1()
    assert fixed.policies == other.policies == fixture.policies
    assert len({fixed.asset_policy_root, other.asset_policy_root, fixture.asset_policy_root}) == 3
    assert len({fixed.fee_policy_root, other.fee_policy_root, fixture.fee_policy_root}) == 3


def test_registry_rejects_zero_malformed_and_untyped_module_release() -> None:
    rows = (_policy(),)

    with pytest.raises(ValueError, match="module release must be nonzero"):
        AssetTransferPolicyRegistryV1(ZERO_ROOT_V1, rows)
    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed"):
        AssetTransferPolicyRegistryV1("0x12", rows)
    with pytest.raises(TypeError, match="module release must be a string"):
        AssetTransferPolicyRegistryV1(3, rows)  # type: ignore[arg-type]


def test_registry_rejects_unsorted_duplicate_and_untyped_members() -> None:
    usd = _policy()
    eur = _policy(asset="EUR")

    with pytest.raises(ValueError, match="canonically ordered and unique"):
        _registry((usd, eur))
    with pytest.raises(ValueError, match="canonically ordered and unique"):
        _registry((usd, usd))
    with pytest.raises(ValueError, match="canonically ordered and unique"):
        _registry((usd, replace(usd, fee_owner="mallory")))
    with pytest.raises(TypeError, match="contains an invalid value"):
        _registry((usd, object()))
    with pytest.raises(TypeError, match="must be a tuple"):
        _registry([usd])  # type: ignore[arg-type]
    assert _registry((eur, usd)).policies == (eur, usd)


def test_registry_cardinality_bva_accepts_bound_and_rejects_one_over() -> None:
    def policies(count: int) -> tuple[AssetTransferPolicyV1, ...]:
        return tuple(_policy(asset=f"A{index:03d}") for index in range(count))

    empty = _registry(())
    single = _registry(policies(1))
    at_limit = _registry(policies(MAX_ASSET_TRANSFER_POLICIES_V1))

    assert empty.policy_for("A000") is None
    assert single.policy_for("A000") == _policy(asset="A000")
    assert len(at_limit.policies) == MAX_ASSET_TRANSFER_POLICIES_V1 == 256
    assert at_limit.asset_policy_root != single.asset_policy_root
    with pytest.raises(ValueError, match="exceeds the ABI V1 bound"):
        _registry(policies(MAX_ASSET_TRANSFER_POLICIES_V1 + 1))
    with pytest.raises(ValueError, match="exceeds the ABI V1 bound"):
        _registry(tuple(reversed(policies(MAX_ASSET_TRANSFER_POLICIES_V1 + 1))))


def test_governed_member_binds_and_verifies_through_receipt() -> None:
    # Arrange
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    verifier = support._RecordingModuleReceiptVerifier()

    # Act
    bound = _bind(governance, executed)
    verified = verify_asset_transfer_lane_module_receipt_v1(
        support._transfer_receipt_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"governed-transfer-receipt"),
        ),
        verifier,
    )

    # Assert: both opaque roots are the typed registry roots, the registry is
    # bound to the executing release, and the profile commits both bindings.
    registry = governance.asset_policy_registry
    assert executed.module_input.asset_policy_registry_root == registry.asset_policy_root
    assert executed.module_input.fee_policy_registry_root == registry.fee_policy_root
    assert executed.module_input.context.module_release_id == registry.module_release_id
    assert governance.policy_registry.registry_root == governance.profile.policy_registry_root
    for policy_kind, root in (
        (ASSET_TRANSFER_ASSET_POLICY_KIND_V1, registry.asset_policy_root),
        (ASSET_TRANSFER_FEE_POLICY_KIND_V1, registry.fee_policy_root),
    ):
        binding = governance.policy_registry.require_binding(
            policy_kind=policy_kind,
            command_kind=_TRANSFER,
        )
        assert binding.policy_root == root
    assert bound.statement_root == executed.module_input.statement_root
    assert bound.route_release_id == _GOVERNED_TRANSFER_ROUTE_RELEASE_ID_V1
    assert governance.profile.profile_id == _GOVERNED_PROFILE_ID_V1
    assert verified.release_route_binding_root == bound.binding_root
    assert len(verifier.calls) == 1


def test_membership_returns_an_owned_exact_governed_member() -> None:
    # Arrange
    governance = support._transfer_governance_v1()
    executed = _execute(governance)

    # Act
    member = require_asset_transfer_policy_membership_v1(
        asset_policy_registry=governance.asset_policy_registry,
        module_input=executed.module_input,
    )

    # Assert
    assert member == _policy()
    assert member is not governance.asset_policy_registry.policies[0]


@pytest.mark.parametrize(
    ("edit", "message"),
    (
        (_with_roots(_root(11), _FIXTURE_FEE_POLICY_ROOT_V1), _ASSET_ROOT_MISMATCH),
        (_with_roots(_FIXTURE_ASSET_POLICY_ROOT_V1, _root(12)), _FEE_ROOT_MISMATCH),
        (
            _with_roots(_FIXTURE_FEE_POLICY_ROOT_V1, _FIXTURE_ASSET_POLICY_ROOT_V1),
            _ASSET_ROOT_MISMATCH,
        ),
    ),
)
def test_direct_transition_stays_authority_free_and_binding_pins_both_roots(
    edit: _InputEdit,
    message: str,
) -> None:
    # Arrange: the lane statement carries ungoverned or swapped opaque roots.
    governance = support._transfer_governance_v1()
    executed = _execute(governance, edit=edit)

    # Act / Assert: the direct transition accepted without consulting any
    # registry; only release-route binding pins both typed registry roots.
    projected = executed.accepted.private_port.pre_state
    assert projected.asset_policy_registry_root == executed.module_input.asset_policy_registry_root
    assert projected.fee_policy_registry_root == executed.module_input.fee_policy_registry_root
    with pytest.raises(ValueError, match=message):
        _bind(governance, executed)


def test_policy_registry_outside_the_profile_rejects_before_route_binding() -> None:
    # Arrange: drop the transfer bindings so the registry root leaves the profile.
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    ungoverned = EconomicPolicyRegistryV1(
        tuple(
            binding
            for binding in governance.policy_registry.bindings
            if binding.policy_kind not in _TRANSFER_POLICY_KINDS
        )
    )
    candidate = replace(
        support._transfer_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        ),
        policy_registry=ungoverned,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="policy registry is outside the profile"):
        bind_asset_transfer_lane_output_to_release_route_v1(candidate)


@pytest.mark.parametrize("retained_kind", _TRANSFER_POLICY_KINDS)
def test_omitting_either_binding_rejects_before_any_witness(retained_kind: str) -> None:
    # Arrange: the profile governs only one of the two transfer policy kinds; a
    # witness minted under the fully governed profile is retained.
    governance = support._transfer_governance_v1(transfer_policy_kinds=(retained_kind,))
    executed = _execute(governance)
    fully_governed = support._transfer_governance_v1()
    retained_witness = _bind(fully_governed, _execute(fully_governed))
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert: one binding is never enough.
    with pytest.raises(ValueError, match="binding is absent from the governed registry"):
        _bind(governance, executed)
    with pytest.raises(ValueError, match="binding is absent from the governed registry"):
        verify_asset_transfer_lane_module_receipt_v1(
            support._transfer_receipt_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                executed.accepted,
                retained_witness,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"one-binding"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_swapped_asset_and_fee_roots_reject_at_governed_binding() -> None:
    # Arrange: a profile whose asset binding carries the fee root and whose fee
    # binding carries the asset root of the same typed registry.
    governance = support._transfer_governance_v1()
    registry = governance.asset_policy_registry
    swapped_roots = {
        ASSET_TRANSFER_ASSET_POLICY_KIND_V1: registry.fee_policy_root,
        ASSET_TRANSFER_FEE_POLICY_KIND_V1: registry.asset_policy_root,
    }
    swapped_registry = EconomicPolicyRegistryV1(
        tuple(
            replace(binding, policy_root=swapped_roots[binding.policy_kind])
            if binding.policy_kind in swapped_roots
            else binding
            for binding in governance.policy_registry.bindings
        )
    )
    swapped_profile = _profile_with_policy_registry(governance.profile, swapped_registry)
    route = swapped_profile.route_registry.route_for_command(_TRANSFER)
    occurrence = _occurrence_for(swapped_profile, route, _command())
    module_input = support._asset_input(swapped_profile, occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    assert swapped_registry.registry_root == swapped_profile.policy_registry_root

    # Act / Assert: domain separation makes the swap observable.
    with pytest.raises(ValueError, match="asset transfer asset policy root mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            AssetTransferReleaseRouteBindingCandidateV1(
                swapped_profile,
                swapped_registry,
                registry,
                occurrence,
                module_input,
                accepted,
            )
        )
    with pytest.raises(ValueError, match="asset transfer asset policy root mismatch"):
        require_governed_asset_transfer_policy_registry_v1(
            profile=swapped_profile,
            policy_registry=swapped_registry,
            occurrence=occurrence,
            asset_policy_registry=registry,
        )


def test_governed_binding_requires_the_transfer_command_kind() -> None:
    governance = support._transfer_governance_v1()
    executed = _execute(governance)

    with pytest.raises(ValueError, match="requires an asset transfer command"):
        require_governed_asset_transfer_policy_registry_v1(
            profile=governance.profile,
            policy_registry=governance.policy_registry,
            occurrence=replace(executed.occurrence, command_kind="managed_asset_issue"),
            asset_policy_registry=governance.asset_policy_registry,
        )


def test_same_policy_rows_under_another_module_release_reject_at_membership() -> None:
    # Arrange: the module executes the governed rows under a foreign release while
    # advertising both governed registry roots.
    governance = support._transfer_governance_v1()
    executed = _execute(governance, edit=_under_module_release(_OTHER_RELEASE_ID))

    # Act / Assert
    registry = governance.asset_policy_registry
    assert executed.module_input.asset_policy_registry_root == registry.asset_policy_root
    assert executed.module_input.fee_policy_registry_root == registry.fee_policy_root
    with pytest.raises(ValueError, match=_RELEASE_MISMATCH):
        _bind(governance, executed)


def test_registry_bound_to_another_release_rejects_at_governed_binding() -> None:
    # Arrange: the profile governs rows bound to a foreign release; the module runs
    # under the active release and advertises that governed registry's roots.
    governance = support._transfer_governance_v1(
        asset_policy_registry=support._asset_transfer_policy_registry_v1(_OTHER_RELEASE_ID)
    )
    executed = _execute(governance)
    registry = governance.asset_policy_registry
    assert executed.module_input.asset_policy_registry_root == registry.asset_policy_root

    # Act / Assert: the registry release is not the profile-selected release.
    with pytest.raises(ValueError, match="not the profile-selected release"):
        _bind(governance, executed)
    with pytest.raises(ValueError, match=_RELEASE_MISMATCH):
        require_asset_transfer_policy_membership_v1(
            asset_policy_registry=registry,
            module_input=executed.module_input,
        )


def test_route_release_check_remains_independent_of_registry_membership() -> None:
    # Arrange: rows, registry, context, and pre-state all agree on a foreign release
    # that the governed lane registry does not carry.
    governance = support._transfer_governance_v1(
        asset_policy_registry=support._asset_transfer_policy_registry_v1(_OTHER_RELEASE_ID)
    )
    executed = _execute(governance, edit=_under_module_release(_OTHER_RELEASE_ID))

    # Act / Assert: membership passes on its own and governed binding still
    # fails closed on the profile-selected release.
    assert (
        require_asset_transfer_policy_membership_v1(
            asset_policy_registry=governance.asset_policy_registry,
            module_input=executed.module_input,
        )
        == _policy()
    )
    with pytest.raises(ValueError, match="not the profile-selected release"):
        _bind(governance, executed)


@pytest.mark.parametrize(
    "rogue",
    (
        _policy(fee_owner="mallory"),
        _policy(transfer_fee_atoms=1),
        _policy(fee_owner="mallory", transfer_fee_atoms=1),
        _policy(transfer_fee_atoms=0),
    ),
)
def test_fee_owner_and_fee_atoms_state_mutations_reject_at_membership(
    rogue: AssetTransferPolicyV1,
) -> None:
    # Arrange: the executed state row differs from the governed member in one
    # fee column while both opaque roots stay governed.
    governance = support._transfer_governance_v1()
    executed = _execute(governance, edit=_with_state_policy(rogue))

    # Act / Assert: the module accepted, governed membership does not.
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        _bind(governance, executed)
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        require_asset_transfer_policy_membership_v1(
            asset_policy_registry=governance.asset_policy_registry,
            module_input=executed.module_input,
        )


def test_enablement_mutation_rejects_at_membership() -> None:
    # Arrange: governance disabled USD; the module executes an enabled row while
    # advertising the disabled registry's roots.
    governance = support._transfer_governance_v1(
        asset_policy_registry=_registry((_policy(enabled=False),))
    )
    executed = _execute(governance, edit=_with_state_policy(_policy(enabled=True)))
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        _bind(governance, executed)
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        verify_asset_transfer_lane_module_receipt_v1(
            support._transfer_receipt_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                executed.accepted,
                _bind(
                    support._transfer_governance_v1(), _execute(support._transfer_governance_v1())
                ),
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"disabled-member"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_disabled_governed_member_admits_no_transfer() -> None:
    # Arrange: governance disabled USD and the state row agrees.
    governance = support._transfer_governance_v1(
        asset_policy_registry=_registry((_policy(enabled=False),))
    )
    occurrence = support._occurrence(
        governance.profile,
        governance.routes[_TRANSFER],
        subject_id="alice",
        grant_root=_root(7),
    )
    module_input = _with_state_policy(_policy(enabled=False))(
        support._asset_input(
            governance.profile,
            occurrence,
            asset_policy_registry=governance.asset_policy_registry,
        )
    )

    # Act / Assert: membership is exact and the transition rejects as a no-op.
    assert require_asset_transfer_policy_membership_v1(
        asset_policy_registry=governance.asset_policy_registry,
        module_input=module_input,
    ) == _policy(enabled=False)
    result = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code is AssetTransferRejectCodeV1.DISABLED_ASSET
    assert result.post_state_root == module_input.pre_state.state_root


def test_command_asset_absent_from_the_governed_registry_rejects() -> None:
    # Arrange: the state carries an ungoverned EUR row and the command moves EUR.
    governance = support._transfer_governance_v1()
    executed = _execute(governance, edit=_with_ungoverned_eur("EUR"))

    # Act / Assert
    with pytest.raises(ValueError, match="absent from the governed policy registry"):
        _bind(governance, executed)


def test_state_carrying_an_ungoverned_extra_policy_rejects() -> None:
    # Arrange: the command targets the governed USD member, the state also carries EUR.
    governance = support._transfer_governance_v1()
    executed = _execute(governance, edit=_with_ungoverned_eur("USD"))

    # Act / Assert
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        _bind(governance, executed)


def test_state_omitting_the_governed_command_policy_rejects_at_membership() -> None:
    # Arrange: the registry governs USD, the pre-state carries no USD row.
    governance = support._transfer_governance_v1()
    occurrence = support._occurrence(
        governance.profile,
        governance.routes[_TRANSFER],
        subject_id="alice",
        grant_root=_root(7),
    )
    base = support._asset_input(
        governance.profile,
        occurrence,
        asset_policy_registry=governance.asset_policy_registry,
    )
    omitted = replace(
        base,
        pre_state=AssetTransferStateV1(base.pre_state.module_release_id, (), (), ()),
    )

    # Act / Assert: membership rejects before any transition consultation, and
    # the direct transition cannot accept such a state either.
    with pytest.raises(ValueError, match="state omits the governed command policy"):
        require_asset_transfer_policy_membership_v1(
            asset_policy_registry=governance.asset_policy_registry,
            module_input=omitted,
        )
    result = transition_asset_transfer_lane_module_v1(omitted)
    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code is AssetTransferRejectCodeV1.UNKNOWN_ASSET


def test_empty_governed_registry_rejects_every_asset() -> None:
    # Arrange: governance commits an empty registry; the module still executes
    # its own USD row while advertising the empty registry's roots.
    empty = _registry(())
    governance = support._transfer_governance_v1(asset_policy_registry=empty)
    executed = _execute(
        governance,
        input_registry=support._asset_transfer_policy_registry_v1(),
        edit=_with_roots(empty.asset_policy_root, empty.fee_policy_root),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="absent from the governed policy registry"):
        _bind(governance, executed)


@pytest.mark.parametrize(
    ("rotated", "message"),
    (
        (_policy(fee_owner="vault"), _FEE_ROOT_MISMATCH),
        (_policy(transfer_fee_atoms=3), _FEE_ROOT_MISMATCH),
        (_policy(enabled=False), _ASSET_ROOT_MISMATCH),
    ),
)
def test_stale_roots_after_policy_rotation_reject_before_any_witness(
    rotated: AssetTransferPolicyV1,
    message: str,
) -> None:
    # Arrange: governance rotated one policy column; an output executed under the
    # old registry roots is presented to the rotated profile.
    old = support._transfer_governance_v1()
    executed = _execute(old)
    old_witness = _bind(old, executed)
    new = support._transfer_governance_v1(asset_policy_registry=_registry((rotated,)))
    assert new.profile.profile_id != old.profile.profile_id
    candidate = AssetTransferReleaseRouteBindingCandidateV1(
        new.profile,
        new.policy_registry,
        new.asset_policy_registry,
        executed.occurrence,
        executed.module_input,
        executed.accepted,
    )
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert: the stale roots reject at membership, before the old
    # witness, old occurrence, or any receipt bytes are compared.
    with pytest.raises(ValueError, match=message):
        bind_asset_transfer_lane_output_to_release_route_v1(candidate)
    with pytest.raises(ValueError, match=message):
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1(
                new.profile,
                new.policy_registry,
                new.asset_policy_registry,
                support._authenticate_occurrence_for_test(
                    old.profile,
                    executed.occurrence,
                    executed.module_input.command,
                    policy_registry=old.policy_registry,
                ),
                executed.module_input,
                executed.accepted,
                old_witness,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"stale-roots"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_old_profile_authentication_with_coherent_rotated_policy_rejects_before_witness_or_verifier() -> (
    None
):
    # Arrange: P1 coherently owns the rotated fee policy, roots, input and
    # accepted output. Mallory splices P0's authenticated occurrence ID into
    # that P1 context while retaining the P0 occurrence and witness.
    old = support._transfer_governance_v1()
    old_executed = _execute(old)
    old_witness = _bind(old, old_executed)
    old_authenticated = support._authenticate_occurrence_for_test(
        old.profile,
        old_executed.occurrence,
        old_executed.module_input.command,
        policy_registry=old.policy_registry,
    )
    new = support._transfer_governance_v1(
        asset_policy_registry=_registry((_policy(fee_owner="vault"),))
    )
    new_executed = _execute(new)
    spliced_input = replace(
        new_executed.module_input,
        context=replace(
            new_executed.module_input.context,
            command_occurrence_id=old_executed.occurrence.occurrence_id,
        ),
    )
    spliced_accepted = transition_asset_transfer_lane_module_v1(spliced_input)
    assert isinstance(spliced_accepted, AssetTransferLaneModuleAcceptedV1)
    binding_candidate = AssetTransferReleaseRouteBindingCandidateV1(
        new.profile,
        new.policy_registry,
        new.asset_policy_registry,
        old_executed.occurrence,
        spliced_input,
        spliced_accepted,
    )
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="occurrence profile root mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(binding_candidate)
    with pytest.raises(ValueError, match="occurrence profile root mismatch"):
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1(
                new.profile,
                new.policy_registry,
                new.asset_policy_registry,
                old_authenticated,
                spliced_input,
                spliced_accepted,
                old_witness,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"p0-auth-p1-policy"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_old_witness_cannot_carry_a_rotated_profile_receipt() -> None:
    # Arrange: an honest output under the rotated profile with a witness minted
    # under the old profile.
    old = support._transfer_governance_v1()
    old_witness = _bind(old, _execute(old))
    new = support._transfer_governance_v1(
        asset_policy_registry=_registry((_policy(fee_owner="vault"),))
    )
    executed = _execute(new)
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert: the rebound witness differs, and the verifier is never reached.
    with pytest.raises(ValueError, match=_STRUCTURAL_MISMATCH):
        verify_asset_transfer_lane_module_receipt_v1(
            support._transfer_receipt_candidate(
                new,
                executed.occurrence,
                executed.module_input,
                executed.accepted,
                old_witness,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"old-witness"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_hostile_registry_and_member_subclasses_cannot_advertise_the_governed_roots() -> None:
    # Arrange
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    governed = governance.asset_policy_registry
    rogue_member = _policy(fee_owner="mallory", transfer_fee_atoms=1)

    class AdvertisingRegistry(AssetTransferPolicyRegistryV1):
        @property
        def asset_policy_root(self) -> str:
            return governed.asset_policy_root

        @property
        def fee_policy_root(self) -> str:
            return governed.fee_policy_root

    hook_calls: list[str] = []

    class MimickingPolicy(AssetTransferPolicyV1):
        def to_canonical(self) -> dict[str, object]:
            hook_calls.append("to_canonical")
            return _policy().to_canonical()

    advertising = AdvertisingRegistry(governed.module_release_id, (rogue_member,))
    mimicking_policy = MimickingPolicy(
        rogue_member.asset,
        rogue_member.fee_owner,
        rogue_member.transfer_fee_atoms,
        rogue_member.enabled,
    )
    with pytest.raises(TypeError, match="policies contains an invalid value"):
        _registry((mimicking_policy,))
    assert hook_calls == []

    mimicking = _registry((rogue_member,))
    object.__setattr__(mimicking, "policies", (mimicking_policy,))
    assert advertising.asset_policy_root == governed.asset_policy_root
    assert advertising.fee_policy_root == governed.fee_policy_root

    # Act / Assert: neither constructor admission nor point-of-use revalidation
    # executes the hostile member's canonical projection.
    with pytest.raises(TypeError, match="requires exact typed inputs"):
        AssetTransferReleaseRouteBindingCandidateV1(
            governance.profile,
            governance.policy_registry,
            advertising,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
    with pytest.raises(TypeError, match="registry type is not closed"):
        require_governed_asset_transfer_policy_registry_v1(
            profile=governance.profile,
            policy_registry=governance.policy_registry,
            occurrence=executed.occurrence,
            asset_policy_registry=advertising,
        )
    with pytest.raises(TypeError, match="must contain exact typed values"):
        snapshot_asset_transfer_policy_registry_v1(mimicking)
    with pytest.raises(TypeError, match="must contain exact typed values"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            replace(
                support._transfer_binding_candidate(
                    governance,
                    executed.occurrence,
                    executed.module_input,
                    executed.accepted,
                ),
                asset_policy_registry=mimicking,
            )
        )
    assert hook_calls == []


def test_hostile_text_bool_and_int_scalars_reject_before_membership() -> None:
    # Arrange: exact-type guards on every economic scalar of a policy row.
    class MimickingOwner(str):
        def __eq__(self, other: object) -> bool:
            return True

        __hash__ = str.__hash__

    class MimickingFee(int):
        def __eq__(self, other: object) -> bool:
            return True

        __hash__ = int.__hash__

    class MimickingRoot(str):
        def __eq__(self, other: object) -> bool:
            return other != ZERO_ROOT_V1

        def __ne__(self, other: object) -> bool:
            return not self.__eq__(other)

        __hash__ = str.__hash__

    with pytest.raises(TypeError, match="fee owner must be a string"):
        AssetTransferPolicyV1("USD", MimickingOwner("mallory"), 2, True)
    with pytest.raises(TypeError, match="module release must be a string"):
        AssetTransferPolicyRegistryV1(
            MimickingRoot(support._asset_transfer_release_id_v1()),
            (_policy(),),
        )

    hostile_owner_policy = AssetTransferPolicyV1("USD", "treasury", 2, True)
    object.__setattr__(hostile_owner_policy, "fee_owner", MimickingOwner("mallory"))
    hostile_owner = _registry((hostile_owner_policy,))
    hostile_release = AssetTransferPolicyRegistryV1(
        support._asset_transfer_release_id_v1(),
        (_policy(),),
    )
    object.__setattr__(
        hostile_release,
        "module_release_id",
        MimickingRoot(support._asset_transfer_release_id_v1()),
    )

    # Act / Assert
    with pytest.raises(TypeError, match="must be an exact primitive"):
        snapshot_asset_transfer_policy_registry_v1(hostile_owner)
    with pytest.raises(ValueError, match="must be a non-negative integer"):
        AssetTransferPolicyV1("USD", "treasury", MimickingFee(1), True)
    with pytest.raises(TypeError, match="must be bool"):
        AssetTransferPolicyV1("USD", "treasury", 2, 1)
    with pytest.raises(TypeError, match="module release must be exact text"):
        snapshot_asset_transfer_policy_registry_v1(hostile_release)


def test_binding_and_receipt_candidates_reject_untyped_registries() -> None:
    # Arrange
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    bound = _bind(governance, executed)
    authenticated = support._authenticate_occurrence_for_test(
        governance.profile,
        executed.occurrence,
        executed.module_input.command,
        policy_registry=governance.policy_registry,
    )

    # Act / Assert
    with pytest.raises(TypeError, match="route candidate must have the exact type"):
        bind_asset_transfer_lane_output_to_release_route_v1(object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="requires exact typed inputs"):
        AssetTransferReleaseRouteBindingCandidateV1(
            governance.profile,
            object(),
            governance.asset_policy_registry,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
    with pytest.raises(TypeError, match="asset transfer policy registry must be typed"):
        AssetTransferLaneModuleReceiptCandidateV1(
            governance.profile,
            governance.policy_registry,
            object(),  # type: ignore[arg-type]
            authenticated,
            executed.module_input,
            executed.accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"untyped"),
        )
    with pytest.raises(TypeError, match="economic policy registry must be typed"):
        AssetTransferLaneModuleReceiptCandidateV1(
            governance.profile,
            object(),
            governance.asset_policy_registry,
            authenticated,
            executed.module_input,
            executed.accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"untyped"),
        )


def test_receipt_candidate_registry_substitution_never_reaches_the_verifier() -> None:
    # Arrange: retain a valid receipt candidate, then swap its typed registry.
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    bound = _bind(governance, executed)
    candidate = support._transfer_receipt_candidate(
        governance,
        executed.occurrence,
        executed.module_input,
        executed.accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"substituted-registry"),
    )
    object.__setattr__(
        candidate, "asset_policy_registry", _registry((_policy(transfer_fee_atoms=1),))
    )
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="asset transfer fee policy root mismatch"):
        verify_asset_transfer_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_receipt_structural_binding_rejects_coherent_foreign_output_first() -> None:
    # Arrange: retain the honest witness while supplying a coherent amount+1
    # output whose public statement is rebound to the honest input.
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    bound = _bind(governance, executed)
    foreign_input = replace(
        executed.module_input,
        command=replace(executed.module_input.command, amount_atoms=31),
    )
    foreign = transition_asset_transfer_lane_module_v1(foreign_input)
    assert isinstance(foreign, AssetTransferLaneModuleAcceptedV1)
    forged = _structurally_rebind_transfer_statement(foreign, executed.module_input.statement_root)
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert: the supplied structural witness is compared before any
    # deterministic recomputation, and the verifier is never invoked.
    with pytest.raises(ValueError, match=_STRUCTURAL_MISMATCH):
        verify_asset_transfer_lane_module_receipt_v1(
            support._transfer_receipt_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                forged,
                bound,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"coherent-foreign-output"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_receipt_recomputation_rejects_structurally_bound_foreign_output() -> None:
    # Arrange: give the coherent foreign output its matching structural witness
    # so that only semantic recomputation can reject it.
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    foreign_input = replace(
        executed.module_input,
        command=replace(executed.module_input.command, amount_atoms=31),
    )
    foreign = transition_asset_transfer_lane_module_v1(foreign_input)
    assert isinstance(foreign, AssetTransferLaneModuleAcceptedV1)
    forged = _structurally_rebind_transfer_statement(foreign, executed.module_input.statement_root)
    forged_bound = binder_module._bind_asset_transfer_lane_output_structural_v1(
        binder_module._snapshot_asset_transfer_route_binding_candidate_v1(
            support._transfer_binding_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                forged,
            )
        )
    )
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert: trusting the supplied acceptance is never an option.
    with pytest.raises(ValueError, match="supplied acceptance differs from recomputation"):
        verify_asset_transfer_lane_module_receipt_v1(
            support._transfer_receipt_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                forged,
                forged_bound,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"structurally-bound-foreign"),
            ),
            verifier,
        )
    with pytest.raises(ValueError, match="supplied acceptance differs from recomputation"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            support._transfer_binding_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                forged,
            )
        )
    assert verifier.calls == []


def test_binding_and_receipt_recompute_the_transition_exactly_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: build the honest witness before instrumenting the deterministic
    # transition used by binding and receipt admission.
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    bound = _bind(governance, executed)
    real_transition = transfer_lane_module._transition_owned_asset_transfer_lane_module_v1
    transition_calls: list[AssetTransferLaneModuleInputV1] = []

    def counted_transition(
        owned_input: AssetTransferLaneModuleInputV1,
    ) -> AssetTransferLaneModuleAcceptedV1:
        transition_calls.append(owned_input)
        result = real_transition(owned_input)
        assert isinstance(result, AssetTransferLaneModuleAcceptedV1)
        return result

    monkeypatch.setattr(
        transfer_lane_module,
        "_transition_owned_asset_transfer_lane_module_v1",
        counted_transition,
    )
    verifier = support._RecordingModuleReceiptVerifier()

    # Act
    rebound = _bind(governance, executed)
    binding_transitions = len(transition_calls)
    verify_asset_transfer_lane_module_receipt_v1(
        support._transfer_receipt_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"one-transfer-transition"),
        ),
        verifier,
    )

    # Assert: structural policy/binding checks are transition-free; each
    # admission recomputes the economic transition once, and the verifier is
    # dispatched last, exactly once.
    assert rebound.binding_root == bound.binding_root
    assert binding_transitions == 1
    assert len(transition_calls) == 2
    assert len(verifier.calls) == 1


def test_verifier_is_unreachable_after_every_structural_policy_or_recompute_failure() -> None:
    # Arrange: one honest fixture plus the retained honest witness.
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    bound = _bind(governance, executed)
    foreign_input = replace(
        executed.module_input,
        command=replace(executed.module_input.command, amount_atoms=31),
    )
    foreign = transition_asset_transfer_lane_module_v1(foreign_input)
    assert isinstance(foreign, AssetTransferLaneModuleAcceptedV1)
    rogue = _execute(governance, edit=_with_state_policy(_policy(fee_owner="mallory")))
    ungoverned = EconomicPolicyRegistryV1(
        tuple(
            binding
            for binding in governance.policy_registry.bindings
            if binding.policy_kind not in _TRANSFER_POLICY_KINDS
        )
    )
    cases: tuple[tuple[str, AssetTransferLaneModuleReceiptCandidateV1, str], ...] = (
        (
            "outside profile",
            replace(
                support._transfer_receipt_candidate(
                    governance,
                    executed.occurrence,
                    executed.module_input,
                    executed.accepted,
                    bound,
                    LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"r"),
                ),
                policy_registry=ungoverned,
            ),
            "outside the profile",
        ),
        (
            "ungoverned member",
            support._transfer_receipt_candidate(
                governance,
                rogue.occurrence,
                rogue.module_input,
                rogue.accepted,
                bound,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"r"),
            ),
            _MEMBER_MISMATCH,
        ),
        (
            "foreign structural witness",
            support._transfer_receipt_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                _structurally_rebind_transfer_statement(
                    foreign,
                    executed.module_input.statement_root,
                ),
                bound,
                LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"r"),
            ),
            _STRUCTURAL_MISMATCH,
        ),
    )

    # Act / Assert
    for label, candidate, message in cases:
        verifier = support._RecordingModuleReceiptVerifier()
        with pytest.raises(ValueError, match=message):
            verify_asset_transfer_lane_module_receipt_v1(candidate, verifier)
        assert verifier.calls == [], label


def test_binder_reads_one_owned_snapshot_across_membership_and_route_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: membership is checked under the governed profile P1. Between
    # membership and route binding a retained alias swaps the candidate to an
    # ungoverned profile P2 (same lanes, no transfer bindings) and P2's
    # occurrence, with a module input executed for P2. A split read would mint
    # a route witness under P2 whose transfer policy was never governed.
    governed = support._transfer_governance_v1()
    ungoverned_profile, ungoverned_routes = support._profile(transfer_policy_kinds=())
    assert ungoverned_profile.policy_registry_root != governed.profile.policy_registry_root
    assert ungoverned_profile.lane_registry == governed.profile.lane_registry
    ungoverned_occurrence = support._occurrence(
        ungoverned_profile,
        ungoverned_routes[_TRANSFER],
        subject_id="alice",
        grant_root=_root(7),
    )
    ungoverned_input = support._asset_input(ungoverned_profile, ungoverned_occurrence)
    ungoverned_accepted = transition_asset_transfer_lane_module_v1(ungoverned_input)
    assert isinstance(ungoverned_accepted, AssetTransferLaneModuleAcceptedV1)
    governed_occurrence = support._occurrence(
        governed.profile,
        governed.routes[_TRANSFER],
        subject_id="alice",
        grant_root=_root(7),
    )
    candidate = AssetTransferReleaseRouteBindingCandidateV1(
        governed.profile,
        governed.policy_registry,
        governed.asset_policy_registry,
        governed_occurrence,
        ungoverned_input,
        ungoverned_accepted,
    )
    real_membership = binder_module.require_asset_transfer_policy_membership_v1
    seam_calls: list[AssetTransferPolicyV1] = []

    def hostile_membership(
        *,
        asset_policy_registry: AssetTransferPolicyRegistryV1,
        module_input: AssetTransferLaneModuleInputV1,
    ) -> AssetTransferPolicyV1:
        member = real_membership(
            asset_policy_registry=asset_policy_registry,
            module_input=module_input,
        )
        object.__setattr__(candidate, "profile", ungoverned_profile)
        object.__setattr__(candidate, "occurrence", ungoverned_occurrence)
        seam_calls.append(member)
        return member

    monkeypatch.setattr(
        binder_module,
        "require_asset_transfer_policy_membership_v1",
        hostile_membership,
    )

    # Act / Assert: the witness is derived from the single snapshot taken at
    # entry, so the swapped-in ungoverned profile never reaches route binding.
    with pytest.raises(ValueError, match="release-route profile root mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(candidate)
    assert len(seam_calls) == 1
    assert candidate.profile is ungoverned_profile
    assert candidate.occurrence is ungoverned_occurrence


def test_retained_candidate_alias_mutations_are_rejected_at_the_snapshot() -> None:
    # Arrange
    governance = support._transfer_governance_v1()
    executed = _execute(governance)

    class AdvertisingOccurrence(EconomicCommandOccurrenceV1):
        @property
        def occurrence_id(self) -> str:
            return executed.occurrence.occurrence_id

    class MimickingRoot(str):
        def __eq__(self, other: object) -> bool:
            return other != ZERO_ROOT_V1

        def __ne__(self, other: object) -> bool:
            return not self.__eq__(other)

        __hash__ = str.__hash__

    hostile_occurrence = AdvertisingOccurrence(
        **{
            field.name: getattr(executed.occurrence, field.name)
            for field in fields(executed.occurrence)
        }
    )
    hostile_binding_rows = tuple(
        replace(binding) for binding in governance.policy_registry.bindings
    )
    hostile_binding = next(
        binding for binding in hostile_binding_rows if binding.policy_kind in _TRANSFER_POLICY_KINDS
    )
    object.__setattr__(hostile_binding, "policy_root", MimickingRoot(_root(999)))
    hostile_bindings = EconomicPolicyRegistryV1(hostile_binding_rows)
    hostile_policy = AssetTransferPolicyV1("USD", "treasury", 2, True)
    object.__setattr__(hostile_policy, "fee_owner", MimickingRoot("treasury"))
    hostile_registry = AssetTransferPolicyRegistryV1(
        governance.asset_policy_registry.module_release_id,
        (hostile_policy,),
    )
    mutations = (
        ("occurrence", hostile_occurrence, "occurrence must have the exact typed value"),
        (
            "profile",
            SimpleNamespace(**_vars_of(governance.profile)),
            "snapshot must have the exact typed value",
        ),
        ("policy_registry", hostile_bindings, "economic policy root must be a string"),
        ("asset_policy_registry", hostile_registry, "must be an exact primitive"),
    )

    for field_name, hostile_value, message in mutations:
        candidate = support._transfer_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
        object.__setattr__(candidate, field_name, hostile_value)

        # Act / Assert: every alias mutation fails at the one owned snapshot.
        with pytest.raises(TypeError, match=message):
            bind_asset_transfer_lane_output_to_release_route_v1(candidate)
    with pytest.raises(TypeError, match="economic policy root must be a string"):
        snapshot_exact_economic_policy_registry_v1(hostile_bindings)


def test_membership_is_content_bound_not_identity_bound() -> None:
    # Arrange
    governance = support._transfer_governance_v1()
    executed = _execute(governance)
    first = _bind(governance, executed)
    rebuilt_registry = _registry(
        tuple(replace(policy) for policy in governance.asset_policy_registry.policies)
    )
    rebuilt_input = replace(
        executed.module_input,
        pre_state=replace(
            executed.module_input.pre_state,
            policies=tuple(replace(policy) for policy in executed.module_input.pre_state.policies),
        ),
    )

    # Act
    second = bind_asset_transfer_lane_output_to_release_route_v1(
        AssetTransferReleaseRouteBindingCandidateV1(
            governance.profile,
            replace(governance.policy_registry),
            rebuilt_registry,
            replace(executed.occurrence),
            rebuilt_input,
            executed.accepted,
        )
    )

    # Assert
    assert second.binding_root == first.binding_root


@pytest.mark.parametrize("transfer_fee_atoms", (0, 1))
def test_governed_binding_preserves_fee_boundaries(transfer_fee_atoms: int) -> None:
    # Arrange: governance rows at the zero and one-atom fee boundaries.
    governance = support._transfer_governance_v1(
        asset_policy_registry=_registry((_policy(transfer_fee_atoms=transfer_fee_atoms),))
    )
    executed = _execute_command(
        governance,
        _command(max_fee_atoms=transfer_fee_atoms),
        balances=(
            EconomicAmountV1("alice", "USD", "accounts", 100),
            EconomicAmountV1("bob", "USD", "accounts", 10),
        ),
        supplies=(AssetSupplyV1("USD", 110),),
    )

    # Act
    bound = _bind(governance, executed)

    # Assert: the typed economic transition is preserved under governance.
    post_state = executed.accepted.post_state
    assert bound.statement_root == executed.module_input.statement_root
    assert post_state.balance_atoms("alice", "USD") == 100 - 30 - transfer_fee_atoms
    assert post_state.balance_atoms("treasury", "USD") == transfer_fee_atoms
    assert len(executed.accepted.effects.fee_conservation) == (1 if transfer_fee_atoms else 0)


def test_governed_binding_preserves_signed_effect_overflow_neighbors() -> None:
    # Arrange: a zero-fee governed row with the exact i128 magnitude neighbors.
    governance = support._transfer_governance_v1(
        asset_policy_registry=_registry((_policy(transfer_fee_atoms=0),))
    )
    representable = (1 << 127) - 1
    overflowing = 1 << 127
    executed = _execute_command(
        governance,
        _command(amount_atoms=representable, max_fee_atoms=0),
        balances=(EconomicAmountV1("alice", "USD", "accounts", representable),),
        supplies=(AssetSupplyV1("USD", representable),),
    )
    profile = governance.profile
    overflow_command = _command(amount_atoms=overflowing, max_fee_atoms=0)
    overflow_occurrence = _occurrence_for(profile, governance.routes[_TRANSFER], overflow_command)
    overflow_input = replace(
        support._asset_input(
            profile,
            overflow_occurrence,
            asset_policy_registry=governance.asset_policy_registry,
        ),
        pre_state=AssetTransferStateV1(
            executed.module_input.pre_state.module_release_id,
            governance.asset_policy_registry.policies,
            (EconomicAmountV1("alice", "USD", "accounts", overflowing),),
            (AssetSupplyV1("USD", overflowing),),
        ),
        command=overflow_command,
    )

    # Act / Assert: the representable neighbor binds; the overflowing neighbor
    # is a typed no-op rejection with nothing to bind.
    assert _bind(governance, executed).statement_root == executed.module_input.statement_root
    assert executed.accepted.post_state.balance_atoms("bob", "USD") == representable
    assert executed.accepted.post_state.balance_atoms("alice", "USD") == 0
    result = transition_asset_transfer_lane_module_v1(overflow_input)
    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code is AssetTransferRejectCodeV1.EFFECT_DELTA_OVERFLOW
    assert result.effects.is_empty


@pytest.mark.parametrize(
    ("fee_owner", "alice_atoms", "bob_atoms", "owner_delta"),
    (("alice", 70, 40, -30), ("bob", 68, 42, 32)),
)
def test_governed_binding_preserves_fee_owner_alias_aggregation(
    fee_owner: str,
    alice_atoms: int,
    bob_atoms: int,
    owner_delta: int,
) -> None:
    # Arrange: the governed fee owner aliases the sender or the recipient.
    governance = support._transfer_governance_v1(
        asset_policy_registry=_registry((_policy(fee_owner=fee_owner),))
    )
    executed = _execute_command(
        governance,
        _command(),
        balances=(
            EconomicAmountV1("alice", "USD", "accounts", 100),
            EconomicAmountV1("bob", "USD", "accounts", 10),
        ),
        supplies=(AssetSupplyV1("USD", 110),),
    )

    # Act
    bound = _bind(governance, executed)

    # Assert
    post_state = executed.accepted.post_state
    assert bound.statement_root == executed.module_input.statement_root
    assert post_state.balance_atoms("alice", "USD") == alice_atoms
    assert post_state.balance_atoms("bob", "USD") == bob_atoms
    owner_row = next(
        row
        for row in executed.accepted.effects.rows
        if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT and row.principal == fee_owner
    )
    assert owner_row.delta_atoms == owner_delta


def test_governed_binding_preserves_first_credit_and_zero_row_removal() -> None:
    # Arrange: Alice is fully debited (amount plus fee) into Carol's first credit.
    governance = support._transfer_governance_v1()
    executed = _execute_command(
        governance,
        _command(recipient="carol", amount_atoms=30, max_fee_atoms=2),
        balances=(
            EconomicAmountV1("alice", "USD", "accounts", 32),
            EconomicAmountV1("treasury", "USD", "accounts", 5),
        ),
        supplies=(AssetSupplyV1("USD", 37),),
    )

    # Act
    bound = _bind(governance, executed)

    # Assert: the absent recipient gains its first row and the zero row is removed.
    post_state = executed.accepted.post_state
    assert bound.statement_root == executed.module_input.statement_root
    assert tuple((row.owner, row.amount_atoms) for row in post_state.balances) == (
        ("carol", 30),
        ("treasury", 7),
    )
    assert post_state.balance_atoms("alice", "USD") == 0
    assert executed.accepted.effects.asset_conservation[0].owned_and_custodied_post_atoms == 37


def _precedence_case(
    case: str,
) -> tuple[AssetTransferReleaseRouteBindingCandidateV1, str]:
    """Build one candidate carrying two defects; the earlier check must win."""

    governance = support._transfer_governance_v1()
    if case == "outside_profile_precedes_absent_member":
        executed = _execute(governance, edit=_with_ungoverned_eur("EUR"))
        ungoverned = EconomicPolicyRegistryV1(
            tuple(
                binding
                for binding in governance.policy_registry.bindings
                if binding.policy_kind not in _TRANSFER_POLICY_KINDS
            )
        )
        candidate = replace(
            support._transfer_binding_candidate(
                governance,
                executed.occurrence,
                executed.module_input,
                executed.accepted,
            ),
            policy_registry=ungoverned,
        )
        return candidate, "outside the profile"
    if case == "absent_binding_precedes_stale_roots":
        one_binding = support._transfer_governance_v1(
            transfer_policy_kinds=(ASSET_TRANSFER_ASSET_POLICY_KIND_V1,)
        )
        executed = _execute(one_binding, edit=_with_roots(_root(11), _root(12)))
        candidate = support._transfer_binding_candidate(
            one_binding,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
        return candidate, "binding is absent from the governed registry"
    if case == "stale_root_precedes_foreign_release":
        executed = _execute(
            governance,
            edit=_under_module_release(_OTHER_RELEASE_ID, asset_policy_registry_root=_root(11)),
        )
        candidate = support._transfer_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
        return candidate, _ASSET_ROOT_MISMATCH
    if case == "foreign_release_precedes_absent_member":
        executed = _execute(
            governance,
            edit=lambda module_input: _with_ungoverned_eur("EUR")(
                _under_module_release(_OTHER_RELEASE_ID)(module_input)
            ),
        )
        candidate = support._transfer_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
        return candidate, _RELEASE_MISMATCH
    raise AssertionError(f"unknown precedence case: {case}")


@pytest.mark.parametrize(
    "case",
    (
        "outside_profile_precedes_absent_member",
        "absent_binding_precedes_stale_roots",
        "stale_root_precedes_foreign_release",
        "foreign_release_precedes_absent_member",
    ),
)
def test_governed_binding_rejection_precedence_is_exact(case: str) -> None:
    # Arrange
    candidate, message = _precedence_case(case)

    # Act / Assert: the earlier governed check wins over the later defect.
    with pytest.raises(ValueError, match=message):
        bind_asset_transfer_lane_output_to_release_route_v1(candidate)


def _vars_of(profile: EconomicProfileSnapshotV1) -> dict[str, object]:
    return {field.name: getattr(profile, field.name) for field in fields(profile)}
