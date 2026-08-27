"""Governed typed policy-registry membership for managed-asset issue and burn.

These tests use a synthetic ACTIVE profile solely to exercise fail-closed
membership through release-route binding and receipt verification. They grant
no release, mount, settlement, or publication authority.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, fields, replace
from types import SimpleNamespace

import pytest

import src.core.lane_module_release_route_binding_v1 as binder_module
from src.core.asset_transfer_types_v1 import ASSET_TRANSFER_COMMAND_KIND_V1
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    AssetSupplyV1,
    EconomicPolicyRegistryV1,
    LaneIdV1,
)
from src.core.lane_module_receipt_verification_v1 import (
    LaneModuleReceiptEnvelopeV1,
    ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
    verify_managed_asset_lifecycle_lane_module_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    ManagedAssetLifecycleReleaseRouteBindingCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
    bind_managed_asset_lifecycle_lane_output_to_release_route_v1,
)
from src.core.managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ManagedAssetLifecycleLaneModuleInputV1,
    transition_managed_asset_lifecycle_lane_module_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    ManagedAssetLifecyclePolicyV1,
)
from src.core.managed_asset_policy_registry_v1 import (
    MANAGED_ASSET_POLICY_KIND_V1,
    MAX_MANAGED_ASSET_POLICIES_V1,
    ManagedAssetPolicyRegistryV1,
    require_governed_managed_asset_policy_registry_v1,
    require_managed_asset_policy_membership_v1,
    require_managed_asset_route_policy_root_v1,
    snapshot_exact_economic_policy_registry_v1,
    snapshot_managed_asset_policy_registry_v1,
)
from tests.core import test_lane_module_release_route_binding_v1 as support

_ISSUE = MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
_BURN = MANAGED_ASSET_BURN_COMMAND_KIND_V1
_DEFAULT_AUTHORITY = {
    _ISSUE: ("issuer", support._root(5)),
    _BURN: ("alice", support._root(6)),
}
_MEMBER_MISMATCH = "state policy is not a governed registry member"
_RELEASE_MISMATCH = "policy registry module release mismatch"
_OTHER_RELEASE_ID = support._root(997)
# Cross-language vectors: the Rust suites assert the same roots for the same
# release-bound registries (USD fixture policy row).
_FIXED_RELEASE_REGISTRY_ROOT_V1 = (
    "0xe9e57192aacf716ec124eabb82fc19ff1382e4a8a60b784b2bed1fb43eac28ba"
)
_OTHER_RELEASE_REGISTRY_ROOT_V1 = (
    "0x155c41281d66c0d34d6d1d2443468a264f123801944cab0174b683001c6ce86a"
)
_FIXTURE_REGISTRY_ROOT_V1 = (
    "0xba06d1d7425a1dff6633b077ad7da33eb7ff681a8623607e9cbda353d87c2879"
)
# Governed issue/burn routes own the registry root as issue_burn_policy_root;
# the Rust route-binding suite asserts the same route release and profile ids.
_GOVERNED_BURN_ROUTE_RELEASE_ID_V1 = (
    "0xf9a0bf0ff296f198c5da915b0e612dcec24eee16b5fb7c65168b63c8b1db4fbc"
)
_GOVERNED_ISSUE_ROUTE_RELEASE_ID_V1 = (
    "0x13a98232cd5861c444fc022c3419967dc488f99ad636202599621f586344962f"
)
_GOVERNED_PROFILE_ID_V1 = (
    "0x8f65206657c02a3677706d7835b94da55e653c45d04abf035e4acd9fdc7a12bd"
)
_ROUTE_POLICY_ROOT_MISMATCH = "route issue/burn policy root mismatch"
_InputEdit = Callable[
    [ManagedAssetLifecycleLaneModuleInputV1],
    ManagedAssetLifecycleLaneModuleInputV1,
]


def _root(value: int) -> str:
    return support._root(value)


def _registry(
    policies: tuple[ManagedAssetLifecyclePolicyV1, ...],
    *,
    module_release_id: str | None = None,
) -> ManagedAssetPolicyRegistryV1:
    return ManagedAssetPolicyRegistryV1(
        support._asset_transfer_release_id_v1()
        if module_release_id is None
        else module_release_id,
        policies,
    )


@dataclass(frozen=True, slots=True)
class _Executed:
    occurrence: EconomicCommandOccurrenceV1
    module_input: ManagedAssetLifecycleLaneModuleInputV1
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1


def _execute(
    governance: support._ManagedGovernanceV1,
    command_kind: str,
    *,
    subject_id: str | None = None,
    grant_root: str | None = None,
    edit: _InputEdit | None = None,
) -> _Executed:
    """Execute one accepted lifecycle transition under the given governance."""

    default_subject, default_grant = _DEFAULT_AUTHORITY[command_kind]
    occurrence = support._occurrence(
        governance.profile,
        governance.routes[command_kind],
        subject_id=default_subject if subject_id is None else subject_id,
        grant_root=default_grant if grant_root is None else grant_root,
    )
    module_input = support._managed_input(governance.profile, occurrence, command_kind)
    if edit is not None:
        module_input = edit(module_input)
    accepted = transition_managed_asset_lifecycle_lane_module_v1(module_input)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    return _Executed(occurrence, module_input, accepted)


def _bind(
    governance: support._ManagedGovernanceV1,
    executed: _Executed,
) -> ReleaseRouteBoundLaneTransitionV1:
    return bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        support._managed_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
    )


def _with_state_policy(policy: ManagedAssetLifecyclePolicyV1) -> _InputEdit:
    def edit(
        module_input: ManagedAssetLifecycleLaneModuleInputV1,
    ) -> ManagedAssetLifecycleLaneModuleInputV1:
        return replace(
            module_input,
            pre_state=replace(module_input.pre_state, policies=(policy,)),
        )

    return edit


def _with_ungoverned_eur(command_asset: str) -> _InputEdit:
    eur = replace(support._managed_asset_policy_v1(), asset="EUR")

    def edit(
        module_input: ManagedAssetLifecycleLaneModuleInputV1,
    ) -> ManagedAssetLifecycleLaneModuleInputV1:
        return replace(
            module_input,
            pre_state=replace(
                module_input.pre_state,
                policies=(eur, support._managed_asset_policy_v1()),
                supplies=(AssetSupplyV1("EUR", 0), AssetSupplyV1("USD", 10)),
            ),
            command=replace(module_input.command, asset=command_asset),
        )

    return edit


def _under_module_release(
    module_release_id: str,
    *,
    asset_policy_registry_root: str | None = None,
) -> _InputEdit:
    """Execute the same command and policy rows under another module release."""

    def edit(
        module_input: ManagedAssetLifecycleLaneModuleInputV1,
    ) -> ManagedAssetLifecycleLaneModuleInputV1:
        edited = replace(
            module_input,
            context=replace(module_input.context, module_release_id=module_release_id),
            pre_state=replace(module_input.pre_state, module_release_id=module_release_id),
        )
        if asset_policy_registry_root is None:
            return edited
        return replace(edited, asset_policy_registry_root=asset_policy_registry_root)

    return edit


def test_registry_root_is_content_derived_and_member_lookup_is_exact() -> None:
    # Arrange
    registry = support._managed_asset_policy_registry_v1()
    rebuilt = _registry(tuple(replace(policy) for policy in registry.policies))
    disabled = _registry((replace(registry.policies[0], enabled=False),))

    # Act / Assert
    assert registry.registry_root == rebuilt.registry_root
    assert registry.registry_root != disabled.registry_root
    assert registry.registry_root.startswith("0x") and len(registry.registry_root) == 66
    assert registry.policy_for("USD") == support._managed_asset_policy_v1()
    assert registry.policy_for("EUR") is None
    with pytest.raises(ValueError, match="must not be empty"):
        registry.policy_for("")


def test_registry_root_binds_the_module_release_with_cross_language_vectors() -> None:
    # Arrange: identical policy rows under three module releases.
    rows = (support._managed_asset_policy_v1(),)
    fixed = _registry(rows, module_release_id=_root(3))
    other = _registry(rows, module_release_id=_OTHER_RELEASE_ID)
    fixture = support._managed_asset_policy_registry_v1()

    # Act / Assert: the release is part of the root, so rows cannot be replayed.
    assert fixed.registry_root == _FIXED_RELEASE_REGISTRY_ROOT_V1
    assert other.registry_root == _OTHER_RELEASE_REGISTRY_ROOT_V1
    assert fixture.registry_root == _FIXTURE_REGISTRY_ROOT_V1
    assert fixture.module_release_id == support._asset_transfer_release_id_v1()
    assert len({fixed.registry_root, other.registry_root, fixture.registry_root}) == 3
    assert fixed.policies == other.policies == fixture.policies


def test_registry_rejects_zero_malformed_and_untyped_module_release() -> None:
    rows = (support._managed_asset_policy_v1(),)

    with pytest.raises(ValueError, match="module release must be nonzero"):
        ManagedAssetPolicyRegistryV1(ZERO_ROOT_V1, rows)
    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed"):
        ManagedAssetPolicyRegistryV1("0x12", rows)
    with pytest.raises(TypeError, match="module release must be a string"):
        ManagedAssetPolicyRegistryV1(3, rows)  # type: ignore[arg-type]


def test_registry_rejects_unsorted_duplicate_and_untyped_members() -> None:
    usd = support._managed_asset_policy_v1()
    eur = replace(usd, asset="EUR")

    with pytest.raises(ValueError, match="canonically ordered and unique"):
        _registry((usd, eur))
    with pytest.raises(ValueError, match="canonically ordered and unique"):
        _registry((usd, usd))
    with pytest.raises(TypeError, match="contains an invalid value"):
        _registry((usd, object()))  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="must be a tuple"):
        _registry([usd])  # type: ignore[arg-type]


def test_registry_cardinality_bva_accepts_bound_and_rejects_one_over() -> None:
    def policies(count: int) -> tuple[ManagedAssetLifecyclePolicyV1, ...]:
        return tuple(
            replace(support._managed_asset_policy_v1(), asset=f"A{index:03d}")
            for index in range(count)
        )

    at_limit = _registry(policies(MAX_MANAGED_ASSET_POLICIES_V1))

    assert len(at_limit.policies) == MAX_MANAGED_ASSET_POLICIES_V1 == 256
    with pytest.raises(ValueError, match="exceeds the ABI V1 bound"):
        _registry(policies(MAX_MANAGED_ASSET_POLICIES_V1 + 1))


@pytest.mark.parametrize("command_kind", (_ISSUE, _BURN))
def test_governed_member_binds_and_verifies_through_receipt(command_kind: str) -> None:
    # Arrange
    governance = support._managed_governance_v1()
    executed = _execute(governance, command_kind)
    verifier = support._RecordingModuleReceiptVerifier()

    # Act
    bound = _bind(governance, executed)
    verified = verify_managed_asset_lifecycle_lane_module_receipt_v1(
        support._managed_receipt_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"governed-receipt"),
        ),
        verifier,
    )

    # Assert
    assert executed.module_input.asset_policy_registry_root == (
        governance.asset_policy_registry.registry_root
    )
    assert executed.module_input.context.module_release_id == (
        governance.asset_policy_registry.module_release_id
    )
    assert bound.statement_root == executed.module_input.statement_root
    assert verified.release_route_binding_root == bound.binding_root
    assert len(verifier.calls) == 1


def test_membership_returns_an_owned_exact_governed_member() -> None:
    # Arrange
    governance = support._managed_governance_v1()
    executed = _execute(governance, _ISSUE)

    # Act
    member = require_managed_asset_policy_membership_v1(
        asset_policy_registry=governance.asset_policy_registry,
        module_input=executed.module_input,
    )

    # Assert
    assert member == support._managed_asset_policy_v1()
    assert member is not governance.asset_policy_registry.policies[0]


def test_direct_transition_stays_authority_free_and_binding_pins_the_governed_root() -> None:
    # Arrange: the lane statement carries an ungoverned opaque policy registry root.
    governance = support._managed_governance_v1()
    executed = _execute(
        governance,
        _ISSUE,
        edit=lambda module_input: replace(module_input, asset_policy_registry_root=_root(11)),
    )

    # Act / Assert: the direct transition accepted without consulting any registry;
    # only release-route binding pins the governed typed registry root.
    assert executed.accepted.private_port.pre_state.asset_policy_registry_root == _root(11)
    with pytest.raises(ValueError, match="lane module policy registry root mismatch"):
        _bind(governance, executed)


def test_policy_registry_outside_the_profile_rejects_before_route_binding() -> None:
    # Arrange: drop the managed bindings so the registry root leaves the profile.
    governance = support._managed_governance_v1()
    executed = _execute(governance, _ISSUE)
    ungoverned = EconomicPolicyRegistryV1(
        tuple(
            binding
            for binding in governance.policy_registry.bindings
            if binding.policy_kind != MANAGED_ASSET_POLICY_KIND_V1
        )
    )
    candidate = replace(
        support._managed_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        ),
        policy_registry=ungoverned,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="policy registry is outside the profile"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(candidate)


def test_binding_absent_for_the_command_kind_rejects() -> None:
    # Arrange: the profile governs managed issue only.
    governance = support._managed_governance_v1(managed_command_kinds=(_ISSUE,))
    issue = _execute(governance, _ISSUE)
    burn = _execute(governance, _BURN)

    # Act / Assert
    assert _bind(governance, issue).route_release_id == (
        governance.routes[_ISSUE].route_release_id
    )
    with pytest.raises(ValueError, match="binding is absent from the governed registry"):
        _bind(governance, burn)


def test_typed_registry_root_must_match_the_governed_binding() -> None:
    # Arrange: a registry whose only member differs from the governed one by one root.
    governance = support._managed_governance_v1()
    executed = _execute(governance, _BURN)
    substituted = _registry(
        (replace(support._managed_asset_policy_v1(), burn_policy_root=_root(66)),)
    )
    candidate = replace(
        support._managed_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        ),
        asset_policy_registry=substituted,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="managed asset policy registry root mismatch"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(candidate)


@pytest.mark.parametrize("command_kind", (_ISSUE, _BURN))
def test_same_policy_rows_under_another_module_release_reject_at_membership(
    command_kind: str,
) -> None:
    # Arrange: the module executes the governed rows under a foreign release while
    # advertising the governed registry root.
    governance = support._managed_governance_v1()
    executed = _execute(governance, command_kind, edit=_under_module_release(_OTHER_RELEASE_ID))

    # Act / Assert
    assert executed.module_input.asset_policy_registry_root == (
        governance.asset_policy_registry.registry_root
    )
    with pytest.raises(ValueError, match=_RELEASE_MISMATCH):
        _bind(governance, executed)


def test_registry_bound_to_another_release_rejects_the_governed_module() -> None:
    # Arrange: the profile governs rows bound to a foreign release; the module runs
    # under the active release and advertises that governed root.
    governance = support._managed_governance_v1(
        asset_policy_registry=support._managed_asset_policy_registry_v1(_OTHER_RELEASE_ID)
    )
    executed = _execute(
        governance,
        _ISSUE,
        edit=lambda module_input: replace(
            module_input,
            asset_policy_registry_root=governance.asset_policy_registry.registry_root,
        ),
    )

    # Act / Assert
    with pytest.raises(ValueError, match=_RELEASE_MISMATCH):
        _bind(governance, executed)
    with pytest.raises(ValueError, match=_RELEASE_MISMATCH):
        require_managed_asset_policy_membership_v1(
            asset_policy_registry=governance.asset_policy_registry,
            module_input=executed.module_input,
        )


def test_route_release_check_remains_independent_of_registry_membership() -> None:
    # Arrange: rows, registry, context, and pre-state all agree on a foreign release
    # that the governed lane registry does not carry.
    governance = support._managed_governance_v1(
        asset_policy_registry=support._managed_asset_policy_registry_v1(_OTHER_RELEASE_ID)
    )
    executed = _execute(
        governance,
        _BURN,
        edit=_under_module_release(
            _OTHER_RELEASE_ID,
            asset_policy_registry_root=governance.asset_policy_registry.registry_root,
        ),
    )

    # Act / Assert: membership passes and the release-route binding still fails closed.
    assert require_managed_asset_policy_membership_v1(
        asset_policy_registry=governance.asset_policy_registry,
        module_input=executed.module_input,
    ) == support._managed_asset_policy_v1()
    with pytest.raises(ValueError, match="release-route module release mismatch"):
        _bind(governance, executed)
    assert governance.profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER).release_id != (
        _OTHER_RELEASE_ID
    )


def test_ungoverned_issuer_substitution_rejects_at_membership() -> None:
    # Arrange: the state names mallory as issuer and the occurrence matches the state.
    governance = support._managed_governance_v1()
    rogue = replace(
        support._managed_asset_policy_v1(),
        issue_authority_subject="mallory",
        issue_policy_root=_root(55),
    )
    executed = _execute(
        governance,
        _ISSUE,
        subject_id="mallory",
        grant_root=_root(55),
        edit=_with_state_policy(rogue),
    )

    # Act / Assert: the module accepted, governed membership does not.
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        _bind(governance, executed)


@pytest.mark.parametrize(
    ("command_kind", "field", "value"),
    (
        (_BURN, "issue_authority_subject", "mallory"),
        (_BURN, "issue_policy_root", _root(55)),
        (_ISSUE, "burn_policy_root", _root(66)),
    ),
)
def test_state_policy_field_substitution_rejects_at_membership(
    command_kind: str,
    field: str,
    value: str,
) -> None:
    # Arrange: substitute one authority field the executed command does not consult.
    governance = support._managed_governance_v1()
    substituted = replace(support._managed_asset_policy_v1(), **{field: value})
    executed = _execute(governance, command_kind, edit=_with_state_policy(substituted))

    # Act / Assert
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        _bind(governance, executed)


def test_command_asset_absent_from_the_governed_registry_rejects() -> None:
    # Arrange: the state carries an ungoverned EUR policy and the command issues EUR.
    governance = support._managed_governance_v1()
    executed = _execute(governance, _ISSUE, edit=_with_ungoverned_eur("EUR"))

    # Act / Assert
    with pytest.raises(ValueError, match="absent from the governed policy registry"):
        _bind(governance, executed)


def test_state_carrying_an_ungoverned_extra_policy_rejects() -> None:
    # Arrange: the command targets the governed USD member, the state also carries EUR.
    governance = support._managed_governance_v1()
    executed = _execute(governance, _ISSUE, edit=_with_ungoverned_eur("USD"))

    # Act / Assert
    with pytest.raises(ValueError, match=_MEMBER_MISMATCH):
        _bind(governance, executed)


def test_empty_governed_registry_rejects_every_asset() -> None:
    # Arrange
    empty = _registry(())
    governance = support._managed_governance_v1(asset_policy_registry=empty)
    executed = _execute(
        governance,
        _ISSUE,
        edit=lambda module_input: replace(
            module_input,
            asset_policy_registry_root=empty.registry_root,
        ),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="absent from the governed policy registry"):
        _bind(governance, executed)


def test_hostile_registry_and_member_subclasses_cannot_advertise_the_governed_root() -> None:
    # Arrange
    governance = support._managed_governance_v1()
    executed = _execute(governance, _ISSUE)
    governed_root = governance.asset_policy_registry.registry_root
    rogue_member = replace(
        support._managed_asset_policy_v1(),
        issue_authority_subject="mallory",
        issue_policy_root=_root(55),
    )

    class AdvertisingRegistry(ManagedAssetPolicyRegistryV1):
        @property
        def registry_root(self) -> str:
            return governed_root

    class MimickingPolicy(ManagedAssetLifecyclePolicyV1):
        def to_canonical(self) -> dict[str, object]:
            return support._managed_asset_policy_v1().to_canonical()

    advertising = AdvertisingRegistry(
        governance.asset_policy_registry.module_release_id,
        (rogue_member,),
    )
    mimicking = _registry(
        (
            MimickingPolicy(
                asset=rogue_member.asset,
                asset_class=rogue_member.asset_class,
                issue_authority_subject=rogue_member.issue_authority_subject,
                issue_policy_root=rogue_member.issue_policy_root,
                burn_policy_root=rogue_member.burn_policy_root,
                enabled=rogue_member.enabled,
            ),
        )
    )
    assert advertising.registry_root == governed_root
    assert mimicking.registry_root == governed_root

    # Act / Assert: neither hostile shape reaches membership comparison.
    with pytest.raises(TypeError, match="requires exact typed inputs"):
        ManagedAssetLifecycleReleaseRouteBindingCandidateV1(
            governance.profile,
            governance.policy_registry,
            advertising,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
    with pytest.raises(TypeError, match="registry type is not closed"):
        require_governed_managed_asset_policy_registry_v1(
            profile=governance.profile,
            policy_registry=governance.policy_registry,
            occurrence=executed.occurrence,
            asset_policy_registry=advertising,
        )
    with pytest.raises(TypeError, match="must contain exact typed values"):
        snapshot_managed_asset_policy_registry_v1(mimicking)
    with pytest.raises(TypeError, match="must contain exact typed values"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            replace(
                support._managed_binding_candidate(
                    governance,
                    executed.occurrence,
                    executed.module_input,
                    executed.accepted,
                ),
                asset_policy_registry=mimicking,
            )
        )


def test_binding_and_receipt_candidates_reject_untyped_registries() -> None:
    # Arrange
    governance = support._managed_governance_v1()
    executed = _execute(governance, _ISSUE)
    bound = _bind(governance, executed)
    authenticated = support._authenticate_occurrence_for_test(
        governance.profile,
        executed.occurrence,
        executed.module_input.command,
        policy_registry=governance.policy_registry,
    )

    # Act / Assert
    with pytest.raises(TypeError, match="route candidate must have the exact type"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            object()  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError, match="requires exact typed inputs"):
        ManagedAssetLifecycleReleaseRouteBindingCandidateV1(
            governance.profile,
            object(),  # type: ignore[arg-type]
            governance.asset_policy_registry,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
    with pytest.raises(TypeError, match="managed asset policy registry must be typed"):
        ManagedAssetLifecycleLaneModuleReceiptCandidateV1(
            governance.profile,
            governance.policy_registry,
            object(),  # type: ignore[arg-type]
            authenticated,
            executed.module_input,
            executed.accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"untyped"),
        )


def test_receipt_candidate_registry_substitution_never_reaches_the_verifier() -> None:
    # Arrange: retain a valid receipt candidate, then swap its typed registry.
    governance = support._managed_governance_v1()
    executed = _execute(governance, _BURN)
    bound = _bind(governance, executed)
    candidate = support._managed_receipt_candidate(
        governance,
        executed.occurrence,
        executed.module_input,
        executed.accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"substituted-registry"),
    )
    substituted = _registry((replace(support._managed_asset_policy_v1(), enabled=False),))
    object.__setattr__(candidate, "asset_policy_registry", substituted)
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="managed asset policy registry root mismatch"):
        verify_managed_asset_lifecycle_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_receipt_candidate_foreign_release_registry_never_reaches_the_verifier() -> None:
    # Arrange: the same rows bound to a foreign release replace the governed registry.
    governance = support._managed_governance_v1()
    executed = _execute(governance, _ISSUE)
    bound = _bind(governance, executed)
    candidate = support._managed_receipt_candidate(
        governance,
        executed.occurrence,
        executed.module_input,
        executed.accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"foreign-release-registry"),
    )
    object.__setattr__(
        candidate,
        "asset_policy_registry",
        support._managed_asset_policy_registry_v1(_OTHER_RELEASE_ID),
    )
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="managed asset policy registry root mismatch"):
        verify_managed_asset_lifecycle_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_membership_is_content_bound_not_identity_bound() -> None:
    # Arrange
    governance = support._managed_governance_v1()
    executed = _execute(governance, _BURN)
    first = _bind(governance, executed)
    rebuilt_registry = _registry(
        tuple(replace(policy) for policy in governance.asset_policy_registry.policies)
    )
    rebuilt_input = replace(
        executed.module_input,
        pre_state=replace(
            executed.module_input.pre_state,
            policies=tuple(
                replace(policy) for policy in executed.module_input.pre_state.policies
            ),
        ),
    )

    # Act
    second = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        ManagedAssetLifecycleReleaseRouteBindingCandidateV1(
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


def test_governed_routes_own_the_exact_registry_root_with_cross_language_vectors() -> None:
    # Arrange
    governance = support._managed_governance_v1()
    executed = _execute(governance, _BURN)

    # Act
    route = require_managed_asset_route_policy_root_v1(
        profile=governance.profile,
        occurrence=executed.occurrence,
        asset_policy_registry=governance.asset_policy_registry,
    )

    # Assert: the route-owned issue/burn policy root is the typed registry root.
    assert route.issue_burn_policy_root == governance.asset_policy_registry.registry_root
    assert route.route_release_id == executed.occurrence.route_release_id
    assert governance.routes[_BURN].route_release_id == _GOVERNED_BURN_ROUTE_RELEASE_ID_V1
    assert governance.routes[_ISSUE].route_release_id == _GOVERNED_ISSUE_ROUTE_RELEASE_ID_V1
    assert governance.profile.profile_id == _GOVERNED_PROFILE_ID_V1
    with pytest.raises(ValueError, match="requires an issue or burn command"):
        require_managed_asset_route_policy_root_v1(
            profile=governance.profile,
            occurrence=replace(executed.occurrence, command_kind=ASSET_TRANSFER_COMMAND_KIND_V1),
            asset_policy_registry=governance.asset_policy_registry,
        )


@pytest.mark.parametrize("command_kind", (_ISSUE, _BURN))
def test_wrong_route_issue_burn_policy_root_rejects_before_any_witness(
    command_kind: str,
) -> None:
    # Arrange: governed rows and membership are exact, but the selected route
    # carries a stale route-owned issue/burn policy root.
    governance = support._managed_governance_v1(route_issue_burn_policy_root=_root(511))
    executed = _execute(governance, command_kind)
    assert require_managed_asset_policy_membership_v1(
        asset_policy_registry=governance.asset_policy_registry,
        module_input=executed.module_input,
    ) == support._managed_asset_policy_v1()

    # Act / Assert
    with pytest.raises(ValueError, match=_ROUTE_POLICY_ROOT_MISMATCH):
        _bind(governance, executed)
    with pytest.raises(ValueError, match=_ROUTE_POLICY_ROOT_MISMATCH):
        require_managed_asset_route_policy_root_v1(
            profile=governance.profile,
            occurrence=executed.occurrence,
            asset_policy_registry=governance.asset_policy_registry,
        )


def test_wrong_route_issue_burn_policy_root_never_reaches_the_verifier() -> None:
    # Arrange: a witness minted under the exact governed profile cannot stand in
    # for a route whose issue/burn policy root is stale.
    governed = support._managed_governance_v1()
    governed_executed = _execute(governed, _ISSUE)
    witness = _bind(governed, governed_executed)
    stale = support._managed_governance_v1(route_issue_burn_policy_root=_root(511))
    executed = _execute(stale, _ISSUE)
    candidate = support._managed_receipt_candidate(
        stale,
        executed.occurrence,
        executed.module_input,
        executed.accepted,
        witness,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"wrong-route-policy-root"),
    )
    verifier = support._RecordingModuleReceiptVerifier()

    # Act / Assert: the rebind rejects before any receipt bytes reach the verifier.
    with pytest.raises(ValueError, match=_ROUTE_POLICY_ROOT_MISMATCH):
        verify_managed_asset_lifecycle_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_binder_reads_one_owned_snapshot_across_membership_and_route_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: membership is checked under the governed profile P1. Between
    # membership and route binding a retained alias swaps the candidate to an
    # ungoverned profile P2 (same lanes, no managed bindings) and P2's burn
    # occurrence, with a module input executed for P2. A split read would mint a
    # route witness under P2 whose managed policy was never governed.
    governed = support._managed_governance_v1()
    ungoverned_profile, ungoverned_routes = support._profile()
    assert ungoverned_profile.policy_registry_root != governed.profile.policy_registry_root
    assert ungoverned_profile.lane_registry == governed.profile.lane_registry
    ungoverned_occurrence = support._occurrence(
        ungoverned_profile,
        ungoverned_routes[_BURN],
        subject_id="alice",
        grant_root=_root(6),
    )
    ungoverned_input = support._managed_input(ungoverned_profile, ungoverned_occurrence, _BURN)
    ungoverned_accepted = transition_managed_asset_lifecycle_lane_module_v1(ungoverned_input)
    assert isinstance(ungoverned_accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    governed_occurrence = support._occurrence(
        governed.profile,
        governed.routes[_BURN],
        subject_id="alice",
        grant_root=_root(6),
    )
    candidate = ManagedAssetLifecycleReleaseRouteBindingCandidateV1(
        governed.profile,
        governed.policy_registry,
        governed.asset_policy_registry,
        governed_occurrence,
        ungoverned_input,
        ungoverned_accepted,
    )
    real_membership = binder_module.require_managed_asset_policy_membership_v1
    seam_calls: list[ManagedAssetLifecyclePolicyV1] = []

    def hostile_membership(
        *,
        asset_policy_registry: ManagedAssetPolicyRegistryV1,
        module_input: ManagedAssetLifecycleLaneModuleInputV1,
    ) -> ManagedAssetLifecyclePolicyV1:
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
        "require_managed_asset_policy_membership_v1",
        hostile_membership,
    )

    # Act / Assert: the witness is derived from the single snapshot taken at
    # entry, so the swapped-in ungoverned profile never reaches route binding.
    with pytest.raises(ValueError, match="release-route profile root mismatch"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(candidate)
    assert len(seam_calls) == 1
    assert candidate.profile is ungoverned_profile
    assert candidate.occurrence is ungoverned_occurrence


def test_retained_candidate_alias_mutations_are_rejected_at_the_snapshot() -> None:
    # Arrange
    governance = support._managed_governance_v1()
    executed = _execute(governance, _ISSUE)

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
        **{field.name: getattr(executed.occurrence, field.name) for field in fields(executed.occurrence)}
    )
    hostile_bindings = EconomicPolicyRegistryV1(
        tuple(
            replace(binding, policy_root=MimickingRoot(_root(999)))
            if binding.policy_kind == MANAGED_ASSET_POLICY_KIND_V1
            else binding
            for binding in governance.policy_registry.bindings
        )
    )
    mutations = (
        ("occurrence", hostile_occurrence, "occurrence must have the exact typed value"),
        ("profile", SimpleNamespace(**vars_of(governance.profile)), "snapshot must have the exact typed value"),
        ("policy_registry", hostile_bindings, "must be an exact primitive"),
    )

    for field_name, hostile_value, message in mutations:
        candidate = support._managed_binding_candidate(
            governance,
            executed.occurrence,
            executed.module_input,
            executed.accepted,
        )
        object.__setattr__(candidate, field_name, hostile_value)

        # Act / Assert: every alias mutation fails at the one owned snapshot.
        with pytest.raises(TypeError, match=message):
            bind_managed_asset_lifecycle_lane_output_to_release_route_v1(candidate)
    with pytest.raises(TypeError, match="must be an exact primitive"):
        snapshot_exact_economic_policy_registry_v1(hostile_bindings)


def vars_of(profile: object) -> dict[str, object]:
    return {field.name: getattr(profile, field.name) for field in fields(profile)}
