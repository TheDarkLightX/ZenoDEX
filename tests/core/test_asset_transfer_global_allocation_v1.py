"""Global allocation binding controls; receipt/signature verifiers are mocks."""

from dataclasses import fields, replace

import pytest

from src.core import asset_transfer_receipt_admission_v1 as admission
from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core import global_settlement_types_v1 as types
from src.core.asset_lane_projection_v1 import project_asset_transfer_state_v1
from src.core.asset_transfer_global_allocation_v1 import (
    AssetTransferGlobalAllocationCandidateV1,
    GlobalAllocationBindingRejectedV1,
)
from src.core.asset_transfer_global_allocation_v1 import (
    GlobalAllocationBindingRejectCodeV1 as Code,
)
from src.core.global_accounting_allocation_projection_v1 import project_allocation_certificate_v1
from tests.core.test_global_settlement_abi_v1 import (
    _POLICY_REGISTRY_BY_PROFILE_ID_V1,
    _asset_module_input_for_occurrence,
    _asset_transfer_policy_registry_for_route_v1,
    _epoch_asset_module_state,
    _global_state_from_asset_module,
    _occurrence,
    _profile,
    _verified_asset_module_for_occurrence,
)


def _global_allocation_fixture(*, controlled_atoms=0, claimant_count=1):
    """Construct the restricted profile and complete pre-state before signing."""
    base, route = _profile()
    arguments = {
        field.name: getattr(base, field.name)
        for field in fields(base)
        if field.name != "profile_id"
    }
    arguments["lane_registry"] = types.LaneRegistryV1(
        tuple(
            row
            if row.lane_id is types.LaneIdV1.ASSET_TRANSFER
            else replace(
                row,
                status=types.ReleaseStatusV1.RETIRED,
                accepts_new_objects=False,
                evidence_statuses=(types.EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,),
            )
            for row in base.lane_registry.releases
        )
    )
    profile = types.EconomicProfileSnapshotV1.build(**arguments)
    _POLICY_REGISTRY_BY_PROFILE_ID_V1[profile.profile_id] = _POLICY_REGISTRY_BY_PROFILE_ID_V1[
        base.profile_id
    ]
    module_state = _epoch_asset_module_state(profile)
    custody = ()
    liabilities = ()
    if controlled_atoms:
        module_state = replace(
            module_state,
            supplies=tuple(
                replace(row, amount_atoms=row.amount_atoms + controlled_atoms)
                if row.asset == "USD"
                else row
                for row in module_state.supplies
            ),
        )
        custody = (types.EconomicAmountV1("custodian", "USD", "vault", controlled_atoms),)
        liabilities = (types.EconomicAmountV1("alice", "USD", "vault", controlled_atoms),)
        if claimant_count > 1:
            assert controlled_atoms % claimant_count == 0
            liabilities = tuple(types.EconomicAmountV1(
                f"claimant-{index:04d}", "USD", "vault", controlled_atoms // claimant_count,
            ) for index in range(claimant_count))
    # The generic helper assumes no custody, so initialize the complete state
    # from its ordinary base and then substitute all three economic tables.
    pre = _global_state_from_asset_module(profile, _epoch_asset_module_state(profile), height=0)
    registry = _asset_transfer_policy_registry_for_route_v1(route)
    projection = project_asset_transfer_state_v1(
        module_state,
        asset_policy_registry_root=registry.asset_policy_root,
        fee_policy_registry_root=registry.fee_policy_root,
        custody=custody,
    )
    lanes = tuple(
        replace(
            row,
            state_root=(
                projection.state_root
                if row.lane_id is types.LaneIdV1.ASSET_TRANSFER
                else cert.REGISTERED_EMPTY_LANE_ROOTS_V1.get(row.lane_id, row.state_root)
            ),
        )
        for row in pre.lane_roots
    )
    pre = replace(
        pre,
        lane_roots=lanes,
        balances=projection.balances,
        custody=custody,
        liabilities=liabilities,
        supplies=projection.supplies,
    )
    occurrence = _occurrence(profile, route, pre)
    module_input = _asset_module_input_for_occurrence(
        profile, occurrence, _epoch_asset_module_state(profile)
    )
    module_input = replace(module_input, pre_state=module_state, custody=custody)
    accepted, witness = _verified_asset_module_for_occurrence(profile, occurrence, module_input)
    post_projection = accepted.private_port.post_state
    post = replace(
        pre,
        height=1,
        lane_roots=(replace(lanes[0], state_root=post_projection.state_root), *lanes[1:]),
        balances=post_projection.balances,
        supplies=post_projection.supplies,
        replay_state=(types.ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id),),
    )
    return profile, route, occurrence, accepted, witness, pre, post


def _admit(fixture):
    _, _, occurrence, accepted, witness, pre, post = fixture
    return admission.verify_asset_transfer_global_fragment_receipt_v1(
        witness, AssetTransferGlobalAllocationCandidateV1(accepted, occurrence, pre, post)
    )


@pytest.mark.parametrize("controlled_atoms", [0, 1, 100, (1 << 127)])
def test_global_fragment_preserves_distinct_roots_and_exact_claimant_partition(controlled_atoms):
    fixture = _global_allocation_fixture(controlled_atoms=controlled_atoms)
    _, _, occurrence, accepted, witness, pre, post = fixture
    before = types.canonical_global_bytes_v1(
        (pre, post, occurrence, accepted.module_journal, accepted.private_port)
    )
    result = _admit(fixture)
    assert isinstance(result, cert.VerifiedLaneAllocationFragmentV1)
    assert accepted.module_journal.post_lane_root != post.lane_roots[0].state_root
    assert result.fragment.lane_state_root == post.lane_roots[0].state_root
    assert result.module_journal_root == witness.module_journal_root
    assert tuple(
        (row.claimant, row.amount_atoms) for row in result.fragment.claimant_entitlements
    ) == ((("alice", controlled_atoms),) if controlled_atoms else ())
    slots = (result, *(None for _ in types.ALL_LANE_IDS_V1[1:]))
    projected = project_allocation_certificate_v1(
        post, ((types.LaneIdV1.ASSET_TRANSFER, result.receipt_root),), slots
    )
    assert isinstance(projected, cert.GlobalAccountingAllocationCertificateV1)
    checked = cert.check_global_accounting_allocation_certificate_v1(projected, post, slots)
    assert isinstance(checked, cert.AllocationCertificateAcceptedV1)
    assert before == types.canonical_global_bytes_v1(
        (pre, post, occurrence, accepted.module_journal, accepted.private_port)
    )


@pytest.mark.parametrize("field", ["chain_id", "deployment_root", "profile_root", "writer_epoch"])
def test_every_current_header_coordinate_is_bound(field):
    fixture = _global_allocation_fixture()
    current = fixture[-1]
    changed = (
        "foreign"
        if field == "chain_id"
        else (current.writer_epoch + 1 if field == "writer_epoch" else "0x" + "99" * 32)
    )
    result = _admit((*fixture[:-1], replace(current, **{field: changed})))
    assert result == GlobalAllocationBindingRejectedV1(Code.GLOBAL_CONTEXT_DRIFT)


@pytest.mark.parametrize(
    "kind,expected",
    [
        ("height", Code.GLOBAL_OCCURRENCE_DRIFT),
        ("enabled", Code.GLOBAL_LANE_SCOPE_UNSUPPORTED),
        ("release", Code.GLOBAL_LANE_SCOPE_UNSUPPORTED),
        ("root", Code.GLOBAL_LANE_ROOT_DRIFT),
        ("balance", Code.GLOBAL_PROJECTION_ROWS_DRIFT),
        ("custody", Code.GLOBAL_PROJECTION_ROWS_DRIFT),
        ("supply", Code.GLOBAL_PROJECTION_ROWS_DRIFT),
        ("claimant", Code.GLOBAL_CLAIMANT_CONTINUITY_DRIFT),
        ("liability_amount", Code.GLOBAL_CLAIMANT_CONTINUITY_DRIFT),
        ("reserve", Code.GLOBAL_UNSUPPORTED_STATE),
        ("replay", Code.GLOBAL_REPLAY_CONTINUITY_DRIFT),
    ],
)
def test_independent_current_binding_guard_failures_are_no_op(kind, expected):
    fixture = _global_allocation_fixture(controlled_atoms=100)
    post = fixture[-1]
    if kind == "height":
        post = replace(post, height=2)
    elif kind == "enabled":
        post = replace(
            post,
            lane_roots=(
                post.lane_roots[0],
                replace(post.lane_roots[1], enabled=True),
                *post.lane_roots[2:],
            ),
        )
    elif kind in {"release", "root"}:
        key = "module_release_id" if kind == "release" else "state_root"
        post = replace(
            post,
            lane_roots=(
                replace(post.lane_roots[0], **{key: "0x" + "99" * 32}),
                *post.lane_roots[1:],
            ),
        )
    elif kind in {"balance", "custody", "supply"}:
        key = {"balance": "balances", "custody": "custody", "supply": "supplies"}[kind]
        rows = getattr(post, key)
        post = replace(
            post, **{key: (replace(rows[0], amount_atoms=rows[0].amount_atoms + 1), *rows[1:])}
        )
    elif kind in {"claimant", "liability_amount"}:
        change = {"owner": "mallory"} if kind == "claimant" else {"amount_atoms": 99}
        post = replace(post, liabilities=(replace(post.liabilities[0], **change),))
    elif kind == "reserve":
        post = replace(post, reserves=(types.EconomicAmountV1("protocol", "USD", "reserve", 1),))
    elif kind == "replay":
        post = replace(post, replay_state=())
    before = types.canonical_global_bytes_v1(post)
    assert _admit((*fixture[:-1], post)) == GlobalAllocationBindingRejectedV1(expected)
    assert types.canonical_global_bytes_v1(post) == before


def test_predecessor_identity_and_occurrence_preimage_cannot_be_substituted():
    fixture = _global_allocation_fixture(controlled_atoms=100)
    profile, route, occurrence, accepted, witness, pre, post = fixture
    # Conservation remains unchanged; the original occurrence commits the full
    # predecessor and therefore refuses a different claimant initialization.
    changed = replace(pre, liabilities=(replace(pre.liabilities[0], owner="mallory"),))
    assert _admit(
        (profile, route, occurrence, accepted, witness, changed, post)
    ) == GlobalAllocationBindingRejectedV1(Code.GLOBAL_OCCURRENCE_DRIFT)
    changed_occurrence = replace(occurrence, nonce=occurrence.nonce + 1)
    assert _admit(
        (profile, route, changed_occurrence, accepted, witness, pre, post)
    ) == GlobalAllocationBindingRejectedV1(Code.GLOBAL_OCCURRENCE_DRIFT)


def test_foreign_receipt_witness_and_malformed_snapshot_refuse():
    fixture = _global_allocation_fixture()
    other = _global_allocation_fixture(controlled_atoms=1)
    result = _admit((*fixture[:4], other[4], *fixture[5:]))
    assert isinstance(result, admission.ReceiptWitnessRejectedV1)
    assert result.code is admission.ReceiptWitnessRejectCodeV1.WITNESS_JOURNAL_ROOT_DRIFT
    with pytest.raises(TypeError, match="exact typed value"):
        _admit((*fixture[:-1], object()))
    with pytest.raises(ValueError, match="unsigned 64-bit"):
        _admit((*fixture[:-1], replace(fixture[-1], height=1 << 64)))


def test_binding_reject_registry_matches_rust():
    import re
    from pathlib import Path

    source = (
        Path(__file__).resolve().parents[2]
        / "zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs"
    ).read_text()
    variants = source.split("pub enum GlobalAllocationBindingRejectCodeV1 {", 1)[1].split("}", 1)[0]
    assert tuple(re.findall(r"\b(GLOBAL_[A-Z_]+),", variants)) == tuple(code.value for code in Code)


def test_maximum_claimant_partition_is_complete_and_over_limit_snapshot_refuses():
    fixture = _global_allocation_fixture(controlled_atoms=8192, claimant_count=4096)
    witness = _admit(fixture)
    assert isinstance(witness, cert.VerifiedLaneAllocationFragmentV1)
    assert len(witness.fragment.claimant_entitlements) == 4096
    assert witness.fragment.claimant_entitlements[-1].claimant == "claimant-4095"
    current = fixture[-1]
    shifted = replace(current, liabilities=(
        replace(current.liabilities[0], amount_atoms=1), *current.liabilities[1:-1],
        replace(current.liabilities[-1], amount_atoms=3),
    ))
    assert sum(row.amount_atoms for row in shifted.liabilities) == 8192
    assert _admit((*fixture[:-1], shifted)) == GlobalAllocationBindingRejectedV1(Code.GLOBAL_CLAIMANT_CONTINUITY_DRIFT)
    # Hostile caller bypasses construction; admission must reconstruct all rows
    # and reject the over-limit input rather than ignoring the final entry.
    forged = object.__new__(types.GlobalEconomicStateV1)
    for field in fields(current):
        object.__setattr__(forged, field.name, getattr(current, field.name))
    object.__setattr__(forged, "liabilities", (*current.liabilities, types.EconomicAmountV1("zz-last", "USD", "vault", 1)))
    with pytest.raises(ValueError, match="maximum|too many|exceed|4096"):
        _admit((*fixture[:-1], forged))


def test_shared_relation_fixture_is_current():
    from tools.render_asset_transfer_global_allocation_v1_golden import FIXTURE, render

    assert FIXTURE.read_text() == render()


@pytest.mark.parametrize("code", tuple(Code))
def test_each_binding_guard_family_kills_a_semantic_bypass_mutant(code):
    """Delete one named refusal family in memory; its independent vector must distinguish it."""
    import ast
    import inspect
    import json

    from src.core import asset_transfer_global_allocation_v1 as relation
    from src.integration.global_allocation_shadow_v1 import decode_shadow_state_v1
    from tools.render_asset_transfer_global_allocation_v1_golden import FIXTURE

    selected = {
        Code.GLOBAL_CONTEXT_DRIFT: "chain_id",
        Code.GLOBAL_OCCURRENCE_DRIFT: "height",
        Code.GLOBAL_LANE_SCOPE_UNSUPPORTED: "enabled",
        Code.GLOBAL_LANE_ROOT_DRIFT: "root",
        Code.GLOBAL_PROJECTION_ROWS_DRIFT: "balance",
        Code.GLOBAL_CLAIMANT_CONTINUITY_DRIFT: "claimant",
        Code.GLOBAL_UNSUPPORTED_STATE: "reserve",
        Code.GLOBAL_REPLAY_CONTINUITY_DRIFT: "replay",
    }
    case = next(
        row for row in json.loads(FIXTURE.read_text())["cases"] if row["name"] == selected[code]
    )
    _, _, occurrence, accepted, _, _, _ = _global_allocation_fixture(controlled_atoms=100)
    predecessor = decode_shadow_state_v1(case["predecessor"])
    current = decode_shadow_state_v1(case["current"])
    original = relation._global_allocation_binding_reject_v1
    assert original(
        accepted, occurrence, predecessor, current
    ) == GlobalAllocationBindingRejectedV1(code)
    tree = ast.parse(inspect.getsource(original))
    changed = 0
    for node in ast.walk(tree):
        if isinstance(node, ast.If) and any(
            isinstance(statement, ast.Return) and code.value in ast.unparse(statement)
            for statement in node.body
        ):
            node.test = ast.Constant(False)
            changed += 1
    assert changed > 0
    ast.fix_missing_locations(tree)
    namespace = dict(vars(relation))
    exec(compile(tree, "<allocation-guard-family-mutant>", "exec"), namespace)
    mutant = namespace[original.__name__]
    assert mutant(accepted, occurrence, predecessor, current) is None
