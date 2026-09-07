"""Boundary evidence for the buyback Spot safety receipt extraction.

Core prepares the shadow Spot receipt in two pure phases (candidate ownership
plus governed selection, then policy/occurrence/state/Oracle/receipt-domain
checks fixing the complete request and every marker source) and calls no
verifier.  The integration shell owns the exact head and Bound type gates,
head ownership, the two Bound identity reads, the Bound deployment binding,
the single ``verify_profile_lane_receipt`` call on a subject detached
immediately before I/O, and minting from that executed copy only.  The
fee-ingress witness is derived only after callback success.

Every backend here is a deterministic recorder behind the measured Bound
capability, never cryptographic evidence, and nothing below grants
publication or production authority.  The ownership repair is evidence
against callback-retained aliases inside one honest process, not against a
compromised Python process or OS.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
from collections.abc import Callable
from dataclasses import fields as dataclass_fields
from dataclasses import replace
from functools import partial
from pathlib import Path
from typing import Any, cast

import pytest

import src.core.economic_receipt_verifier_deployment_v1 as deployment
import src.core.zdex_buyback_spot_safety_receipt_preparation_v1 as prep
import src.core.zdex_buyback_spot_safety_receipt_v1 as core
import src.integration.zdex_buyback_spot_safety_receipt_v1 as shell
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierSelectionPurposeV1,
)
from src.core.global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    RouteRegistryV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from src.core.zdex_atomic_buyback_state_v1 import ZDEXAtomicBuybackTokenomicsStateV1
from src.core.zdex_buyback_price_authority_v1 import VerifiedZDEXBuybackPriceAuthorityV1
from src.core.zdex_buyback_price_safety_v1 import VerifiedZDEXBuybackPriceSafetyV1
from src.core.zdex_buyback_spot_safety_receipt_v1 import (
    ZDEXBuybackSpotReceiptEnvelopeV1,
    ZDEXBuybackSpotReceiptRejectCodeV1,
    ZDEXBuybackSpotReceiptRejectedV1,
)
from src.core.zdex_fee_allocation_types_v1 import ZDEXFeeAllocationPolicyV1
from src.core.zdex_verified_fee_ingress_slice_v1 import VerifiedZDEXFeeIngressSliceV1
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import (
    _VERIFIER_ARTIFACT,
    _Fixture,
    _fixture,
    _HostileRoot,
    _root,
    _verifier_manifest,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
_CORE_MODULE = "src/core/zdex_buyback_spot_safety_receipt_v1.py"
_PREPARATION_MODULE = "src/core/zdex_buyback_spot_safety_receipt_preparation_v1.py"
_SHELL_MODULE = "src/integration/zdex_buyback_spot_safety_receipt_v1.py"
_MOVED_NAME = "verify_zdex_buyback_spot_safety_receipt_shadow_v2"
_EFFECT_IMPORT_ROOTS = frozenset(
    {"threading", "weakref", "os", "sys", "time", "datetime", "random", "pathlib", "importlib"}
)
# The policy registry's pure ``require_binding`` stays in core; the Bound verifier's
# ``require_binding`` is counted on the shell separately below.
_VERIFIER_CALL_NAMES = frozenset(
    {
        "verify_succinct_receipt",
        "verify_profile_lane_receipt",
        "verify_profile_lane_coordinator_receipt",
        "verify_profile_route_receipt",
    }
)
_RETAINED_CORE_NAMES = (
    "ZDEXBuybackSpotSafetyPurchaseJournalV2",
    "ZDEXBuybackSpotReceiptEnvelopeV1",
    "ZDEXBuybackSpotReceiptCandidateV2",
    "ZDEXBuybackSpotReceiptRejectCodeV1",
    "ZDEXBuybackSpotReceiptRejectedV1",
    "VerifiedZDEXBuybackSpotSafetyPurchaseV2",
    "_VerifiedZDEXBuybackSpotFieldsV2",
    "_ZDEXBuybackSpotReceiptSnapshotV2",
)
_MARKER_FIELD_NAMES = (
    "journal",
    "journal_digest",
    "expected_image_id",
    "receipt_digest",
    "receipt_kind",
    "tokenomics_pre_state",
    "spend_policy",
    "fee_policy",
    "fee_context",
    "fee_command",
    "fee_ingress",
    "price_authority",
    "authority_head_root",
    "verifier_binding_root",
)
_INGRESS_FIELD_NAMES = (
    "command_occurrence_id",
    "global_pre_state_root",
    "profile_root",
    "fee_state_root",
    "fee_asset_id",
    "fee_ingress_atoms",
    "authority_head_root",
    "verifier_binding_root",
)
_PREPARED_FACT_NAMES = tuple(
    name
    for name in (field.name for field in dataclass_fields(prep.PreparedZDEXBuybackSpotSafetyReceiptV2))
    if name not in {"profile", "price_authority"}
)
# Fixed vectors captured on the pre-extraction tree (base 5eedab8f0) with the
# retained fixture and recorder.  The extraction must reproduce them exactly.
_JOURNAL_LEN_PIN = 2690
_JOURNAL_DIGEST_PIN = "0x2fbfc2bf5f34968cdf3204a00c420cd476378a59edb79258fe2ea18a569e03e5"
_RECEIPT_DIGEST_PIN = "0xe1842d7022ae4052d3ae9a81543998499938f22eb93a5747d93a5def35e0a3b6"
_EXPECTED_IMAGE_PIN = "0x0000000000000000000000000000000000000000000000000000000000000429"
_BINDING_ROOT_PIN = "0x5c31513e607ac75e8ac7d6932a086184e3af70607cd269e12ac625b602ce7432"
_HEAD_ROOT_PIN = "0xa013d69a3b516cbfd7bdf6b0b8aa985590b42e332468f154cc4056883aaa5635"
_VERIFIER_BINDING_ROOT_PIN = (
    "0x7cbc86eadc10c8154ac4ef54f93d7e58716400471e4afd7182e7d1b4bdaffcdd"
)
_FEE_INGRESS_BINDING_ROOT_PIN = (
    "0x7ad40feebce872a69f9c7def5c408f5bc3ec5c861d323e794d6739199f31808a"
)
_PRICE_AUTHORITY_ROOT_PIN = (
    "0x15ecdaa5390b408ee4439e5f96491fbddf6f1f339249c8135af787b933b7b421"
)
_PRICE_SAFETY_BINDING_ROOT_PIN = (
    "0xeea967a46948ca6e35c8ee0c59338794663acaf5aab8cd08e9c51f771da6a51d"
)
_JOURNAL_ROOT_PIN = "0xabb0d484e2b863d1dbdf1736bf4e08f80198ce3547b9150a0c0f3601ca290714"
_FEE_INGRESS_ATOMS_PIN = 125
_AUTHORITY_DETAIL = "receipt verifier is outside the current authority head"
_DEPLOYMENT_DETAIL = "receipt verifier deployment binding mismatch"
_OWNERSHIP_DETAIL = "authority head ownership or invariant validation failed"
_MALFORMED_DETAIL = "candidate ownership or invariant validation failed"
_CALLBACK_DETAIL = "receipt callback rejected or failed"
Reject = ZDEXBuybackSpotReceiptRejectCodeV1


def _digest(data: bytes) -> str:
    return "0x" + hashlib.sha256(data).hexdigest()


def _request(fixture: _Fixture) -> tuple[bytes, str, bytes]:
    return (
        fixture.candidate.receipt.receipt_bytes,
        fixture.spot_release.guest_image_id,
        canonical_global_bytes_v1(fixture.candidate.journal),
    )


def _selection(fixture: _Fixture) -> prep.PreparedZDEXBuybackSpotSelectionV2:
    return prep.prepare_zdex_buyback_spot_safety_selection_v2(fixture.candidate)


def _prepared(
    fixture: _Fixture, head: GlobalEconomicAuthorityHeadV1 | None = None
) -> prep.PreparedZDEXBuybackSpotSafetyReceiptV2:
    return prep.prepare_zdex_buyback_spot_safety_receipt_v2(
        _selection(fixture),
        authority_head=head or fixture.authority_head,
        verifier_binding_root=fixture.receipt_verifier.binding_root,
    )


def _verify(fixture: _Fixture, candidate: Any = None, **overrides: Any) -> Any:
    kwargs: dict[str, Any] = {
        "authority_head": fixture.authority_head,
        "receipt_verifier": fixture.receipt_verifier,
    }
    kwargs.update(overrides)
    return shell.verify_zdex_buyback_spot_safety_receipt_shadow_v2(
        fixture.candidate if candidate is None else candidate, **kwargs
    )


def _prepared_facts(prepared: Any) -> tuple[object, ...]:
    return (
        *(getattr(prepared, name) for name in _PREPARED_FACT_NAMES),
        prepared.profile.profile_id,
        prepared.price_authority.authority_root,
    )


def _marker_facts(marker: Any) -> tuple[object, ...]:
    return (
        marker.journal,
        marker.journal_root,
        marker.journal_digest,
        marker.expected_image_id,
        marker.receipt_digest,
        marker.receipt_kind,
        marker.tokenomics_pre_state,
        marker.spend_policy,
        marker.fee_policy,
        marker.fee_context,
        marker.fee_command,
        marker.fee_ingress.binding_root,
        marker.price_authority_root,
        marker.authority_head_root,
        marker.verifier_binding_root,
        marker.binding_root,
    )


def _ingress_facts(ingress: Any) -> tuple[object, ...]:
    return tuple(getattr(ingress, name) for name in _INGRESS_FIELD_NAMES)


def _verifier_registry(fixture: _Fixture) -> Any:
    with deployment._BOUND_RECEIPT_VERIFIER_LOCK_V1:
        return deployment._BOUND_RECEIPT_VERIFIER_AUTHORITIES_V1[
            fixture.receipt_verifier
        ].verifier_registry


def _assert_rejects(
    run: Callable[[], object],
    code: ZDEXBuybackSpotReceiptRejectCodeV1,
    detail: str,
    fixture: _Fixture,
    *,
    calls: int = 0,
) -> ZDEXBuybackSpotReceiptRejectedV1:
    """Typed rejection with exact code and detail, and an exact backend call count."""

    calls_before = len(fixture.backend.calls)
    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as rejected:
        run()
    assert rejected.value.code is code
    assert str(rejected.value) == f"{code.value}: {detail}"
    assert len(fixture.backend.calls) == calls_before + calls
    return rejected.value


# --- fixtures ----------------------------------------------------------------


def _build_values(record: Any, identity_field: str) -> dict[str, Any]:
    return {
        field.name: getattr(record, field.name)
        for field in dataclass_fields(record)
        if field.name != identity_field
    }


def _rebuild_profile(
    profile: EconomicProfileSnapshotV1,
    *,
    lane_registry: LaneRegistryV1 | None = None,
    route_registry: RouteRegistryV1 | None = None,
) -> EconomicProfileSnapshotV1:
    return EconomicProfileSnapshotV1.build(
        authority_epoch=profile.authority_epoch,
        lane_registry=lane_registry or profile.lane_registry,
        lane_coordinator_registry=profile.lane_coordinator_registry,
        route_registry=route_registry or profile.route_registry,
        proof_shape_root=profile.proof_shape_root,
        root_image_id=profile.root_image_id,
        verifier_registry_root=profile.verifier_registry_root,
        migration_registry_root=profile.migration_registry_root,
        policy_registry_root=profile.policy_registry_root,
        terminal_registry_root=profile.terminal_registry_root,
        status=profile.status,
    )


def _tight_profile(
    fixture: _Fixture, *, route_max_journal_bytes: int, spot_max_journal_bytes: int
) -> tuple[EconomicProfileSnapshotV1, RouteReleaseV1, LaneModuleReleaseV1]:
    """Rebuild the governed profile with only the two journal ceilings changed."""

    profile = fixture.candidate.profile
    spot_values = _build_values(fixture.spot_release, "release_id")
    spot_values["max_journal_bytes"] = spot_max_journal_bytes
    spot = LaneModuleReleaseV1.build(**spot_values)
    releases = tuple(
        spot if item.lane_id is LaneIdV1.SPOT_LIQUIDITY else item
        for item in profile.lane_registry.releases
    )
    route_values = _build_values(fixture.route, "route_release_id")
    route_values["module_release_ids"] = (spot.release_id, fixture.route.module_release_ids[1])
    route_values["max_journal_bytes"] = route_max_journal_bytes
    route = RouteReleaseV1.build(**route_values)
    rebuilt = _rebuild_profile(
        profile, lane_registry=LaneRegistryV1(releases), route_registry=RouteRegistryV1((route,))
    )
    return rebuilt, route, spot


def _rebind_fixture(
    fixture: _Fixture,
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    spot: LaneModuleReleaseV1,
    *,
    receipt_bytes: bytes,
) -> _Fixture:
    """Re-coordinate state, occurrence, fee context, journal, verifier and head."""

    base = fixture.candidate
    state = replace(
        base.global_pre_state,
        profile_root=profile.profile_id,
        lane_roots=tuple(
            replace(row, module_release_id=spot.release_id)
            if row.lane_id is LaneIdV1.SPOT_LIQUIDITY
            else row
            for row in base.global_pre_state.lane_roots
        ),
    )
    occurrence = replace(
        base.occurrence,
        route_release_id=route.route_release_id,
        profile_root=profile.profile_id,
        pre_state_root=state.state_root,
    )
    fee_context = replace(
        base.fee_context,
        profile_root=profile.profile_id,
        allocation_route_release_id=route.route_release_id,
        authorized_buyback_route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
    )
    journal = replace(
        base.journal,
        profile_root=profile.profile_id,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        global_pre_state_root=state.state_root,
        spot_module_release_id=spot.release_id,
        spot_guest_image_id=spot.guest_image_id,
        fee_context_root=hash_global_v1("zdex-fee-allocation-context-v1", fee_context.to_canonical()),
    )
    candidate = replace(
        base,
        profile=profile,
        occurrence=occurrence,
        global_pre_state=state,
        fee_context=fee_context,
        journal=journal,
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes),
    )
    bound = deployment.bind_economic_receipt_verifier_deployment_v1(
        profile=profile,
        verifier_registry=_verifier_registry(fixture),
        selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW,
        evidence_manifest=_verifier_manifest(),
        measured_artifact_bytes=_VERIFIER_ARTIFACT,
        deployment_root=occurrence.deployment_root,
        backend=fixture.backend,
    )
    head = replace(
        fixture.authority_head,
        profile_root=profile.profile_id,
        verifier_binding_root=bound.binding_root,
    )
    return _Fixture(candidate, route, spot, head, bound, fixture.backend)


def _ceiling_fixture(
    *, route_max_journal_bytes: int, spot_max_journal_bytes: int, receipt_bytes: bytes = b"receipt"
) -> _Fixture:
    fixture = _fixture()
    profile, route, spot = _tight_profile(
        fixture,
        route_max_journal_bytes=route_max_journal_bytes,
        spot_max_journal_bytes=spot_max_journal_bytes,
    )
    return _rebind_fixture(fixture, profile, route, spot, receipt_bytes=receipt_bytes)


def _foreign_deployment_verifier(fixture: _Fixture) -> tuple[Any, GlobalEconomicAuthorityHeadV1]:
    """A Bound capability for another deployment root, with a head that names it."""

    bound = deployment.bind_economic_receipt_verifier_deployment_v1(
        profile=fixture.candidate.profile,
        verifier_registry=_verifier_registry(fixture),
        selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW,
        evidence_manifest=_verifier_manifest(),
        measured_artifact_bytes=_VERIFIER_ARTIFACT,
        deployment_root=_root(41),
        backend=fixture.backend,
    )
    return bound, replace(fixture.authority_head, verifier_binding_root=bound.binding_root)


def _malformed_head(fixture: _Fixture) -> GlobalEconomicAuthorityHeadV1:
    head = replace(fixture.authority_head)
    object.__setattr__(head, "generation", "7")
    return head


def _parse(relative: str) -> ast.Module:
    return ast.parse((REPO_ROOT / relative).read_text(encoding="utf-8"), filename=relative)


def _call_names(tree: ast.AST) -> list[str]:
    names: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                names.append(node.func.attr)
            elif isinstance(node.func, ast.Name):
                names.append(node.func.id)
    return names


def _import_targets(tree: ast.AST) -> list[str]:
    targets: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            targets.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            targets.append("." * node.level + (node.module or ""))
    return targets


def _parameter_names(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            args = node.args
            names.update(
                parameter.arg for parameter in (*args.posonlyargs, *args.args, *args.kwonlyargs)
            )
    return names


def _mutant(
    module: object,
    original: Callable[..., object],
    target: str,
    body: str,
    extra: dict[str, object] | None = None,
) -> Any:
    source = inspect.getsource(original)
    assert source.count(target) == 1, "mutant target is no longer unique"
    namespace = dict(vars(module))
    namespace.update(extra or {})
    exec(  # noqa: S102 - deliberate structure-preserving mutant of the boundary
        compile(source.replace(target, body, 1), f"<mutant:{original.__name__}>", "exec"),
        namespace,
    )
    return namespace[original.__name__]


# --- construction conformance ------------------------------------------------


def test_core_and_preparation_modules_have_no_callback_parameter_call_or_shell_import() -> None:
    for relative in (_CORE_MODULE, _PREPARATION_MODULE):
        tree = _parse(relative)
        text = (REPO_ROOT / relative).read_text(encoding="utf-8")
        imports = _import_targets(tree)
        assert not any(name.split(".")[0] in _EFFECT_IMPORT_ROOTS for name in imports), relative
        assert not any(
            "integration" in name.split(".") or name.startswith("..") for name in imports
        ), relative
        assert not (set(_call_names(tree)) & _VERIFIER_CALL_NAMES), relative
        assert "receipt_verifier" not in _parameter_names(tree), relative
        assert "BoundEconomicReceiptVerifierV1" not in text, relative
        assert "ZDEXLaneSuccinctReceiptVerifierV1" not in text, relative
        assert "performs no publication or IO" not in text, relative
    assert not hasattr(core, _MOVED_NAME)
    assert not hasattr(prep, _MOVED_NAME)
    assert not any(name.startswith("verify_") for name in (*core.__all__, *prep.__all__))
    assert all(hasattr(core, name) for name in _RETAINED_CORE_NAMES)
    assert core.VerifiedZDEXBuybackSpotSafetyPurchaseV2.__module__ == core.__name__
    assert prep._build_verified_zdex_buyback_spot_safety_purchase_v2.__module__ == prep.__name__
    assert tuple(
        field.name for field in dataclass_fields(core._VerifiedZDEXBuybackSpotFieldsV2)
    ) == _MARKER_FIELD_NAMES
    assert tuple(
        inspect.signature(prep.prepare_zdex_buyback_spot_safety_selection_v2).parameters
    ) == ("candidate",)
    assert tuple(
        inspect.signature(prep.prepare_zdex_buyback_spot_safety_receipt_v2).parameters
    ) == ("selection", "authority_head", "verifier_binding_root")
    # The prepared record carries raw fee state and roots, never a minted ingress witness.
    prepared_types = {
        field.type for field in dataclass_fields(prep.PreparedZDEXBuybackSpotSafetyReceiptV2)
    }
    assert "VerifiedZDEXFeeIngressSliceV1" not in prepared_types
    assert "fee_ingress" not in {
        field.name for field in dataclass_fields(prep.PreparedZDEXBuybackSpotSafetyReceiptV2)
    }


def test_shell_owns_the_single_bound_callback_and_reads_no_caller_alias_after_io() -> None:
    tree = _parse(_SHELL_MODULE)
    calls = _call_names(tree)
    assert calls.count("verify_profile_lane_receipt") == 1
    assert calls.count("verify_succinct_receipt") == 0
    assert calls.count("require_binding") == 1
    assert all(
        not name.startswith("..") or name.startswith("..core") for name in _import_targets(tree)
    )
    assert shell.__all__ == [_MOVED_NAME]
    assert tuple(
        inspect.signature(shell.verify_zdex_buyback_spot_safety_receipt_shadow_v2).parameters
    ) == ("candidate", "authority_head", "receipt_verifier")
    # After the exact head/Bound gates the public path never touches the caller head,
    # candidate or verifier identity again; execution mints from the executed copy only.
    source = inspect.getsource(shell.verify_zdex_buyback_spot_safety_receipt_shadow_v2)
    tail = source[source.index("    prepared = prepare_zdex_buyback_spot_safety_receipt_v2(") :]
    assert "authority_head=owned_head" in tail
    assert "authority_head," not in tail and "authority_head)" not in tail
    assert "candidate" not in tail
    executor = inspect.getsource(shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2)
    executor_tail = executor[executor.index("    except Exception:") :]
    assert "prepared" not in executor_tail
    assert "_build_verified_zdex_buyback_spot_safety_purchase_v2(owned)" in executor_tail


# --- pure preparation -------------------------------------------------------


def test_selection_phase_owns_the_candidate_and_selects_releases_with_no_verifier() -> None:
    # Arrange
    fixture = _fixture()

    # Act: prepare twice with no verifier anywhere.
    first = _selection(fixture)
    second = _selection(fixture)

    # Assert: exact typed data, identical decision, releases are the profile's own.
    assert type(first) is prep.PreparedZDEXBuybackSpotSelectionV2
    assert first == second
    assert first.route == fixture.route
    assert first.spot_release == fixture.spot_release
    assert first.tokenomics_release == fixture.candidate.profile.lane_registry.release_for(
        LaneIdV1.ZDEX_TOKENOMICS
    )
    assert first.owned.profile == fixture.candidate.profile
    assert first.owned.profile is not fixture.candidate.profile
    assert first.owned.journal is not fixture.candidate.journal
    assert first.route is not fixture.route
    assert fixture.backend.calls == []
    # Caller-graph mutation after phase 1 does not reach the owned subject.
    object.__setattr__(fixture.candidate.journal, "quote_amount_in_atoms", 1)
    object.__setattr__(fixture.candidate.profile, "profile_id", _root(90_001))
    snapshot = prep.snapshot_prepared_zdex_buyback_spot_selection_v2(first)
    assert first == snapshot
    assert snapshot is not first
    assert first.owned.journal.quote_amount_in_atoms == 125


def test_receipt_phase_is_deterministic_complete_and_reproduces_the_pinned_marker() -> None:
    # Arrange
    fixture = _fixture()
    candidate = fixture.candidate

    # Act
    first = _prepared(fixture)
    second = _prepared(fixture)

    # Assert: exact request, digests bound to bytes, pre-I/O roots, no callback.
    assert type(first) is prep.PreparedZDEXBuybackSpotSafetyReceiptV2
    assert _prepared_facts(first) == _prepared_facts(second)
    assert (first.receipt_bytes, first.expected_image_id, first.expected_journal_bytes) == (
        _request(fixture)
    )
    assert first.expected_module_release_id == fixture.spot_release.release_id
    assert first.expected_image_id == _EXPECTED_IMAGE_PIN
    assert first.expected_image_id != fixture.route.guest_image_id
    assert len(first.expected_journal_bytes) == _JOURNAL_LEN_PIN
    assert first.journal_digest == _digest(first.expected_journal_bytes) == _JOURNAL_DIGEST_PIN
    assert first.receipt_digest == _digest(first.receipt_bytes) == _RECEIPT_DIGEST_PIN
    assert first.receipt_kind is ReceiptKindV1.SUCCINCT
    assert first.journal == candidate.journal and first.journal is not candidate.journal
    assert first.profile == candidate.profile and first.profile is not candidate.profile
    assert first.authority_head == fixture.authority_head
    assert first.authority_head is not fixture.authority_head
    assert first.authority_head_root == _HEAD_ROOT_PIN
    assert first.verifier_binding_root == _VERIFIER_BINDING_ROOT_PIN
    assert first.price_authority_root == _PRICE_AUTHORITY_ROOT_PIN
    assert first.price_authority.authority_root == _PRICE_AUTHORITY_ROOT_PIN
    assert first.fee_state == candidate.tokenomics_pre_state.fee_state_for(
        candidate.journal.quote_asset_id
    )
    assert first.fee_state.fee_ingress_atoms == _FEE_INGRESS_ATOMS_PIN
    assert first.command_occurrence_id == candidate.occurrence.occurrence_id
    assert first.global_pre_state_root == candidate.global_pre_state.state_root
    assert first.profile_root == candidate.profile.profile_id
    assert not hasattr(first, "fee_ingress")
    assert fixture.backend.calls == []
    # The private factory mints the identical marker the old path produced.
    marker = prep._build_verified_zdex_buyback_spot_safety_purchase_v2(first)
    assert type(marker) is core.VerifiedZDEXBuybackSpotSafetyPurchaseV2
    assert marker.binding_root == _BINDING_ROOT_PIN
    assert marker.journal_root == _JOURNAL_ROOT_PIN
    assert marker.fee_ingress.binding_root == _FEE_INGRESS_BINDING_ROOT_PIN
    assert _ingress_facts(marker.fee_ingress) == (
        candidate.occurrence.occurrence_id,
        candidate.global_pre_state.state_root,
        candidate.profile.profile_id,
        first.fee_state.state_root,
        candidate.journal.quote_asset_id,
        _FEE_INGRESS_ATOMS_PIN,
        _HEAD_ROOT_PIN,
        _VERIFIER_BINDING_ROOT_PIN,
    )
    assert marker.fee_command.fee_charged_atoms == marker.fee_ingress.fee_ingress_atoms
    assert fixture.backend.calls == []


def test_prepared_subject_is_detached_from_candidate_head_and_selection_graphs() -> None:
    fixture = _fixture()
    head = replace(fixture.authority_head)
    selection = _selection(fixture)
    prepared = prep.prepare_zdex_buyback_spot_safety_receipt_v2(
        selection, authority_head=head, verifier_binding_root=fixture.receipt_verifier.binding_root
    )
    facts = _prepared_facts(prepared)

    object.__setattr__(fixture.candidate.journal, "quote_amount_in_atoms", 1)
    object.__setattr__(fixture.candidate.profile, "profile_id", _root(90_002))
    object.__setattr__(fixture.candidate.receipt, "receipt_bytes", b"mutated")
    object.__setattr__(fixture.candidate.fee_context, "policy_root", _root(90_003))
    object.__setattr__(head, "generation", 5)
    object.__setattr__(selection.owned.journal, "purchased_zdex_atoms", 1)
    object.__setattr__(selection.owned.profile, "authority_epoch", 99)
    snapshot = prep.snapshot_prepared_zdex_buyback_spot_safety_receipt_v2(prepared)

    assert _prepared_facts(prepared) == facts
    assert _prepared_facts(snapshot) == facts
    assert snapshot is not prepared
    assert snapshot.journal is not prepared.journal
    assert snapshot.profile is not prepared.profile
    assert snapshot.fee_state is not prepared.fee_state
    assert snapshot.tokenomics_pre_state is not prepared.tokenomics_pre_state
    assert snapshot.price_authority is not prepared.price_authority
    assert snapshot.price_authority.price_safety is not prepared.price_authority.price_safety
    assert snapshot.authority_head is not prepared.authority_head
    assert snapshot.authority_head == prepared.authority_head
    assert prepared.authority_head is not head
    assert prepared.authority_head_root == _HEAD_ROOT_PIN
    assert prepared.authority_head.authority_root == _HEAD_ROOT_PIN
    assert head.authority_root != _HEAD_ROOT_PIN


def _forge(prepared: Any, **changes: Any) -> Any:
    """Copy a prepared record past its constructor with deliberately malformed fields."""

    forged = object.__new__(type(prepared))
    for field in dataclass_fields(prepared):
        object.__setattr__(forged, field.name, changes.get(field.name, getattr(prepared, field.name)))
    return forged


def _inconsistent_records(
    prepared: prep.PreparedZDEXBuybackSpotSafetyReceiptV2, fixture: _Fixture
) -> tuple[tuple[str, Any, type[Exception], str], ...]:
    class _Forged(prep.PreparedZDEXBuybackSpotSafetyReceiptV2):
        pass

    values = {field.name: getattr(prepared, field.name) for field in dataclass_fields(prepared)}
    return (
        ("forged_subclass", _Forged(**values), TypeError, "must be exact typed data"),
        ("not_a_record", object(), TypeError, "must be exact typed data"),
        ("selection_record", _selection(fixture), TypeError, "must be exact typed data"),
        (
            "hostile_image",
            _forge(prepared, expected_image_id=_HostileRoot(prepared.expected_image_id)),
            TypeError,
            "expected_image_id must be exact str",
        ),
        (
            "open_kind",
            _forge(prepared, receipt_kind="SUCCINCT"),
            TypeError,
            "receipt kind must be exact typed data",
        ),
        (
            "bytearray_receipt",
            _forge(prepared, receipt_bytes=bytearray(prepared.receipt_bytes)),
            TypeError,
            "receipt bytes must be exact typed data",
        ),
        (
            "short_head_root",
            _forge(prepared, authority_head_root="0x12"),
            ValueError,
            "authority_head_root",
        ),
        (
            "open_authority_head",
            _forge(prepared, authority_head=object()),
            TypeError,
            "authority head must be exact typed data",
        ),
        (
            "wrong_receipt_digest",
            replace(prepared, receipt_digest=_root(1)),
            ValueError,
            "receipt digest mismatch",
        ),
        (
            "wrong_journal_bytes",
            replace(prepared, expected_journal_bytes=prepared.expected_journal_bytes + b" "),
            ValueError,
            "journal bytes mismatch",
        ),
        (
            "wrong_journal_digest",
            replace(prepared, journal_digest=_root(2)),
            ValueError,
            "journal digest mismatch",
        ),
        (
            "route_image_request",
            replace(prepared, expected_image_id=fixture.route.guest_image_id),
            ValueError,
            "request image is outside the profile",
        ),
        (
            "foreign_occurrence_root",
            replace(prepared, command_occurrence_id=_root(3)),
            ValueError,
            "ingress roots are outside the journal",
        ),
        (
            "foreign_profile_root",
            replace(prepared, profile_root=_root(4)),
            ValueError,
            "ingress roots are outside the journal",
        ),
        (
            "wrong_price_authority_root",
            replace(prepared, price_authority_root=_root(5)),
            ValueError,
            "price authority root mismatch",
        ),
        (
            "foreign_fee_state",
            replace(prepared, fee_state=replace(prepared.fee_state, fee_ingress_atoms=126)),
            ValueError,
            "fee state is outside the tokenomics pre-state",
        ),
    )


def test_prepared_record_requires_exact_types_and_request_to_marker_binding() -> None:
    fixture = _fixture()
    prepared = _prepared(fixture)

    for label, subject, error, message in _inconsistent_records(prepared, fixture):
        # These values intentionally cross the typed boundary malformed.
        untyped_subject: Any = subject
        with pytest.raises(error, match=message):
            prep.snapshot_prepared_zdex_buyback_spot_safety_receipt_v2(untyped_subject)
        with pytest.raises(error, match=message):
            prep._build_verified_zdex_buyback_spot_safety_purchase_v2(untyped_subject)
        with pytest.raises(error, match=message):
            shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(
                untyped_subject, fixture.receipt_verifier
            )
        assert fixture.backend.calls == [], label
    with pytest.raises(TypeError, match="selection must be exact typed data"):
        prep.snapshot_prepared_zdex_buyback_spot_selection_v2(cast(Any, prepared))
    with pytest.raises(TypeError, match="selection must be exact typed data"):
        prep.prepare_zdex_buyback_spot_safety_receipt_v2(
            cast(Any, prepared),
            authority_head=fixture.authority_head,
            verifier_binding_root=fixture.receipt_verifier.binding_root,
        )
    with pytest.raises(TypeError, match="must be a bound capability"):
        shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(prepared, cast(Any, object()))
    assert fixture.backend.calls == []


def test_pure_authority_predicates_keep_the_former_code_detail_and_order() -> None:
    fixture = _fixture()
    selection = _selection(fixture)
    head = fixture.authority_head
    bound = fixture.receipt_verifier
    head_mutants = (
        replace(head, status=GlobalEconomicAuthorityStatusV1.REVOKED),
        replace(head, chain_id="other-chain"),
        replace(head, deployment_root=_root(70_101)),
        replace(head, profile_root=_root(70_102)),
        replace(head, writer_epoch=head.writer_epoch + 1),
        replace(head, verifier_registry_root=_root(70_103)),
    )
    for mutant in head_mutants:
        _assert_rejects(
            partial(prep.require_zdex_buyback_spot_authority_head_v2, selection, mutant),
            Reject.AUTHORITY_BINDING_MISMATCH,
            _AUTHORITY_DETAIL,
            fixture,
        )
    prep.require_zdex_buyback_spot_authority_head_v2(selection, head)
    identity_mutants: tuple[tuple[Any, Any, Any], ...] = (
        (head, _root(70_104), bound.binding_root),
        (head, bound.release_id, _root(70_105)),
        (head, _HostileRoot(bound.release_id), bound.binding_root),
        (head, bound.release_id, _HostileRoot(bound.binding_root)),
        (replace(head, root_image_id=_root(70_106)), bound.release_id, bound.binding_root),
    )
    for identity_head, release_id, binding_root in identity_mutants:
        _assert_rejects(
            partial(
                prep.require_zdex_buyback_spot_verifier_identity_v2,
                selection,
                identity_head,
                verifier_release_id=release_id,
                verifier_binding_root=binding_root,
            ),
            Reject.AUTHORITY_BINDING_MISMATCH,
            _AUTHORITY_DETAIL,
            fixture,
        )
    prep.require_zdex_buyback_spot_verifier_identity_v2(
        selection, head, verifier_release_id=bound.release_id, verifier_binding_root=bound.binding_root
    )
    # Phase 2 re-applies the head predicates and refuses a binding root outside the head.
    _assert_rejects(
        lambda: prep.prepare_zdex_buyback_spot_safety_receipt_v2(
            selection, authority_head=head, verifier_binding_root=_root(70_107)
        ),
        Reject.AUTHORITY_BINDING_MISMATCH,
        _AUTHORITY_DETAIL,
        fixture,
    )
    _assert_rejects(
        lambda: prep.prepare_zdex_buyback_spot_safety_receipt_v2(
            selection, authority_head=head_mutants[0], verifier_binding_root=bound.binding_root
        ),
        Reject.AUTHORITY_BINDING_MISMATCH,
        _AUTHORITY_DETAIL,
        fixture,
    )
    # The pure head snapshot reruns the head's own checks on exact-typed malformed data.
    with pytest.raises(TypeError, match="generation must be an exact integer"):
        prep.snapshot_zdex_buyback_spot_authority_head_v2(_malformed_head(fixture))
    with pytest.raises(TypeError, match="authority head must be exact typed data"):
        prep.snapshot_zdex_buyback_spot_authority_head_v2(cast(Any, object()))


# --- shell execution ---------------------------------------------------------


def test_shell_executes_exactly_the_prepared_request_once_and_mints_the_pinned_marker() -> None:
    # Arrange
    fixture = _fixture()
    prepared = _prepared(fixture)
    expected_marker = _marker_facts(prep._build_verified_zdex_buyback_spot_safety_purchase_v2(prepared))
    assert fixture.backend.calls == []

    # Act
    marker = _verify(fixture)

    # Assert: one call, exact request, marker minted from exactly those bytes and fields.
    assert fixture.backend.calls == [_request(fixture)]
    assert fixture.backend.calls == [
        (prepared.receipt_bytes, prepared.expected_image_id, prepared.expected_journal_bytes)
    ]
    assert type(marker) is core.VerifiedZDEXBuybackSpotSafetyPurchaseV2
    assert _marker_facts(marker) == expected_marker
    assert marker.receipt_digest == _digest(fixture.backend.calls[0][0]) == _RECEIPT_DIGEST_PIN
    assert marker.expected_image_id == fixture.backend.calls[0][1] == _EXPECTED_IMAGE_PIN
    assert marker.journal_digest == _digest(fixture.backend.calls[0][2]) == _JOURNAL_DIGEST_PIN
    assert marker.binding_root == _BINDING_ROOT_PIN
    assert marker.authority_head_root == _HEAD_ROOT_PIN
    assert marker.verifier_binding_root == _VERIFIER_BINDING_ROOT_PIN
    assert marker.price_authority_root == _PRICE_AUTHORITY_ROOT_PIN
    assert marker.fee_ingress.binding_root == _FEE_INGRESS_BINDING_ROOT_PIN
    assert marker.fee_command.fee_charged_atoms == _FEE_INGRESS_ATOMS_PIN
    assert marker.journal == fixture.candidate.journal
    assert marker.journal is not fixture.candidate.journal
    with pytest.raises(AttributeError, match="immutable"):
        marker._fields = cast(Any, object())


def _guard_subject(fixture: _Fixture, label: str) -> tuple[Any, dict[str, Any]]:
    """Build one- and two-defect subjects; the earlier phase must reject first."""

    candidate: Any = fixture.candidate
    kwargs: dict[str, Any] = {}
    if "not_a_candidate" in label:
        candidate = object()
    if "zero_routes" in label:
        profile = _rebuild_profile(fixture.candidate.profile, route_registry=RouteRegistryV1(()))
        candidate = replace(candidate, profile=profile)
    if "swapped_lanes" in label:
        values = _build_values(fixture.route, "route_release_id")
        values["ordered_lanes"] = (LaneIdV1.ZDEX_TOKENOMICS, LaneIdV1.SPOT_LIQUIDITY)
        values["module_release_ids"] = tuple(reversed(fixture.route.module_release_ids))
        profile = _rebuild_profile(
            fixture.candidate.profile, route_registry=RouteRegistryV1((RouteReleaseV1.build(**values),))
        )
        candidate = replace(candidate, profile=profile)
    if "head_not_exact" in label:
        kwargs["authority_head"] = object()
    if "malformed_head" in label:
        kwargs["authority_head"] = _malformed_head(fixture)
    if "verifier_not_bound" in label:
        kwargs["receipt_verifier"] = object()
    if "revoked_head" in label:
        kwargs["authority_head"] = replace(
            fixture.authority_head, status=GlobalEconomicAuthorityStatusV1.REVOKED
        )
    if "stale_head" in label:
        kwargs["authority_head"] = replace(fixture.authority_head, profile_root=_root(70_000))
    if "foreign_deployment" in label:
        bound, head = _foreign_deployment_verifier(fixture)
        kwargs["receipt_verifier"] = bound
        kwargs["authority_head"] = head
    if "spend_policy" in label:
        candidate = replace(
            candidate,
            spend_policy=replace(fixture.candidate.spend_policy, per_command_quote_cap_atoms=201),
        )
    if "writer_epoch" in label:
        candidate = replace(candidate, journal=replace(candidate.journal, writer_epoch=12))
    if "reserve_claim" in label:
        candidate = replace(candidate, journal=replace(candidate.journal, quote_reserve_atoms=999))
    if "oracle_payload" in label:
        candidate = replace(
            candidate, journal=replace(candidate.journal, oracle_quote_numerator_atoms=2)
        )
    if "price_envelope" in label:
        candidate = replace(candidate, journal=replace(candidate.journal, purchased_zdex_atoms=110))
    if "composite_kind" in label:
        candidate = replace(
            candidate,
            receipt=ZDEXBuybackSpotReceiptEnvelopeV1(
                ReceiptKindV1.COMPOSITE, b"" if "empty" in label else b"composite"
            ),
        )
    elif "empty" in label:
        candidate = replace(
            candidate, receipt=ZDEXBuybackSpotReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"")
        )
    return candidate, kwargs


_POLICY_DETAIL = "journal resources are outside the governed buyback policy"
_OCCURRENCE_DETAIL = "journal occurrence or release coordinate mismatch"
_RESERVE_DETAIL = "RESERVE_AMOUNT_MISMATCH: committed reserve amount mismatch"
_ORACLE_DETAIL = "Oracle occurrence root does not commit the exact price payload"
_KIND_DETAIL = "only Succinct receipts are admissible"
_EMPTY_DETAIL = "receipt bytes must be nonempty"
# (label, code, exact detail or None, pure phase that reproduces the rejection)
_GUARDS = (
    ("not_a_candidate", Reject.MALFORMED_CANDIDATE, _MALFORMED_DETAIL, "selection"),
    ("not_a_candidate_with_head_not_exact", Reject.MALFORMED_CANDIDATE, _MALFORMED_DETAIL, "selection"),
    ("zero_routes", Reject.GOVERNED_ROUTE_MISMATCH, "profile must select exactly one buyback route", "selection"),
    ("swapped_lanes", Reject.GOVERNED_ROUTE_MISMATCH, "buyback route shape or status mismatch", "selection"),
    ("swapped_lanes_with_verifier_not_bound", Reject.GOVERNED_ROUTE_MISMATCH, "buyback route shape or status mismatch", "selection"),
    ("head_not_exact", Reject.AUTHORITY_BINDING_MISMATCH, _AUTHORITY_DETAIL, "shell"),
    ("head_not_exact_with_verifier_not_bound", Reject.AUTHORITY_BINDING_MISMATCH, _AUTHORITY_DETAIL, "shell"),
    ("verifier_not_bound", Reject.AUTHORITY_BINDING_MISMATCH, _AUTHORITY_DETAIL, "shell"),
    # Paired baseline case: a malformed exact head with a non-Bound verifier keeps the
    # former compound's second term and its detail.
    ("malformed_head_with_verifier_not_bound", Reject.AUTHORITY_BINDING_MISMATCH, _AUTHORITY_DETAIL, "shell"),
    # Named strengthening (recorded for root): at base a malformed exact head with a
    # valid Bound capability reached the callback and minted; ownership now fails closed.
    ("malformed_head", Reject.AUTHORITY_BINDING_MISMATCH, _OWNERSHIP_DETAIL, "shell"),
    ("revoked_head", Reject.AUTHORITY_BINDING_MISMATCH, _AUTHORITY_DETAIL, "head"),
    ("revoked_head_then_spend_policy", Reject.AUTHORITY_BINDING_MISMATCH, _AUTHORITY_DETAIL, "head"),
    ("stale_head", Reject.AUTHORITY_BINDING_MISMATCH, _AUTHORITY_DETAIL, "head"),
    ("foreign_deployment", Reject.AUTHORITY_BINDING_MISMATCH, _DEPLOYMENT_DETAIL, "shell"),
    ("foreign_deployment_then_spend_policy", Reject.AUTHORITY_BINDING_MISMATCH, _DEPLOYMENT_DETAIL, "shell"),
    ("spend_policy", Reject.GOVERNED_POLICY_MISMATCH, _POLICY_DETAIL, "receipt"),
    ("spend_policy_then_writer_epoch", Reject.GOVERNED_POLICY_MISMATCH, _POLICY_DETAIL, "receipt"),
    ("writer_epoch", Reject.OCCURRENCE_BINDING_MISMATCH, _OCCURRENCE_DETAIL, "receipt"),
    ("writer_epoch_then_reserve_claim", Reject.OCCURRENCE_BINDING_MISMATCH, _OCCURRENCE_DETAIL, "receipt"),
    ("reserve_claim", Reject.STATE_ROOT_BINDING_MISMATCH, _RESERVE_DETAIL, "receipt"),
    ("reserve_claim_then_composite_kind", Reject.STATE_ROOT_BINDING_MISMATCH, _RESERVE_DETAIL, "receipt"),
    ("oracle_payload", Reject.ORACLE_BINDING_MISMATCH, _ORACLE_DETAIL, "receipt"),
    ("price_envelope", Reject.PRICE_SAFETY_REJECTED, None, "receipt"),
    ("price_envelope_then_empty", Reject.PRICE_SAFETY_REJECTED, None, "receipt"),
    ("composite_kind", Reject.UNSUPPORTED_RECEIPT_KIND, _KIND_DETAIL, "receipt"),
    ("composite_kind_empty", Reject.UNSUPPORTED_RECEIPT_KIND, _KIND_DETAIL, "receipt"),
    ("empty", Reject.EMPTY_RECEIPT, _EMPTY_DETAIL, "receipt"),
)


def _pure_phase_rejection(
    phase: str, fixture: _Fixture, candidate: Any, kwargs: dict[str, Any]
) -> ZDEXBuybackSpotReceiptRejectedV1 | None:
    """Reproduce the rejection with the responsible pure phase and no verifier."""

    if phase == "shell":
        return None
    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as pure:
        if phase == "selection":
            prep.prepare_zdex_buyback_spot_safety_selection_v2(candidate)
        elif phase == "head":
            prep.require_zdex_buyback_spot_authority_head_v2(
                prep.prepare_zdex_buyback_spot_safety_selection_v2(candidate),
                kwargs["authority_head"],
            )
        else:
            prep.prepare_zdex_buyback_spot_safety_receipt_v2(
                prep.prepare_zdex_buyback_spot_safety_selection_v2(candidate),
                authority_head=fixture.authority_head,
                verifier_binding_root=fixture.receipt_verifier.binding_root,
            )
    return pure.value


@pytest.mark.parametrize(("label", "code", "detail", "phase"), _GUARDS)
def test_every_guard_rejects_before_the_callback_with_no_marker(
    label: str, code: ZDEXBuybackSpotReceiptRejectCodeV1, detail: str | None, phase: str
) -> None:
    fixture = _fixture()
    candidate, kwargs = _guard_subject(fixture, label)

    # Act / Assert: the shell rejects with the exact code and detail and no backend call.
    calls_before = len(fixture.backend.calls)
    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as rejected:
        _verify(fixture, candidate, **kwargs)
    assert rejected.value.code is code
    if detail is not None:
        assert str(rejected.value) == f"{code.value}: {detail}"
    assert len(fixture.backend.calls) == calls_before
    # The same rejection is reproduced by the responsible pure phase with no verifier.
    pure = _pure_phase_rejection(phase, fixture, candidate, kwargs)
    if pure is not None:
        assert pure.code is code
        assert str(pure) == str(rejected.value)
    assert fixture.backend.calls[calls_before:] == []


@pytest.mark.parametrize(
    "receipt_kind",
    (ReceiptKindV1.COMPOSITE, ReceiptKindV1.CONDITIONAL, ReceiptKindV1.FAKE, ReceiptKindV1.DEVELOPMENT),
)
def test_only_succinct_receipts_are_admissible(receipt_kind: ReceiptKindV1) -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate, receipt=ZDEXBuybackSpotReceiptEnvelopeV1(receipt_kind, b"inadmissible")
    )
    _assert_rejects(
        lambda: _verify(fixture, candidate),
        Reject.UNSUPPORTED_RECEIPT_KIND,
        "only Succinct receipts are admissible",
        fixture,
    )


@pytest.mark.parametrize("reply", (False, 0, b"", True, object(), b"ok"))
def test_bound_exact_none_contract_rejects_every_non_none_reply_after_one_call(reply: object) -> None:
    fixture = _fixture()
    fixture.backend.result = reply

    _assert_rejects(
        lambda: _verify(fixture), Reject.RECEIPT_VERIFICATION_FAILED, _CALLBACK_DETAIL, fixture, calls=1
    )
    assert fixture.backend.calls == [_request(fixture)]


def test_backend_exception_rejects_after_one_call_without_leaking_backend_detail() -> None:
    fixture = _fixture()
    fixture.backend.error = RuntimeError("backend details must not escape")

    rejected = _assert_rejects(
        lambda: _verify(fixture), Reject.RECEIPT_VERIFICATION_FAILED, _CALLBACK_DETAIL, fixture, calls=1
    )
    assert "backend details" not in str(rejected)
    assert fixture.backend.calls == [_request(fixture)]
    # The same subject succeeds once the backend recovers, so admission was never the cause.
    fixture.backend.error = None
    assert _verify(fixture).binding_root == _BINDING_ROOT_PIN
    assert len(fixture.backend.calls) == 2


def test_bound_authority_source_mutation_during_callback_still_fails_its_own_recheck() -> None:
    fixture = _fixture()
    bound = fixture.receipt_verifier
    registry = deployment._BOUND_RECEIPT_VERIFIER_AUTHORITIES_V1
    with deployment._BOUND_RECEIPT_VERIFIER_LOCK_V1:
        original_authority = registry[bound]
    other_backend = type(fixture.backend)()

    def swap(*_: object) -> None:
        with deployment._BOUND_RECEIPT_VERIFIER_LOCK_V1:
            registry[bound] = replace(
                original_authority,
                backend=other_backend,
                verify_call=other_backend.verify_succinct_receipt,
            )

    fixture.backend.hook = swap
    try:
        _assert_rejects(
            lambda: _verify(fixture), Reject.RECEIPT_VERIFICATION_FAILED, _CALLBACK_DETAIL, fixture, calls=1
        )
    finally:
        fixture.backend.hook = None
        with deployment._BOUND_RECEIPT_VERIFIER_LOCK_V1:
            registry[bound] = original_authority
    assert fixture.backend.calls == [_request(fixture)]
    assert other_backend.calls == []


@pytest.mark.parametrize(
    ("route_max", "spot_max", "admitted"),
    (
        (_JOURNAL_LEN_PIN, 65_536, True),
        (65_536, _JOURNAL_LEN_PIN, True),
        (_JOURNAL_LEN_PIN, _JOURNAL_LEN_PIN, True),
        (_JOURNAL_LEN_PIN - 1, 65_536, False),
        (65_536, _JOURNAL_LEN_PIN - 1, False),
        (_JOURNAL_LEN_PIN - 1, _JOURNAL_LEN_PIN, False),
        (_JOURNAL_LEN_PIN, _JOURNAL_LEN_PIN - 1, False),
    ),
)
def test_journal_ceiling_is_the_route_spot_minimum_with_equality_admitted(
    route_max: int, spot_max: int, admitted: bool
) -> None:
    # Arrange: a receipt longer than the ceiling shows the ceiling bounds the journal only.
    long_receipt = b"r" * (_JOURNAL_LEN_PIN + 1)
    fixture = _ceiling_fixture(
        route_max_journal_bytes=route_max, spot_max_journal_bytes=spot_max, receipt_bytes=long_receipt
    )
    assert fixture.route.max_journal_bytes == route_max
    assert fixture.spot_release.max_journal_bytes == spot_max
    assert len(canonical_global_bytes_v1(fixture.candidate.journal)) == _JOURNAL_LEN_PIN

    # Act / Assert
    if admitted:
        prepared = _prepared(fixture)
        assert len(prepared.expected_journal_bytes) == _JOURNAL_LEN_PIN
        marker = _verify(fixture)
        assert fixture.backend.calls == [_request(fixture)]
        assert marker.receipt_digest == _digest(long_receipt)
        assert marker.expected_image_id == fixture.spot_release.guest_image_id
        return
    _assert_rejects(
        lambda: _prepared(fixture),
        Reject.JOURNAL_TOO_LARGE,
        "canonical journal exceeds the selected release ceiling",
        fixture,
    )
    _assert_rejects(
        lambda: _verify(fixture),
        Reject.JOURNAL_TOO_LARGE,
        "canonical journal exceeds the selected release ceiling",
        fixture,
    )
    # Paired failures: empty receipt bytes reject before the over-ceiling journal.
    empty_and_over = replace(
        fixture.candidate, receipt=ZDEXBuybackSpotReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"")
    )
    _assert_rejects(
        lambda: _verify(fixture, empty_and_over),
        Reject.EMPTY_RECEIPT,
        "receipt bytes must be nonempty",
        fixture,
    )


# --- alias isolation and lifecycle ------------------------------------------


def test_callback_mutation_of_candidate_and_head_aliases_cannot_relabel_marker() -> None:
    # Arrange: the callback mutates every caller-held alias the shell was given.
    fixture = _fixture()
    candidate = fixture.candidate
    head = fixture.authority_head
    fee_state = candidate.tokenomics_pre_state.fee_state_for(candidate.journal.quote_asset_id)

    def mutate(receipt_bytes: bytes, image_id: str, journal_bytes: bytes) -> None:
        assert (receipt_bytes, image_id, journal_bytes) == _request(fixture)
        object.__setattr__(candidate.journal, "quote_amount_in_atoms", 1)
        object.__setattr__(candidate.journal, "spot_guest_image_id", _root(99_001))
        object.__setattr__(candidate.profile, "profile_id", _root(99_002))
        object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated")
        object.__setattr__(candidate.fee_context, "policy_root", _root(99_003))
        object.__setattr__(candidate.spend_policy, "per_command_quote_cap_atoms", 1)
        object.__setattr__(fee_state, "fee_ingress_atoms", 1)
        object.__setattr__(head, "generation", 7)
        object.__setattr__(head, "activation_id", _root(99_004))
        object.__setattr__(head, "profile_root", _root(99_005))

    fixture.backend.hook = mutate
    try:
        marker = _verify(fixture)
    finally:
        fixture.backend.hook = None

    # Assert: the marker carries the pre-I/O owned subject and head, not the aliases.
    assert head.authority_root != _HEAD_ROOT_PIN
    assert marker.authority_head_root == _HEAD_ROOT_PIN
    assert marker.verifier_binding_root == _VERIFIER_BINDING_ROOT_PIN
    assert marker.fee_ingress.authority_head_root == _HEAD_ROOT_PIN
    assert marker.fee_ingress.profile_root == marker.journal.profile_root
    assert marker.fee_ingress.fee_ingress_atoms == _FEE_INGRESS_ATOMS_PIN
    assert marker.fee_command.fee_charged_atoms == _FEE_INGRESS_ATOMS_PIN
    assert marker.journal.quote_amount_in_atoms == 125
    assert marker.expected_image_id == _EXPECTED_IMAGE_PIN
    assert marker.receipt_digest == _RECEIPT_DIGEST_PIN
    assert marker.spend_policy.per_command_quote_cap_atoms == 200
    assert marker.binding_root == _BINDING_ROOT_PIN


def test_callback_mutation_of_the_caller_held_prepared_alias_cannot_relabel_marker() -> None:
    # Arrange: the caller keeps the prepared alias and forges every marker source.
    fixture = _fixture()
    prepared = _prepared(fixture)
    expected_facts = _prepared_facts(prepared)
    forged_journal = replace(prepared.journal, quote_amount_in_atoms=1)
    forged_fee_state = replace(prepared.fee_state, fee_ingress_atoms=1)

    def mutate(*_: object) -> None:
        object.__setattr__(prepared, "journal", forged_journal)
        object.__setattr__(prepared, "journal_digest", _digest(b"mutated-journal"))
        object.__setattr__(prepared, "expected_image_id", _root(78_502))
        object.__setattr__(prepared, "receipt_bytes", b"mutated-leaf")
        object.__setattr__(prepared, "receipt_digest", _digest(b"mutated-leaf"))
        object.__setattr__(prepared, "authority_head_root", _root(78_504))
        object.__setattr__(prepared, "verifier_binding_root", _root(78_505))
        object.__setattr__(prepared, "fee_state", forged_fee_state)
        object.__setattr__(prepared, "profile_root", _root(78_506))

    fixture.backend.hook = mutate
    try:
        marker = shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(
            prepared, fixture.receipt_verifier
        )
    finally:
        fixture.backend.hook = None

    # Assert: the marker is the executed subject, not the mutated alias.
    assert fixture.backend.calls == [_request(fixture)]
    assert _marker_facts(marker) == _marker_facts(
        prep._build_verified_zdex_buyback_spot_safety_purchase_v2(_prepared(fixture))
    )
    assert marker.binding_root == _BINDING_ROOT_PIN
    assert prepared.authority_head_root == _root(78_504)
    assert _prepared_facts(_prepared(fixture)) == expected_facts
    assert not any(name.startswith("bind_") for name in (*shell.__all__, *prep.__all__))


def _witness_fields(witness: Any) -> Any:
    return object.__getattribute__(witness, "_fields")


def _forged_witness(witness: Any, **changes: Any) -> Any:
    """Copy an opaque witness past its constructor with substituted private fields."""

    forged = object.__new__(type(witness))
    object.__setattr__(forged, "_fields", replace(_witness_fields(witness), **changes))
    return forged


def _mutate_price_witness_aliases(authority: Any) -> Callable[[], None]:
    """Relabel a retained price authority and its nested price safety in place.

    Returns the restorer.  Both witnesses are relabelled through their private
    slot exactly as a callback holding the prepared alias could do.
    """

    safety = authority.price_safety
    authority_fields = _witness_fields(authority)
    safety_fields = _witness_fields(safety)
    object.__setattr__(
        safety, "_fields", replace(safety_fields, route_safe_quote_limit_atoms=1, minimum_output_atoms=1)
    )
    object.__setattr__(
        authority,
        "_fields",
        replace(authority_fields, execution_policy_root=_root(78_601), price_safety=safety),
    )

    def restore() -> None:
        object.__setattr__(safety, "_fields", safety_fields)
        object.__setattr__(authority, "_fields", authority_fields)

    return restore


def test_callback_mutation_of_retained_price_witness_aliases_cannot_relabel_or_reject(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Named law for root's draft finding: both price witnesses are owned before I/O.

    A callback that relabels the retained ``prepared.price_authority`` private
    fields, or the nested price-safety fields, neither changes the completed
    marker nor produces a post-callback rejection.
    """

    # Arrange: the caller-held prepared alias on the private executor path.
    fixture = _fixture()
    prepared = _prepared(fixture)
    expected = _marker_facts(prep._build_verified_zdex_buyback_spot_safety_purchase_v2(prepared))
    restorers: list[Callable[[], None]] = []
    fixture.backend.hook = lambda *_: restorers.append(
        _mutate_price_witness_aliases(prepared.price_authority)
    )
    try:
        marker = shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(
            prepared, fixture.receipt_verifier
        )
    finally:
        fixture.backend.hook = None
    assert len(restorers) == 1
    assert prepared.price_authority.authority_root != _PRICE_AUTHORITY_ROOT_PIN
    restorers.pop()()
    # Assert: the executed copy owns both witnesses, so the marker is unchanged.
    assert fixture.backend.calls == [_request(fixture)]
    assert _marker_facts(marker) == expected
    assert marker.price_authority_root == _PRICE_AUTHORITY_ROOT_PIN
    assert marker.price_safety.binding_root == _PRICE_SAFETY_BINDING_ROOT_PIN
    assert marker.price_safety.route_safe_quote_limit_atoms == 200
    assert marker.binding_root == _BINDING_ROOT_PIN
    assert type(marker.price_safety) is VerifiedZDEXBuybackPriceSafetyV1

    # Arrange: the public path, where the shell holds the prepared subject internally.
    seen: list[Any] = []
    original_prepare = shell.prepare_zdex_buyback_spot_safety_receipt_v2

    def capturing_prepare(selection: Any, **kwargs: Any) -> Any:
        subject = original_prepare(selection, **kwargs)
        seen.append(subject)
        return subject

    monkeypatch.setattr(shell, "prepare_zdex_buyback_spot_safety_receipt_v2", capturing_prepare)
    public = _fixture()
    public.backend.hook = lambda *_: restorers.append(
        _mutate_price_witness_aliases(seen[-1].price_authority)
    )
    try:
        public_marker = _verify(public)
    finally:
        public.backend.hook = None
        while restorers:
            restorers.pop()()
    assert len(seen) == 1
    assert public.backend.calls == [_request(public)]
    assert _marker_facts(public_marker) == expected
    assert public_marker.price_authority_root == _PRICE_AUTHORITY_ROOT_PIN


def test_snapshot_owns_both_price_witnesses_and_refuses_non_exact_witness_data() -> None:
    fixture = _fixture()
    prepared = _prepared(fixture)

    snapshot = prep.snapshot_prepared_zdex_buyback_spot_safety_receipt_v2(prepared)

    assert snapshot.price_authority is not prepared.price_authority
    assert snapshot.price_authority.price_safety is not prepared.price_authority.price_safety
    assert type(snapshot.price_authority) is VerifiedZDEXBuybackPriceAuthorityV1
    assert type(snapshot.price_authority.price_safety) is VerifiedZDEXBuybackPriceSafetyV1
    assert snapshot.price_authority.authority_root == _PRICE_AUTHORITY_ROOT_PIN
    assert snapshot.price_authority.price_safety.binding_root == _PRICE_SAFETY_BINDING_ROOT_PIN
    # Deliberately malformed witness data is refused before any copy is made.
    class _ForgedAuthority(VerifiedZDEXBuybackPriceAuthorityV1):
        pass

    forged_subclass = object.__new__(_ForgedAuthority)
    object.__setattr__(forged_subclass, "_fields", _witness_fields(prepared.price_authority))
    hostile_root = _forged_witness(
        prepared.price_authority,
        execution_policy_root=_HostileRoot(prepared.price_authority.execution_policy_root),
    )
    hostile_safety = _forged_witness(
        prepared.price_authority,
        price_safety=_forged_witness(
            prepared.price_authority.price_safety, route_safe_quote_limit_atoms=cast(Any, "200")
        ),
    )
    for witness, message in (
        (forged_subclass, "price authority must be exact typed data"),
        (object(), "price authority must be exact typed data"),
        (hostile_root, "price authority root 2 must be exact str"),
        (hostile_safety, "route_safe_quote_limit_atoms must be exact int"),
    ):
        with pytest.raises(TypeError, match=message):
            prep._snapshot_price_authority_v2(cast(Any, witness))


def _coherent_substitutions(
    prepared: prep.PreparedZDEXBuybackSpotSafetyReceiptV2, fixture: _Fixture
) -> tuple[tuple[str, Any, str], ...]:
    """Well-typed single-field substitutions with the journal and bytes held fixed."""

    state = prepared.tokenomics_pre_state
    cadence = replace(state.buyback_spend_states[0], last_execution_height=1)
    shares = list(prepared.fee_policy.shares)
    shares[0] = replace(shares[0], share_bps=shares[0].share_bps + 1)
    forged_authority = _forged_witness(prepared.price_authority, execution_policy_root=_root(0xA1))
    forged_safety = _forged_witness(
        prepared.price_authority,
        price_safety=_forged_witness(prepared.price_authority.price_safety, minimum_output_atoms=108),
    )
    # A tighter route keeps the Spot release identity, so only the route lookup fails;
    # a tighter Spot release changes the release identity the journal commits.
    tight_route_profile, _, _ = _tight_profile(
        fixture, route_max_journal_bytes=_JOURNAL_LEN_PIN - 1, spot_max_journal_bytes=65_536
    )
    tight_spot_profile, _, _ = _tight_profile(
        fixture, route_max_journal_bytes=65_536, spot_max_journal_bytes=_JOURNAL_LEN_PIN - 1
    )
    policies = "marker policies are outside the journal"
    domain = "receipt domain is outside the admissible kind"
    root = "price authority root mismatch"
    return (
        ("spend_policy", replace(prepared, spend_policy=replace(prepared.spend_policy, per_command_quote_cap_atoms=201)), policies),
        ("fee_policy", replace(prepared, fee_policy=ZDEXFeeAllocationPolicyV1(tuple(shares))), policies),
        ("fee_context", replace(prepared, fee_context=replace(prepared.fee_context, writer_epoch=12)), policies),
        ("tokenomics_pre_state", replace(prepared, tokenomics_pre_state=ZDEXAtomicBuybackTokenomicsStateV1(state.tokenomics, (cadence,))), policies),
        ("receipt_kind_conditional", replace(prepared, receipt_kind=ReceiptKindV1.CONDITIONAL), domain),
        ("receipt_kind_fake", replace(prepared, receipt_kind=ReceiptKindV1.FAKE), domain),
        ("empty_receipt_with_coherent_digest", replace(prepared, receipt_bytes=b"", receipt_digest=_digest(b"")), domain),
        ("module_release_id", replace(prepared, expected_module_release_id=fixture.candidate.journal.tokenomics_module_release_id), "request image is outside the profile"),
        ("profile_with_foreign_route", replace(prepared, profile=tight_route_profile), "journal is outside the selected route ceiling"),
        ("profile_with_foreign_spot_release", replace(prepared, profile=tight_spot_profile), "request image is outside the profile"),
        ("price_authority_with_coherent_root", replace(prepared, price_authority=forged_authority, price_authority_root=forged_authority.authority_root), root),
        ("nested_price_safety_with_coherent_root", replace(prepared, price_authority=forged_safety, price_authority_root=forged_safety.authority_root), root),
    )


def test_coherent_field_substitution_rejects_before_bound_with_no_call() -> None:
    """Root's draft finding: prepared records are caller-constructible data.

    Substituting one well-typed marker source while the executed journal and
    bytes stay fixed must reject in the snapshot, the completion factory and
    the private executor before the Bound verifier is invoked.
    """

    fixture = _fixture()
    prepared = _prepared(fixture)

    for label, subject, message in _coherent_substitutions(prepared, fixture):
        with pytest.raises(ValueError, match=message):
            prep.snapshot_prepared_zdex_buyback_spot_safety_receipt_v2(subject)
        with pytest.raises(ValueError, match=message):
            prep._build_verified_zdex_buyback_spot_safety_purchase_v2(subject)
        with pytest.raises(ValueError, match=message):
            shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(
                subject, fixture.receipt_verifier
            )
        assert fixture.backend.calls == [], label
    # The unsubstituted record still executes once and mints the pinned marker.
    marker = shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(
        prepared, fixture.receipt_verifier
    )
    assert fixture.backend.calls == [_request(fixture)]
    assert marker.binding_root == _BINDING_ROOT_PIN


@pytest.mark.parametrize(
    ("field_name", "replacement"),
    (
        ("authority_head_root", _root(80_001)),
        ("verifier_binding_root", _root(80_002)),
    ),
)
def test_prepared_root_substitutions_reject_before_callback_and_fee_ingress_derivation(
    monkeypatch: pytest.MonkeyPatch,
    field_name: str,
    replacement: str,
) -> None:
    """Each authority provenance root must bind before the sole backend call.

    The frozen draft accepted each one-field substitute with the exact same
    request and journal, called the backend, and derived fee ingress under the
    substituted root.  This ordinary law fixes that pre-I/O boundary.
    """

    fixture = _fixture()
    prepared = _prepared(fixture)
    if field_name == "authority_head_root":
        subject = replace(prepared, authority_head_root=replacement)
    else:
        assert field_name == "verifier_binding_root"
        subject = replace(prepared, verifier_binding_root=replacement)
    exact_request = _request(fixture)
    derivations: list[str] = []
    original_derive = prep._derive_verified_zdex_fee_ingress_slice_v1

    def recording_derive(**kwargs: Any) -> VerifiedZDEXFeeIngressSliceV1:
        derivations.append("derive")
        return original_derive(**kwargs)

    monkeypatch.setattr(prep, "_derive_verified_zdex_fee_ingress_slice_v1", recording_derive)

    assert (subject.receipt_bytes, subject.expected_image_id, subject.expected_journal_bytes) == (
        exact_request
    )
    assert subject.journal == prepared.journal
    assert subject.journal_digest == prepared.journal_digest
    _assert_rejects(
        lambda: shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(
            subject, fixture.receipt_verifier
        ),
        Reject.AUTHORITY_BINDING_MISMATCH,
        _AUTHORITY_DETAIL,
        fixture,
    )
    assert fixture.backend.calls == []
    assert derivations == []


def test_fee_ingress_witness_is_derived_only_after_callback_success(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: record the order of the backend call and the ingress derivation.
    fixture = _fixture()
    sequence: list[str] = []
    original_derive = prep._derive_verified_zdex_fee_ingress_slice_v1

    def recording_derive(**kwargs: Any) -> VerifiedZDEXFeeIngressSliceV1:
        sequence.append("derive")
        assert len(fixture.backend.calls) == 1
        return original_derive(**kwargs)

    monkeypatch.setattr(prep, "_derive_verified_zdex_fee_ingress_slice_v1", recording_derive)
    fixture.backend.hook = lambda *_: sequence.append("backend")

    # Act / Assert: preparation and detachment derive nothing.
    prepared = _prepared(fixture)
    prep.snapshot_prepared_zdex_buyback_spot_safety_receipt_v2(prepared)
    assert sequence == []
    # A failed callback never derives the witness.
    fixture.backend.error = ValueError("boundary backend rejection")
    _assert_rejects(
        lambda: _verify(fixture), Reject.RECEIPT_VERIFICATION_FAILED, _CALLBACK_DETAIL, fixture, calls=1
    )
    assert sequence == ["backend"]
    # A successful callback derives it exactly once, afterwards, from the executed copy.
    fixture.backend.error = None
    fixture.backend.calls.clear()
    sequence.clear()
    marker = _verify(fixture)
    fixture.backend.hook = None
    assert sequence == ["backend", "derive"]
    assert type(marker.fee_ingress) is VerifiedZDEXFeeIngressSliceV1
    assert _ingress_facts(marker.fee_ingress) == (
        fixture.candidate.occurrence.occurrence_id,
        fixture.candidate.global_pre_state.state_root,
        fixture.candidate.profile.profile_id,
        prepared.fee_state.state_root,
        fixture.candidate.journal.quote_asset_id,
        _FEE_INGRESS_ATOMS_PIN,
        _HEAD_ROOT_PIN,
        _VERIFIER_BINDING_ROOT_PIN,
    )
    assert marker.fee_ingress.binding_root == _FEE_INGRESS_BINDING_ROOT_PIN
    assert marker.fee_command.fee_charged_atoms == marker.fee_ingress.fee_ingress_atoms
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedZDEXFeeIngressSliceV1(object(), cast(Any, object()))


# --- semantic mutants (executed, structure-preserving) -----------------------


def test_callback_before_guard_mutant_is_killed_by_the_no_call_law() -> None:
    original = shell.verify_zdex_buyback_spot_safety_receipt_shadow_v2
    target = "    selection = prepare_zdex_buyback_spot_safety_selection_v2(candidate)\n"
    mutant_body = (
        "    receipt_verifier.verify_profile_lane_receipt(\n"
        "        candidate.receipt.receipt_bytes,\n"
        "        profile=candidate.profile,\n"
        "        lane_id=LaneIdV1.SPOT_LIQUIDITY,\n"
        "        expected_module_release_id=candidate.journal.spot_module_release_id,\n"
        "        expected_image_id=candidate.journal.spot_guest_image_id,\n"
        "        expected_journal_bytes=canonical_global_bytes_v1(candidate.journal),\n"
        "    )\n"
        "    selection = prepare_zdex_buyback_spot_safety_selection_v2(candidate)\n"
    )
    mutant = _mutant(
        shell, original, target, mutant_body, {"canonical_global_bytes_v1": canonical_global_bytes_v1}
    )
    fixture = _fixture()
    tampered = replace(
        fixture.candidate,
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional"),
    )
    expected_request = (b"conditional", fixture.spot_release.guest_image_id, _request(fixture)[2])

    # Control: the ordinary law holds on the unmutated shell.
    _assert_rejects(
        lambda: original(
            tampered, authority_head=fixture.authority_head, receipt_verifier=fixture.receipt_verifier
        ),
        Reject.UNSUPPORTED_RECEIPT_KIND,
        "only Succinct receipts are admissible",
        fixture,
    )
    assert fixture.backend.calls == []
    # Mutant: the same rejection is raised, but the no-call assertion is reachable and fails.
    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as rejected:
        mutant(tampered, authority_head=fixture.authority_head, receipt_verifier=fixture.receipt_verifier)
    assert rejected.value.code is Reject.UNSUPPORTED_RECEIPT_KIND
    assert fixture.backend.calls == [expected_request]
    with pytest.raises(AssertionError):
        assert fixture.backend.calls == []


def test_wrong_request_image_mutant_is_killed_by_the_bound_image_law() -> None:
    original = shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2
    mutant = _mutant(
        shell,
        original,
        "            expected_image_id=owned.expected_image_id,\n",
        "            expected_image_id=owned.profile.root_image_id,\n",
    )
    fixture = _fixture()
    prepared = _prepared(fixture)
    assert prepared.expected_image_id != prepared.profile.root_image_id

    # Control: the module image is requested and the marker names it.
    marker = original(prepared, fixture.receipt_verifier)
    assert fixture.backend.calls == [_request(fixture)]
    assert marker.expected_image_id == _EXPECTED_IMAGE_PIN
    # Mutant: the Bound verifier refuses the root image for the Spot lane before the
    # backend is reached, so the exact-request observation fails and nothing is minted.
    fixture.backend.calls.clear()
    _assert_rejects(
        lambda: mutant(prepared, fixture.receipt_verifier),
        Reject.RECEIPT_VERIFICATION_FAILED,
        _CALLBACK_DETAIL,
        fixture,
    )
    with pytest.raises(AssertionError):
        assert fixture.backend.calls == [_request(fixture)]


def _head_root_after_callback(
    verify: Callable[..., Any],
) -> str:
    fixture = _fixture()
    head = fixture.authority_head
    fixture.backend.hook = lambda *_: object.__setattr__(head, "generation", 7)
    try:
        marker = verify(
            fixture.candidate, authority_head=head, receipt_verifier=fixture.receipt_verifier
        )
    finally:
        fixture.backend.hook = None
    assert head.authority_root != _HEAD_ROOT_PIN
    assert fixture.backend.calls == [_request(fixture)]
    return marker.authority_head_root


def test_post_io_caller_head_relabel_mutant_is_killed_by_the_head_mutation_observation() -> None:
    """Failing-first evidence for the named ownership repair.

    The former core path read ``authority_head.authority_root`` from the caller
    alias after the Bound callback.  The mutant restores that read; a callback
    that mutates the caller-held head then relabels the marker.
    """

    original = shell.verify_zdex_buyback_spot_safety_receipt_shadow_v2
    target = (
        "    return _execute_prepared_zdex_buyback_spot_safety_receipt_v2(prepared, receipt_verifier)\n"
    )
    mutant_body = (
        "    verified = _execute_prepared_zdex_buyback_spot_safety_receipt_v2(\n"
        "        prepared, receipt_verifier\n"
        "    )\n"
        "    return VerifiedZDEXBuybackSpotSafetyPurchaseV2(\n"
        "        _VERIFIED_ZDEX_BUYBACK_SPOT_TOKEN_V2,\n"
        "        replace(verified._fields, authority_head_root=authority_head.authority_root),\n"
        "    )\n"
    )
    mutant = _mutant(
        shell,
        original,
        target,
        mutant_body,
        {
            "replace": replace,
            "_VERIFIED_ZDEX_BUYBACK_SPOT_TOKEN_V2": core._VERIFIED_ZDEX_BUYBACK_SPOT_TOKEN_V2,
        },
    )

    # Control: the repaired shell reports the owned pre-I/O head root.
    assert _head_root_after_callback(original) == _HEAD_ROOT_PIN
    # Mutant: the post-I/O alias read relabels the marker, so the observation fails.
    assert _head_root_after_callback(mutant) != _HEAD_ROOT_PIN
    with pytest.raises(AssertionError):
        assert _head_root_after_callback(mutant) == _HEAD_ROOT_PIN


def test_aliased_price_authority_mutant_is_killed_by_the_post_callback_completion_law(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Failing-first evidence for root's draft price-alias finding.

    The draft snapshot kept ``price_authority=prepared.price_authority`` by
    reference.  The mutant restores that alias; a callback that relabels the
    retained witness then makes completion reject after one successful callback
    with the exact draft message root recorded.
    """

    original = prep.snapshot_prepared_zdex_buyback_spot_safety_receipt_v2
    mutant = _mutant(
        prep,
        original,
        "        price_authority=_snapshot_price_authority_v2(prepared.price_authority),\n",
        "        price_authority=prepared.price_authority,\n",
    )

    def run(snapshot: Callable[..., Any]) -> tuple[Any, _Fixture]:
        monkeypatch.setattr(prep, "snapshot_prepared_zdex_buyback_spot_safety_receipt_v2", snapshot)
        monkeypatch.setattr(shell, "snapshot_prepared_zdex_buyback_spot_safety_receipt_v2", snapshot)
        fixture = _fixture()
        prepared = _prepared(fixture)
        restorers: list[Callable[[], None]] = []
        fixture.backend.hook = lambda *_: restorers.append(
            _mutate_price_witness_aliases(prepared.price_authority)
        )
        try:
            return (
                shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(
                    prepared, fixture.receipt_verifier
                ),
                fixture,
            )
        finally:
            fixture.backend.hook = None
            assert len(fixture.backend.calls) == 1

    # Control: the owned copy completes with the pre-I/O price authority root.
    marker, _ = run(original)
    assert marker.price_authority_root == _PRICE_AUTHORITY_ROOT_PIN
    # Mutant: the retained alias reaches completion and rejects after the callback.
    with pytest.raises(
        ValueError, match="prepared ZDEX buyback Spot receipt price authority root mismatch"
    ):
        run(mutant)


def test_missed_digest_check_mutant_is_killed_by_the_digest_observation() -> None:
    original = prep.snapshot_prepared_zdex_buyback_spot_safety_receipt_v2
    mutant = _mutant(
        prep,
        original,
        "    _require_prepared_request_binding_v2(prepared)\n",
        "    pass\n",
    )
    fixture = _fixture()
    prepared = _prepared(fixture)
    inconsistent = replace(prepared, receipt_digest=_digest(b"other"))

    # Control: the unmutated snapshot refuses a record whose digest is unbound to its bytes.
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        original(inconsistent)
    # Mutant: the same record is accepted with its digest unbound from its bytes, so the
    # control rejection is unreachable and a shell would execute unbound bytes.
    accepted = mutant(inconsistent)
    assert accepted.receipt_digest != _digest(accepted.receipt_bytes)
    assert _prepared_facts(accepted) == _prepared_facts(inconsistent)
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        shell._execute_prepared_zdex_buyback_spot_safety_receipt_v2(
            inconsistent, fixture.receipt_verifier
        )
    assert fixture.backend.calls == []


def test_pre_callback_fee_ingress_mutant_is_killed_by_the_lifecycle_observation() -> None:
    derivations: list[str] = []
    original_derive = prep._derive_verified_zdex_fee_ingress_slice_v1

    def recording_derive(**kwargs: Any) -> VerifiedZDEXFeeIngressSliceV1:
        derivations.append("derive")
        return original_derive(**kwargs)

    original = prep.prepare_zdex_buyback_spot_safety_receipt_v2
    target = "    return PreparedZDEXBuybackSpotSafetyReceiptV2(\n"
    mutant_body = (
        "    _derive_verified_zdex_fee_ingress_slice_v1(\n"
        "        command_occurrence_id=owned.occurrence.occurrence_id,\n"
        "        global_pre_state_root=owned.global_pre_state.state_root,\n"
        "        profile_root=owned.profile.profile_id,\n"
        "        fee_state=owned.tokenomics_pre_state.fee_state_for(owned.journal.quote_asset_id),\n"
        "        authority_head_root=head.authority_root,\n"
        "        verifier_binding_root=verifier_binding_root,\n"
        "    )\n"
        "    return PreparedZDEXBuybackSpotSafetyReceiptV2(\n"
    )
    mutant = _mutant(
        prep, original, target, mutant_body, {"_derive_verified_zdex_fee_ingress_slice_v1": recording_derive}
    )
    fixture = _fixture()
    selection = _selection(fixture)

    # Control: pure preparation derives no ingress witness before any callback.
    control = original(
        selection,
        authority_head=fixture.authority_head,
        verifier_binding_root=fixture.receipt_verifier.binding_root,
    )
    assert derivations == []
    # Mutant: the witness is derived before any I/O, so the lifecycle observation fails.
    mutated = mutant(
        selection,
        authority_head=fixture.authority_head,
        verifier_binding_root=fixture.receipt_verifier.binding_root,
    )
    assert derivations == ["derive"]
    assert fixture.backend.calls == []
    assert _prepared_facts(mutated) == _prepared_facts(control)
    with pytest.raises(AssertionError):
        assert derivations == []
