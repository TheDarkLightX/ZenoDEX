"""Boundary evidence for the epoch and initial-state verifier extraction.

Core prepares exact detached subjects and calls no verifier; the integration
shell executes exactly those subjects on the selected verifier and mints the
publisher-bound witness.  Every receipt verifier here is a deterministic
recorder or the synthetic process reply, never cryptographic evidence.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
from dataclasses import replace
from pathlib import Path

import pytest

import src.core.economic_initial_state_publisher_verification_v1 as initial_core
import src.core.global_economic_proof_v1 as proof
import src.core.zdex_fee_allocation_receipt_verification_v1 as fee_leaf_core
import src.core.zdex_purchase_burn_receipt_preparation_v1 as purchase_burn_prep
import src.core.zdex_purchase_burn_receipt_verification_v1 as purchase_burn_core
import src.integration.economic_initial_state_publisher_verification_v1 as initial_shell
import src.integration.global_economic_epoch_verification_v1 as shell
import src.integration.zdex_fee_allocation_receipt_verification_v1 as fee_leaf_shell
from src.core.economic_initial_state_atom_coverage_v1 import EconomicInitialStateKindV1
from src.core.economic_initial_state_v1 import _VerifiedEconomicInitialStateV1
from src.core.global_settlement_types_v1 import canonical_global_bytes_v1
from src.integration.global_economic_commit_v1 import CommitOutcomeStatusV1
from src.integration.global_economic_durable_publisher_v1 import (
    VerifiedDurableEconomicPublisherV1,
)
from src.integration.global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCommitStatusV1,
)
from tests.core.test_economic_receipt_verifier_release_v1 import _RecordingBackend
from tests.core.test_global_settlement_abi_v1 import (
    _commit_port,
    _epoch_admission_fixture,
    _epoch_candidate_with_rebound_post_state,
    _initial_state_admission,
    _migration_admission_for_source_head,
    _profile,
    _publisher_verified_epoch,
    _RecordingReceiptVerifier,
    _root,
    _state,
    _verified_epoch,
)
from tests.core.test_zdex_purchase_burn_route_v1 import _fee_receipt_candidate_fixture
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    publisher_raw_evidence_v1,
)
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    simulated_measured_publisher_crypto_v1 as simulated_measured_publisher_crypto_v1,
)
from tests.integration.test_global_economic_durable_publisher_v1 import (
    _bound_receipt_verifier_v1,
    _publisher_fixture_v1,
)

REPO_ROOT = Path(__file__).resolve().parents[2]

# Fixed vectors captured on the pre-extraction tree (base 05e897256) with the
# same retained fixtures.  The extraction must reproduce them exactly.
_RESEARCH_TWO_COMMAND_PINS = {
    "commit_id": "0xfc18524623cb1ff079460ff9b20d7c4f93ea6ecdb7c2bdbdbac1e5289d1bc2c1",
    "verified_certificate_root": (
        "0x41daf424240744eb3a88cbf7cfcdd8f0b40e57f2b2a0d4d12ff8399d87764e01"
    ),
    "verified_effect_plan_root": (
        "0x2a904f90e4b1d8b55e648fc0fd4a53273e1495f02ace48aebb41218bfbb2fcb0"
    ),
    "verified_state_effect_refinement_root": (
        "0x386afa75e6e8232365b5f5685604dadc5df17b5f7d6666f4792fbee2edea187e"
    ),
    "state_delta_root": "0xe2fcff7132cbdf840e178c04bea6d97aae319b681cc075ab002b74cd12cd248b",
    "ordered_route_binding_roots": (
        "0xf702670c9cd37fbbe3b746721ecd6d0589dc5fe6af556a4c19cf5589a9202901",
        "0xceae9aebc04964be76c6b7804b2e5ac763208ed709f9c8f284ec02129eee0c6c",
    ),
    "receipt_digest": "0x2fc5a01247e2ec0488aa29e38e4ef12824e94d2bf923d1108b262768e979885e",
    "expected_image_id": "0x000000000000000000000000000000000000000000000000000000000000019b",
    "expected_journal_len": 1751,
    "expected_journal_sha256": (
        "0x3815aae3b712784fd3b28a78a6e94f150c820b948c59e3a5cc99abe3fab9e52e"
    ),
}
_IN_MEMORY_PUBLISHER_PINS = {
    "commit_id": "0xf8b860443ed13a7d592d262a52e27cabcd4ff00eb015306f64fcf278936b40c2",
    "verified_certificate_root": (
        "0x43f1bfade5be8cda3628df0fc55c6123604b22ff90ad6d408d5b13ca4d64a602"
    ),
    "verified_effect_plan_root": (
        "0x5bd4040dafaea90639950058f6aa04f79529f5cb5d563c7ca5a3ef6cf5d39f07"
    ),
    "verified_state_effect_refinement_root": (
        "0x8aa213472811ab1bff7d2d0c2aa75fc243d567e9af2b7795fc029df4a568af44"
    ),
    "receipt_digest": "0x1ea826d086906dfa2591c53cd8bde4ae5d1e8fb4b3510dbeebca21d719073857",
    "published_record_sha256": (
        "0xa73b5f243d2e41445a863a910ba68a90275bc614f95efe93a4fe77282f0f2058"
    ),
    "published_state_root": (
        "0xd17250db767f19cf8e157f5fc002a291ce4d5649f89f6303b922d310dbc21acd"
    ),
    "initial_state_certificate_root": (
        "0x82816c7f3486fad0cdf48adbe58ef9d480884d18d33cc5b62d768ca7234eff00"
    ),
    "genesis_receipt_sha256": (
        "0xe9333d9f8293c9f7a6c3a5df4628c246088a4b0a7910a86e2a5733e980ea6812"
    ),
    "genesis_journal_sha256": (
        "0x4c80edaed40aa4a8a654eef8de1e3b424156b963a1f85ed2ffa4094f8f3bb030"
    ),
    "genesis_journal_len": 1343,
    "epoch_journal_sha256": (
        "0xc65afdb02dba8b67fd62c345c446998647b6f746e9d8b9e79eacadf0e02236c6"
    ),
    "epoch_journal_len": 1544,
}
_GENESIS_PINS = {
    "certificate_root": "0x82816c7f3486fad0cdf48adbe58ef9d480884d18d33cc5b62d768ca7234eff00",
    "profile_id": "0xb6a11327b2d140e4f8f438decc36c70abbfd64ffc6d47e810dc99590afd23eb5",
    "state_root": "0x047222effa8aca2203f345614f91f62539e5e2a94758053a321792fc63fd439a",
}
_MIGRATION_PINS = {
    "certificate_root": "0xc2b522c810ab091a59142bf561da8603751a66f2a71b0adebdb2ab5a6be04b9a",
    "profile_id": "0x24004ea7d446efd48843af4e4b1e7cbdfd54c9ec4efcef121811d31629ae83c3",
    "state_root": "0x1c39ac470ec17e77ab98d313808dd82d9c3fd4cfb72ba3d985641c1887c96ee4",
    "journal_sha256": "0x340973f4b290e8f524b4fc2f08ed847db5e7faf8179d8b8e7c6764ba95f886cf",
}

_CORE_ROOT_EPOCH_MODULES = (
    "src/core/global_economic_proof_v1.py",
    "src/core/economic_initial_state_publisher_verification_v1.py",
)
_SHELL_MODULES = (
    "src/integration/global_economic_epoch_verification_v1.py",
    "src/integration/economic_initial_state_publisher_verification_v1.py",
)
_CONSUMER_MODULES = (
    "src/integration/global_economic_commit_v1.py",
    "src/integration/global_economic_durable_publisher_v1.py",
)
_MOVED_NAMES = frozenset(
    {
        "VerifiedEconomicEpochV1",
        "verify_economic_epoch_v1",
        "_snapshot_verified_economic_epoch_v1",
        "_verified_economic_epoch_is_bound_to_publisher_v1",
        "_verify_economic_epoch_for_publisher_v1",
        "_verify_economic_initial_state_for_publisher_v1",
        "_verify_economic_migration_for_publisher_v1",
    }
)
_VERIFIER_CALL_NAMES = frozenset(
    {
        "verify_succinct_receipt",
        "verify_profile_lane_receipt",
        "verify_profile_lane_coordinator_receipt",
        "verify_profile_route_receipt",
    }
)
_SHELL_MECHANISM_NAMES = frozenset({"Lock", "RLock", "WeakKeyDictionary", "WeakValueDictionary"})
_PUBLISHER_OBJECT_FIELD_NAMES = frozenset(
    {
        "publisher_binding_token",
        "publisher_verifier_identity",
        "receipt_verifier",
        "backend",
        "verify_call",
    }
)
# Remaining receipt callback and deployment owners found by the scoped source
# review. Each marker is checked below; this list is not a transitive purity proof.
_LEGACY_CORE_CALLBACK_DEBT = (
    (
        "src/core/zdex_purchase_burn_receipt_verification_v1.py",
        "receipt_verifier.require_binding(",
        "shared _require_current_shadow_authority_v1 reads the Bound verifier registry",
    ),
    (
        "src/core/zdex_atomic_buyback_receipt_verification_v2.py",
        "receipt_verifier.verify_profile_lane_receipt(",
        "atomic buyback module receipt callback",
    ),
    (
        "src/core/zdex_atomic_buyback_lane_receipt_v2.py",
        "receipt_verifier.verify_profile_lane_coordinator_receipt(",
        "atomic buyback lane coordinator receipt callback",
    ),
    (
        "src/core/zdex_atomic_buyback_route_receipt_v2.py",
        "receipt_verifier.verify_profile_route_receipt(",
        "atomic buyback route receipt callback",
    ),
    (
        "src/core/zdex_buyback_spot_safety_receipt_v1.py",
        "receipt_verifier.verify_profile_lane_receipt(",
        "buyback Spot safety module receipt callback",
    ),
    (
        "src/core/economic_receipt_verifier_deployment_v1.py",
        "_BOUND_RECEIPT_VERIFIER_AUTHORITIES_V1: WeakKeyDictionary[",
        "Bound deployment registry, lock and backend call remain core debt",
    ),
)
# Core callback debt closed by the tokenomics burn-lane / fee-lane extraction.
# The former marker for each row was "receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1".
# Each module is re-checked to stay a pure preparation boundary so the closure
# cannot silently regress; the shell below is the only callback owner.
_CLOSED_TOKENOMICS_CALLBACK_CORE_MODULES = (
    "src/core/zdex_tokenomics_lane_receipt_common_v1.py",
    "src/core/zdex_tokenomics_lane_receipt_verification_v1.py",
    "src/core/zdex_tokenomics_fee_lane_receipt_verification_v1.py",
)
_TOKENOMICS_SHELL_MODULE = "src/integration/zdex_tokenomics_lane_receipt_verification_v1.py"
# Core callback debt closed by the fee-allocation leaf extraction.  The former row was
# ("src/core/zdex_fee_allocation_receipt_verification_v1.py",
#  "receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1", "fee allocation receipt callback").
_CLOSED_FEE_LEAF_CALLBACK_CORE_MODULES = (
    "src/core/zdex_fee_allocation_receipt_verification_v1.py",
)
_FEE_LEAF_SHELL_MODULE = "src/integration/zdex_fee_allocation_receipt_verification_v1.py"
# Core callback debt closed by the purchase V1/V2 and burn V1 extraction.  The former
# row was ("src/core/zdex_purchase_burn_receipt_verification_v1.py",
#  "receipt_verifier.verify_succinct_receipt(",
#  "purchase V1/V2 and burn V1 callbacks plus governed wrapper paths").  The old module
# keeps only the shared Bound-authority helper, which stays an open row above.
_CLOSED_PURCHASE_BURN_PREPARATION_CORE_MODULES = (
    "src/core/zdex_purchase_burn_receipt_preparation_v1.py",
)
_PURCHASE_BURN_LEGACY_CORE_MODULE = "src/core/zdex_purchase_burn_receipt_verification_v1.py"
_PURCHASE_BURN_SHELL_MODULE = "src/integration/zdex_purchase_burn_receipt_verification_v1.py"
_PURCHASE_BURN_MOVED_NAMES = frozenset(
    {
        "verify_zdex_amm_purchase_receipt_v1",
        "verify_zdex_amm_purchase_receipt_v2",
        "verify_zdex_burn_receipt_v1",
        "verify_governed_zdex_amm_purchase_receipt_shadow_v1",
        "verify_governed_zdex_amm_purchase_receipt_shadow_v2",
        "verify_governed_zdex_burn_receipt_shadow_v1",
        "ZDEXLaneSuccinctReceiptVerifierV1",
        "_ProfileLaneReceiptVerifierV1",
    }
)


def _digest(data: bytes) -> str:
    return "0x" + hashlib.sha256(data).hexdigest()


def _registered_receipt_digests() -> tuple[str, ...]:
    with shell._VERIFIED_ECONOMIC_EPOCH_AUTHORITY_LOCK:
        records = tuple(shell._VERIFIED_ECONOMIC_EPOCH_AUTHORITIES.values())
    return tuple(record.prepared.receipt_digest for record in records)


def _prepared_facts(prepared: proof.PreparedEconomicEpochV1) -> tuple[object, ...]:
    return (
        prepared.certificate.certificate_root,
        prepared.certificate_root,
        tuple(item.occurrence_id for item in prepared.command_occurrences),
        prepared.effect_plan.effect_plan_root,
        prepared.effect_plan_root,
        prepared.ordered_route_binding_roots,
        prepared.profile.profile_id,
        prepared.profile.root_image_id,
        prepared.receipt_digest,
        tuple(item.effect_plan_root for item in prepared.route_effect_plans),
        tuple(item.journal_root for item in prepared.route_journals),
        tuple(
            (
                tuple(journal.journal_root for journal in item.lane_journals),
                item.post_state.state_root,
            )
            for item in prepared.route_state_disclosures
        ),
        prepared.route_state_effect_refinement_roots,
        prepared.route_state_projection_roots,
        prepared.state_effect_refinement.refinement_root,
        prepared.state_effect_refinement.state_delta_root,
        prepared.state_effect_refinement_root,
        prepared.receipt_bytes,
        prepared.expected_image_id,
        prepared.expected_journal_bytes,
        prepared.commit_id,
        tuple(item.effect_occurrence_id for item in prepared.effect_occurrences),
    )


def _witness_facts(verified: shell.VerifiedEconomicEpochV1) -> tuple[object, ...]:
    return (
        verified.commit_id,
        verified.verified_certificate_root,
        verified.certificate.certificate_root,
        verified.verified_effect_plan_root,
        verified.effect_plan.effect_plan_root,
        verified.verified_state_effect_refinement_root,
        verified.state_effect_refinement.refinement_root,
        verified.state_effect_refinement.state_delta_root,
        verified.ordered_route_binding_roots,
        verified.ordered_command_body_hashes,
        verified.receipt_digest,
        verified.route_state_projection_roots,
        verified.route_state_effect_refinement_roots,
        tuple(item.effect_occurrence_id for item in verified.effect_occurrences),
    )


def _witness_facts_from_prepared(prepared: proof.PreparedEconomicEpochV1) -> tuple[object, ...]:
    return (
        prepared.commit_id,
        prepared.certificate_root,
        prepared.certificate.certificate_root,
        prepared.effect_plan_root,
        prepared.effect_plan.effect_plan_root,
        prepared.state_effect_refinement_root,
        prepared.state_effect_refinement.refinement_root,
        prepared.state_effect_refinement.state_delta_root,
        prepared.ordered_route_binding_roots,
        prepared.ordered_command_body_hashes,
        prepared.receipt_digest,
        prepared.route_state_projection_roots,
        prepared.route_state_effect_refinement_roots,
        tuple(item.effect_occurrence_id for item in prepared.effect_occurrences),
    )


def _publisher_token(port: object) -> object:
    return port._GlobalEconomicCommitPortV1__publisher_binding_token  # type: ignore[attr-defined]


class _StrictThreeFieldVerifier:
    """Accept exactly one positional receipt plus two keyword fields, nothing else."""

    def __init__(self) -> None:
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        /,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))


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


# --- pure preparation -------------------------------------------------------


def test_prepare_is_repeatable_pure_and_grants_no_authority() -> None:
    # Arrange: the retained two-command fixture and no verifier anywhere.
    candidate = _epoch_admission_fixture(2)
    assert tuple(inspect.signature(proof.prepare_economic_epoch_v1).parameters) == ("candidate",)

    # Act: prepare twice.
    first = proof.prepare_economic_epoch_v1(candidate)
    second = proof.prepare_economic_epoch_v1(candidate)

    # Assert: byte-identical decision, execution subject equals the candidate facts.
    assert type(first) is proof.PreparedEconomicEpochV1
    assert _prepared_facts(first) == _prepared_facts(second)
    assert first.expected_image_id == candidate.profile.root_image_id
    assert first.expected_journal_bytes == candidate.certificate.canonical_journal_bytes
    assert len(first.expected_journal_bytes) == candidate.certificate.journal_bytes
    assert first.receipt_digest == _digest(candidate.receipt_bytes)
    assert first.receipt_digest == candidate.certificate.receipt_root
    assert first.commit_id == proof.derive_verified_economic_epoch_commit_id_v1(
        certificate_root=first.certificate_root,
        ordered_route_binding_roots=first.ordered_route_binding_roots,
        receipt_digest=first.receipt_digest,
    )
    pins = _RESEARCH_TWO_COMMAND_PINS
    assert first.commit_id == pins["commit_id"]
    assert first.certificate_root == pins["verified_certificate_root"]
    assert first.effect_plan_root == pins["verified_effect_plan_root"]
    assert first.state_effect_refinement_root == pins["verified_state_effect_refinement_root"]
    assert first.state_effect_refinement.state_delta_root == pins["state_delta_root"]
    assert first.ordered_route_binding_roots == pins["ordered_route_binding_roots"]
    assert first.receipt_digest == pins["receipt_digest"]
    assert first.expected_image_id == pins["expected_image_id"]
    assert len(first.expected_journal_bytes) == pins["expected_journal_len"]
    assert _digest(first.expected_journal_bytes) == pins["expected_journal_sha256"]

    # Assert: plain data cannot become a witness without the shell's private token.
    with pytest.raises(TypeError, match="verifier-constructed"):
        shell.VerifiedEconomicEpochV1(first, object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="verifier-constructed"):
        shell.VerifiedEconomicEpochV1(
            object(),
            shell._VerifiedEconomicEpochAuthorityRecordV1(
                prepared=first,
                publisher_binding_token=None,
                publisher_verifier_identity=None,
            ),
        )


def test_prepared_subject_is_detached_from_the_caller_candidate_graph() -> None:
    candidate = _epoch_admission_fixture(1)
    prepared = proof.prepare_economic_epoch_v1(candidate)
    facts = _prepared_facts(prepared)

    object.__setattr__(candidate.certificate, "post_state_root", _root(91_001))
    object.__setattr__(candidate.profile, "root_image_id", _root(91_002))
    object.__setattr__(candidate.effect_plan.rows[0], "delta_atoms", 91_003)
    object.__setattr__(candidate.route_journals[0], "post_state_root", _root(91_004))
    object.__setattr__(
        candidate.route_state_disclosures[0].lane_journals[0],
        "post_lane_root",
        _root(91_005),
    )

    assert prepared.certificate is not candidate.certificate
    assert prepared.profile is not candidate.profile
    assert _prepared_facts(prepared) == facts
    assert _prepared_facts(proof._snapshot_prepared_economic_epoch_v1(prepared)) == facts


@pytest.mark.parametrize(
    "label",
    (
        "not_a_candidate",
        "wrong_chain_context",
        "wrong_deployment_context",
        "wrong_receipt_digest",
        "wrong_journal_byte_count",
        "wrong_refinement",
        "swapped_route_journals",
        "missing_route_witness",
    ),
)
def test_structural_rejections_precede_any_backend_call(label: str) -> None:
    # Arrange: one-defect subjects with unique receipts where a digest is observed.
    if label == "not_a_candidate":
        subject: object = object()
        expected: tuple[type[Exception], str] = (TypeError, "candidate type is not closed")
    elif label == "wrong_chain_context":
        subject = replace(_epoch_admission_fixture(1), expected_chain_id="foreign-chain")
        expected = (ValueError, "chain id mismatch")
    elif label == "wrong_deployment_context":
        subject = replace(_epoch_admission_fixture(1), expected_deployment_root=_root(92_001))
        expected = (ValueError, "deployment root mismatch")
    elif label == "wrong_receipt_digest":
        subject = replace(_epoch_admission_fixture(1), receipt_bytes=b"boundary-tampered-receipt")
        expected = (ValueError, "receipt root mismatch")
    elif label == "wrong_journal_byte_count":
        valid = _epoch_admission_fixture(1)
        subject = replace(
            valid,
            certificate=replace(valid.certificate, journal_bytes=valid.certificate.journal_bytes + 1),
        )
        expected = (ValueError, "canonical journal byte count mismatch")
    elif label == "wrong_refinement":
        valid = _epoch_admission_fixture(1)
        subject = _epoch_candidate_with_rebound_post_state(
            valid,
            replace(valid.post_state, replay_state=()),
        )
        expected = (ValueError, "replay state delta mismatch")
    elif label == "swapped_route_journals":
        valid = _epoch_admission_fixture(2)
        subject = replace(valid, route_journals=tuple(reversed(valid.route_journals)))
        expected = (ValueError, "route journal order or root mismatch")
    else:
        subject = replace(_epoch_admission_fixture(1), verified_routes=())
        expected = (ValueError, "route witness count mismatch")
    exception_type, message = expected

    # Act / Assert: the research shell and pure preparation reject identically, with no call.
    verifier = _RecordingReceiptVerifier()
    with pytest.raises(exception_type, match=message):
        shell.verify_economic_epoch_v1(subject, verifier)  # type: ignore[arg-type]
    assert verifier.calls == []
    with pytest.raises(exception_type, match=message):
        proof.prepare_economic_epoch_v1(subject)  # type: ignore[arg-type]
    if label == "wrong_receipt_digest":
        assert _digest(b"boundary-tampered-receipt") not in _registered_receipt_digests()
    if not isinstance(subject, proof.EconomicEpochReceiptCandidateV1):
        return

    # Act / Assert: the publisher-bound shell rejects before its backend sees the epoch.
    port_verifier = _RecordingReceiptVerifier()
    port = _commit_port(subject.profile, subject.pre_state, port_verifier)
    genesis_calls = list(port_verifier.calls)
    assert len(genesis_calls) == 1
    with pytest.raises(exception_type, match=message):
        port.verify_economic_epoch(subject)
    assert port_verifier.calls == genesis_calls
    assert port.state == subject.pre_state
    assert port.records == ()


# --- exact execution request and runtime controls ---------------------------


def test_shell_executes_exactly_the_prepared_three_field_request() -> None:
    candidate = _epoch_admission_fixture(2)
    prepared = proof.prepare_economic_epoch_v1(candidate)
    verifier = _StrictThreeFieldVerifier()

    verified = shell.verify_economic_epoch_v1(candidate, verifier)

    assert verifier.calls == [
        (prepared.receipt_bytes, prepared.expected_image_id, prepared.expected_journal_bytes)
    ]
    receipt, image, journal = verifier.calls[0]
    assert receipt is candidate.receipt_bytes
    assert image == _RESEARCH_TWO_COMMAND_PINS["expected_image_id"]
    assert len(journal) == _RESEARCH_TWO_COMMAND_PINS["expected_journal_len"]
    assert _digest(journal) == _RESEARCH_TWO_COMMAND_PINS["expected_journal_sha256"]
    assert _witness_facts(verified) == _witness_facts_from_prepared(prepared)
    assert verified.recheck_route_state_projections(
        pre_state=candidate.pre_state,
        post_state=candidate.post_state,
    ) == verified.route_state_projection_roots
    assert (
        verified.recheck_state_effect_refinement(
            pre_state=candidate.pre_state,
            post_state=candidate.post_state,
        ).refinement_root
        == verified.verified_state_effect_refinement_root
    )
    # A research witness carries no publisher binding at all.
    assert shell._verified_economic_epoch_is_bound_to_publisher_v1(verified, object(), verifier) is False
    authority = shell._verified_economic_epoch_authority_v1(verified)
    assert authority.publisher_binding_token is None
    assert authority.publisher_verifier_identity is None


def test_publisher_bound_epoch_and_commit_reproduce_the_pre_extraction_subject() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    pins = _IN_MEMORY_PUBLISHER_PINS

    port, verified, body, verifier, _, _ = _publisher_verified_epoch(
        profile, route, pre_state, post_state
    )

    assert port.initial_state_certificate_root == pins["initial_state_certificate_root"]
    assert [(_digest(r), i, _digest(j), len(j)) for r, i, j in verifier.calls] == [
        (
            pins["genesis_receipt_sha256"],
            profile.root_image_id,
            pins["genesis_journal_sha256"],
            pins["genesis_journal_len"],
        ),
        (
            pins["receipt_digest"],
            profile.root_image_id,
            pins["epoch_journal_sha256"],
            pins["epoch_journal_len"],
        ),
    ]
    assert verified.commit_id == pins["commit_id"]
    assert verified.verified_certificate_root == pins["verified_certificate_root"]
    assert verified.verified_effect_plan_root == pins["verified_effect_plan_root"]
    assert (
        verified.verified_state_effect_refinement_root
        == pins["verified_state_effect_refinement_root"]
    )
    assert verified.receipt_digest == pins["receipt_digest"]
    assert shell._verified_economic_epoch_is_bound_to_publisher_v1(
        verified, _publisher_token(port), verifier
    )

    outcome = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert outcome.status is CommitOutcomeStatusV1.COMMITTED
    assert outcome.record is not None
    assert _digest(canonical_global_bytes_v1(outcome.record)) == pins["published_record_sha256"]
    assert outcome.state.state_root == pins["published_state_root"] == post_state.state_root
    retry = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert retry.status is CommitOutcomeStatusV1.ALREADY_COMMITTED
    assert retry.record == outcome.record
    assert len(verifier.calls) == 2


def test_genesis_and_migration_prepare_exact_subjects_and_execute_once() -> None:
    profile, _ = _profile()
    pre_state = _state(profile, height=0)
    admission = _initial_state_admission(profile, pre_state)

    # Genesis: pure preparation fixes the exact execution subject.
    prepared = initial_core._prepare_economic_initial_state_for_publisher_v1(admission)
    assert type(prepared) is initial_core._PreparedEconomicInitialStateV1
    assert prepared.kind is EconomicInitialStateKindV1.GENESIS
    assert prepared.expected_image_id == profile.root_image_id
    assert prepared.expected_journal_bytes == admission.certificate.canonical_journal_bytes
    assert prepared.receipt_bytes == admission.receipt_bytes
    assert prepared.certificate_root == _GENESIS_PINS["certificate_root"]
    assert prepared.state.state_root == _GENESIS_PINS["state_root"]
    assert prepared.profile.profile_id == _GENESIS_PINS["profile_id"]
    genesis_verifier = _StrictThreeFieldVerifier()
    verified = initial_shell._verify_economic_initial_state_for_publisher_v1(
        admission, genesis_verifier
    )
    assert type(verified) is _VerifiedEconomicInitialStateV1
    assert genesis_verifier.calls == [
        (admission.receipt_bytes, profile.root_image_id, admission.certificate.canonical_journal_bytes)
    ]
    assert _digest(genesis_verifier.calls[0][2]) == _IN_MEMORY_PUBLISHER_PINS["genesis_journal_sha256"]
    assert verified.certificate_root == prepared.certificate_root
    assert verified.state == pre_state
    assert verified.state is not prepared.state
    assert verified.profile.profile_id == profile.profile_id

    # Kind controls reject before any call in either direction.
    target_profile, migrated_state, migration_admission = (
        _migration_admission_for_source_head(profile, pre_state)
    )
    kind_verifier = _RecordingReceiptVerifier()
    with pytest.raises(ValueError, match="requires a migration admission"):
        initial_shell._verify_economic_migration_for_publisher_v1(
            admission, pre_state, kind_verifier
        )
    with pytest.raises(ValueError, match="requires a genesis admission"):
        initial_shell._verify_economic_initial_state_for_publisher_v1(
            migration_admission, kind_verifier
        )
    assert kind_verifier.calls == []

    # Migration: exact predecessor, exact subject, one call.
    migration_prepared = initial_core._prepare_economic_migration_for_publisher_v1(
        migration_admission, pre_state
    )
    assert migration_prepared.kind is EconomicInitialStateKindV1.MIGRATION
    assert migration_prepared.certificate_root == _MIGRATION_PINS["certificate_root"]
    migration_verifier = _StrictThreeFieldVerifier()
    migrated = initial_shell._verify_economic_migration_for_publisher_v1(
        migration_admission, pre_state, migration_verifier
    )
    assert migration_verifier.calls == [
        (
            migration_admission.receipt_bytes,
            migration_admission.profile.root_image_id,
            migration_admission.certificate.canonical_journal_bytes,
        )
    ]
    assert _digest(migration_verifier.calls[0][2]) == _MIGRATION_PINS["journal_sha256"]
    assert migrated.certificate_root == _MIGRATION_PINS["certificate_root"]
    assert migrated.state == migrated_state
    assert migrated.state.state_root == _MIGRATION_PINS["state_root"]
    assert migrated.profile.profile_id == target_profile.profile_id == _MIGRATION_PINS["profile_id"]

    # Exact predecessor behaviour and exact-subject finishing are unchanged.
    wrong_verifier = _RecordingReceiptVerifier()
    with pytest.raises(ValueError, match="does not match the publisher-owned source head"):
        initial_shell._verify_economic_migration_for_publisher_v1(
            migration_admission,
            replace(pre_state, history_root=_root(93_001)),
            wrong_verifier,
        )
    with pytest.raises(TypeError, match="predecessor state type is not closed"):
        initial_shell._verify_economic_migration_for_publisher_v1(
            migration_admission,
            object(),  # type: ignore[arg-type]
            wrong_verifier,
        )
    with pytest.raises(TypeError, match="prepared initial state type is not closed"):
        initial_shell._execute_prepared_economic_initial_state_v1(
            object(),  # type: ignore[arg-type]
            wrong_verifier,
        )
    with pytest.raises(TypeError, match="prepared initial state type is not closed"):
        initial_core._finish_prepared_economic_initial_state_v1(object())  # type: ignore[arg-type]
    assert wrong_verifier.calls == []


def test_initial_state_executor_detaches_complete_admission_before_io(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    profile, _ = _profile()
    state = _state(profile, height=0)
    admission = _initial_state_admission(profile, state)
    prepared = initial_core._prepare_economic_initial_state_for_publisher_v1(admission)
    fields = object.__getattribute__(prepared, "_fields")
    forged = object.__new__(initial_core._PreparedEconomicInitialStateV1)
    object.__setattr__(forged, "_fields", fields)
    rejected_verifier = _RecordingReceiptVerifier()
    with pytest.raises(TypeError, match="not preparer-constructed"):
        initial_shell._execute_prepared_economic_initial_state_v1(forged, rejected_verifier)
    assert rejected_verifier.calls == []

    malformed = replace(
        fields,
        owned=replace(
            fields.owned,
            certificate=replace(fields.owned.certificate, state_root=_root(93_101)),
        ),
    )
    object.__setattr__(prepared, "_fields", malformed)
    with pytest.raises(ValueError, match="initial state state root mismatch"):
        initial_shell._execute_prepared_economic_initial_state_v1(prepared, rejected_verifier)
    assert rejected_verifier.calls == []

    seen_prepared: list[initial_core._PreparedEconomicInitialStateV1] = []
    original_prepare = initial_shell._prepare_economic_initial_state_for_publisher_v1

    def capturing_prepare(subject: object) -> initial_core._PreparedEconomicInitialStateV1:
        prepared_subject = original_prepare(subject)  # type: ignore[arg-type]
        seen_prepared.append(prepared_subject)
        return prepared_subject

    monkeypatch.setattr(initial_shell, "_prepare_economic_initial_state_for_publisher_v1", capturing_prepare)

    class RelabelingVerifier(_RecordingReceiptVerifier):
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            captured = seen_prepared[-1]
            captured_fields = object.__getattribute__(captured, "_fields")
            object.__setattr__(
                captured,
                "_fields",
                replace(
                    captured_fields,
                    owned=replace(
                        captured_fields.owned,
                        certificate=replace(
                            captured_fields.owned.certificate,
                            state_root=_root(93_102),
                        ),
                    ),
                ),
            )

    verifier = RelabelingVerifier()
    verified = initial_shell._verify_economic_initial_state_for_publisher_v1(admission, verifier)
    assert verifier.calls == [
        (admission.receipt_bytes, profile.root_image_id, admission.certificate.canonical_journal_bytes)
    ]
    assert verified.certificate_root == admission.certificate.certificate_root
    assert verified.state == state
    assert verified.profile.profile_id == profile.profile_id


# --- callback mutation ------------------------------------------------------


def test_callback_mutation_of_caller_graphs_cannot_relabel_witness_or_commit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    expected_head = pre_state.state_root
    expected_profile = profile.profile_id
    seen_candidates: list[proof.EconomicEpochReceiptCandidateV1] = []
    facts_at_prepare: list[tuple[object, ...]] = []
    original_prepare = shell.prepare_economic_epoch_v1

    def capturing_prepare(candidate: proof.EconomicEpochReceiptCandidateV1):
        prepared = original_prepare(candidate)
        seen_candidates.append(candidate)
        facts_at_prepare.append(_witness_facts_from_prepared(prepared))
        return prepared

    monkeypatch.setattr(shell, "prepare_economic_epoch_v1", capturing_prepare)

    class GraphMutatingVerifier(_RecordingReceiptVerifier):
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if not seen_candidates:
                return
            candidate = seen_candidates[-1]
            object.__setattr__(candidate.certificate, "post_state_root", _root(94_001))
            object.__setattr__(candidate.profile, "root_image_id", _root(94_002))
            object.__setattr__(candidate.effect_plan.rows[0], "delta_atoms", 94_003)
            object.__setattr__(candidate.route_journals[0], "post_state_root", _root(94_004))
            object.__setattr__(
                candidate.route_state_disclosures[0].lane_journals[0],
                "post_lane_root",
                _root(94_005),
            )

    verifier = GraphMutatingVerifier()
    port = _commit_port(profile, pre_state, verifier)
    verified, body, _, _, _ = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=b"boundary-graph-mutation-receipt",
        publisher=port,
        receipt_verifier=verifier,
    )

    assert len(verifier.calls) == 2
    assert len(facts_at_prepare) == 1
    assert _witness_facts(verified) == facts_at_prepare[0]
    assert verified.certificate.post_state_root == post_state.state_root
    assert verified.certificate.root_image_id == port.profile.root_image_id
    outcome = port.commit_verified_economic_epoch(
        expected_head=expected_head,
        expected_profile=expected_profile,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert outcome.status is CommitOutcomeStatusV1.COMMITTED
    assert outcome.record is not None
    assert outcome.record.certificate_root == facts_at_prepare[0][1]
    assert outcome.record.post_state_root == post_state.state_root
    assert port.state == post_state


@pytest.mark.parametrize(
    "target",
    ("certificate_root", "certificate.post_state_root", "expected_image_id", "receipt_digest"),
)
def test_callback_mutation_of_unowned_prepared_subject_cannot_relabel_minted_witness(
    monkeypatch: pytest.MonkeyPatch, target: str
) -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    receipt_bytes = f"boundary-relabel-{target}".encode("ascii")
    seen_prepared: list[proof.PreparedEconomicEpochV1] = []
    facts_at_prepare: list[tuple[object, ...]] = []
    original_prepare = shell.prepare_economic_epoch_v1

    def capturing_prepare(candidate: proof.EconomicEpochReceiptCandidateV1):
        prepared = original_prepare(candidate)
        seen_prepared.append(prepared)
        facts_at_prepare.append(_witness_facts_from_prepared(prepared))
        return prepared

    monkeypatch.setattr(shell, "prepare_economic_epoch_v1", capturing_prepare)

    class RelabelingVerifier(_RecordingReceiptVerifier):
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if not seen_prepared:
                return
            prepared = seen_prepared[-1]
            fields = object.__getattribute__(prepared, "_fields")
            if target == "certificate_root":
                replacement = replace(fields, certificate_root=_root(95_001))
            elif target == "certificate.post_state_root":
                replacement = replace(
                    fields,
                    certificate=replace(fields.certificate, post_state_root=_root(95_002)),
                )
            elif target == "expected_image_id":
                replacement = replace(fields, expected_image_id=_root(95_003))
            else:
                replacement = replace(fields, receipt_digest=_root(95_004))
            object.__setattr__(prepared, "_fields", replacement)

    verifier = RelabelingVerifier()
    port = _commit_port(profile, pre_state, verifier)
    verified, body, _, _, _ = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=receipt_bytes,
        publisher=port,
        receipt_verifier=verifier,
    )
    assert len(verifier.calls) == 2
    assert len(facts_at_prepare) == 1
    assert _witness_facts(verified) == facts_at_prepare[0]
    assert verified.certificate.post_state_root == post_state.state_root
    outcome = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert outcome.status is CommitOutcomeStatusV1.COMMITTED
    assert port.state == post_state


def test_epoch_executor_rejects_unconstructed_subclass_and_substituted_subjects_before_io() -> None:
    candidate = _epoch_admission_fixture(1)
    prepared = proof.prepare_economic_epoch_v1(candidate)
    fields = object.__getattribute__(prepared, "_fields")
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(TypeError, match="preparer-constructed"):
        proof.PreparedEconomicEpochV1(object(), fields)
    forged = object.__new__(proof.PreparedEconomicEpochV1)
    object.__setattr__(forged, "_fields", fields)
    with pytest.raises(TypeError, match="not preparer-constructed"):
        shell._execute_prepared_economic_epoch_v1(forged, verifier)

    class Subclass(proof.PreparedEconomicEpochV1):
        pass

    subclass = Subclass(proof._PREPARED_ECONOMIC_EPOCH_TOKEN, fields)
    with pytest.raises(TypeError, match="type is not closed"):
        shell._execute_prepared_economic_epoch_v1(subclass, verifier)

    object.__setattr__(prepared, "_fields", replace(fields, expected_image_id=_root(95_101)))
    with pytest.raises(ValueError, match="execution subject mismatch"):
        shell._execute_prepared_economic_epoch_v1(prepared, verifier)
    assert verifier.calls == []


# --- retained refusals ------------------------------------------------------


def test_forged_direct_handle_subclass_and_field_injection_are_refused() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    port, verified, body, _, _, _ = _publisher_verified_epoch(profile, route, pre_state, post_state)
    before = (port.state, port.records, verified.commit_id)

    def commit(witness: object) -> object:
        return port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=profile.profile_id,
            verified_epoch=witness,  # type: ignore[arg-type]
            body_and_state=body,
        )

    forged = object.__new__(shell.VerifiedEconomicEpochV1)
    with pytest.raises(TypeError, match="not verifier-registered"):
        _ = forged.commit_id
    with pytest.raises(TypeError, match="not verifier-registered"):
        commit(forged)
    authority = shell._verified_economic_epoch_authority_v1(verified)
    with pytest.raises(TypeError, match="verifier-constructed"):
        shell.VerifiedEconomicEpochV1(object(), authority)

    class Subclass(shell.VerifiedEconomicEpochV1):
        pass

    minted_subclass = Subclass(shell._VERIFIED_ECONOMIC_EPOCH_TOKEN, authority)
    with pytest.raises(TypeError, match="handle type is not closed"):
        _ = minted_subclass.commit_id
    with pytest.raises(TypeError, match="commit requires VerifiedEconomicEpochV1"):
        commit(minted_subclass)
    with pytest.raises(TypeError, match="commit requires VerifiedEconomicEpochV1"):
        commit(authority.prepared)
    with pytest.raises(TypeError, match="commit requires VerifiedEconomicEpochV1"):
        commit(authority)

    for name, value in (
        ("_prepared", authority.prepared),
        ("commit_id", _root(96_001)),
        ("_VerifiedEconomicEpochV1__authority", authority),
    ):
        with pytest.raises(AttributeError):
            object.__setattr__(verified, name, value)
        with pytest.raises(AttributeError, match="immutable"):
            setattr(verified, name, value)
    assert (port.state, port.records, verified.commit_id) == before


def test_publisher_identity_requires_the_exact_token_and_verifier_objects() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    first_port, verified, body, verifier, _, _ = _publisher_verified_epoch(
        profile, route, pre_state, post_state
    )
    token = _publisher_token(first_port)
    is_bound = shell._verified_economic_epoch_is_bound_to_publisher_v1

    class AlwaysEqualVerifier(_RecordingReceiptVerifier):
        def __eq__(self, other: object) -> bool:
            return True

        __hash__ = object.__hash__

    lookalike = AlwaysEqualVerifier()
    assert lookalike == verifier
    assert is_bound(verified, token, verifier) is True
    assert is_bound(verified, token, lookalike) is False
    assert is_bound(verified, object(), verifier) is False
    assert is_bound(verified, token, verified.receipt_digest) is False  # type: ignore[arg-type]
    assert is_bound(verified, token, True) is False  # type: ignore[arg-type]
    for bad_token in (True, verified.receipt_digest, None, first_port):
        with pytest.raises(TypeError, match="exact opaque object"):
            is_bound(verified, bad_token, verifier)

    # A fresh handle from the retained record keeps the same identity binding.
    fresh = shell._snapshot_verified_economic_epoch_v1(verified)
    assert fresh is not verified
    assert _witness_facts(fresh) == _witness_facts(verified)
    assert is_bound(fresh, token, verifier) is True

    # Caller-constructed records with same-looking coordinates never bind.
    prepared = shell._verified_economic_epoch_authority_v1(verified).prepared
    lookalike_witnesses = tuple(
        shell.VerifiedEconomicEpochV1(
            shell._VERIFIED_ECONOMIC_EPOCH_TOKEN,
            shell._VerifiedEconomicEpochAuthorityRecordV1(
                prepared=prepared,
                publisher_binding_token=binding_token,
                publisher_verifier_identity=identity,
            ),
        )
        for binding_token, identity in (
            (object(), verifier),
            (token, _RecordingReceiptVerifier()),
            (token, lookalike),
            (None, None),
        )
    )
    research, _, _, _, _ = _verified_epoch(profile, route, pre_state, post_state)
    second_port = _commit_port(profile, pre_state, _RecordingReceiptVerifier())
    before = (first_port.state, first_port.records, second_port.state, second_port.records)
    for witness in (*lookalike_witnesses, research):
        assert witness.commit_id == verified.commit_id
        with pytest.raises(TypeError, match="verified by this exact commit port"):
            first_port.commit_verified_economic_epoch(
                expected_head=pre_state.state_root,
                expected_profile=profile.profile_id,
                verified_epoch=witness,
                body_and_state=body,
            )
    with pytest.raises(TypeError, match="verified by this exact commit port"):
        second_port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=profile.profile_id,
            verified_epoch=verified,
            body_and_state=body,
        )
    object.__setattr__(first_port, "_receipt_verifier", lookalike)
    with pytest.raises(TypeError, match="verified by this exact commit port"):
        first_port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=profile.profile_id,
            verified_epoch=verified,
            body_and_state=body,
        )
    object.__setattr__(first_port, "_receipt_verifier", verifier)
    assert (first_port.state, first_port.records, second_port.state, second_port.records) == before

    outcome = first_port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert outcome.status is CommitOutcomeStatusV1.COMMITTED
    assert first_port.state == post_state


# --- backend failure and replay --------------------------------------------


def test_backend_exception_registers_nothing_and_changes_no_state() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    receipt_bytes = b"boundary-outage-receipt"

    class OutageVerifier(_RecordingReceiptVerifier):
        def __init__(self) -> None:
            super().__init__()
            self.outage = True

        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if self.outage and receipt_bytes == b"boundary-outage-receipt":
                raise RuntimeError("boundary backend outage")

    verifier = OutageVerifier()
    port = _commit_port(profile, pre_state, verifier)
    with pytest.raises(RuntimeError, match="boundary backend outage"):
        _verified_epoch(
            profile,
            route,
            pre_state,
            post_state,
            receipt_bytes=receipt_bytes,
            publisher=port,
            receipt_verifier=verifier,
        )
    assert len(verifier.calls) == 2
    assert _digest(receipt_bytes) not in _registered_receipt_digests()
    assert port.state == pre_state
    assert port.records == ()

    research_verifier = OutageVerifier()
    with pytest.raises(RuntimeError, match="boundary backend outage"):
        _verified_epoch(
            profile,
            route,
            pre_state,
            post_state,
            receipt_bytes=receipt_bytes,
            receipt_verifier=research_verifier,
        )
    assert len(research_verifier.calls) == 1
    assert _digest(receipt_bytes) not in _registered_receipt_digests()

    # The same subject succeeds once the backend recovers, so admission was never the cause.
    verifier.outage = False
    verified, body, _, _, _ = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=receipt_bytes,
        publisher=port,
        receipt_verifier=verifier,
    )
    assert verified.receipt_digest == _digest(receipt_bytes)
    outcome = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert outcome.status is CommitOutcomeStatusV1.COMMITTED
    assert port.state == post_state


def test_changed_receipt_body_or_state_cannot_replay_a_committed_epoch() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    port, verified, body, verifier, _, _ = _publisher_verified_epoch(
        profile, route, pre_state, post_state
    )
    committed = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert committed.status is CommitOutcomeStatusV1.COMMITTED
    assert committed.record is not None
    history = (port.state, port.records)

    exact = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert exact.status is CommitOutcomeStatusV1.ALREADY_COMMITTED
    assert exact.record == committed.record

    changed_body = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=replace(body, receipt_archive_root=_root(97_001)),
    )
    assert changed_body.status is CommitOutcomeStatusV1.BINDING_REJECTED
    assert changed_body.reason == "receipt archive root mismatch"
    changed_state = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=replace(body, post_state=replace(post_state, history_root=_root(97_002))),
    )
    assert changed_state.status is CommitOutcomeStatusV1.BINDING_REJECTED
    assert changed_state.reason == "body post-state root mismatch"

    changed_receipt, _, _, _, _ = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=b"boundary-changed-receipt",
        publisher=port,
        receipt_verifier=verifier,
    )
    assert changed_receipt.commit_id != verified.commit_id
    stale = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=changed_receipt,
        body_and_state=body,
    )
    assert stale.status is CommitOutcomeStatusV1.STALE_HEAD
    assert stale.record is None
    assert (port.state, port.records) == history


# --- durable publisher with the measured bound verifier --------------------


def test_durable_publisher_executes_the_exact_prepared_subject_on_its_bound_verifier(
    tmp_path: Path,
    simulated_measured_publisher_crypto_v1,
) -> None:
    admission, candidate, body = _publisher_fixture_v1(receipt_bytes=b"boundary-durable-epoch")
    backend = _RecordingBackend()
    pipeline, _ = _bound_receipt_verifier_v1(candidate, backend)
    publisher = VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "boundary-durable.sqlite", admission, pipeline
    )
    try:
        source = publisher.head
        outcome = publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            raw_evidence=publisher_raw_evidence_v1(candidate),
            body_and_state=body,
        )
        assert outcome.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert outcome.published_epoch is not None
        epoch_calls = [call for call in backend.calls if call[0] == candidate.receipt_bytes]
        assert epoch_calls == [
            (
                candidate.receipt_bytes,
                candidate.profile.root_image_id,
                candidate.certificate.canonical_journal_bytes,
            )
        ]
        genesis_calls = [call for call in backend.calls if call[0] == admission.receipt_bytes]
        assert genesis_calls == [
            (
                admission.receipt_bytes,
                admission.profile.root_image_id,
                admission.certificate.canonical_journal_bytes,
            )
        ]
        assert outcome.published_epoch.receipt_root == _digest(candidate.receipt_bytes)
        assert outcome.published_epoch.certificate_root == candidate.certificate.certificate_root
        assert publisher.head == outcome.committed_epoch
        retry = publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            raw_evidence=publisher_raw_evidence_v1(candidate),
            body_and_state=body,
        )
        assert retry.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        assert retry.published_epoch == outcome.published_epoch
    finally:
        publisher.close()


def test_durable_backend_rejection_registers_no_witness_and_keeps_genesis(
    tmp_path: Path,
    simulated_measured_publisher_crypto_v1,
) -> None:
    admission, candidate, body = _publisher_fixture_v1(receipt_bytes=b"boundary-durable-rejected")

    class RejectingBackend(_RecordingBackend):
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> object:
            result = super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if receipt_bytes == candidate.receipt_bytes:
                raise ValueError("boundary backend rejected epoch")
            return result

    backend = RejectingBackend()
    pipeline, _ = _bound_receipt_verifier_v1(candidate, backend)
    publisher = VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "boundary-durable-rejected.sqlite", admission, pipeline
    )
    try:
        source = publisher.head
        with pytest.raises(ValueError, match="boundary backend rejected epoch"):
            publisher.publish_economic_epoch(
                expected_source=source,
                candidate=candidate,
                raw_evidence=publisher_raw_evidence_v1(candidate),
                body_and_state=body,
            )
        assert publisher.head == source
        assert len(backend.calls) == 2
        assert _digest(candidate.receipt_bytes) not in _registered_receipt_digests()
    finally:
        publisher.close()


# --- construction conformance ------------------------------------------------


def test_core_root_epoch_and_initial_state_code_has_no_shell_mechanisms() -> None:
    for relative in _CORE_ROOT_EPOCH_MODULES:
        tree = _parse(relative)
        imports = _import_targets(tree)
        assert not any(name.split(".")[0] in {"threading", "weakref"} for name in imports), relative
        assert not any(
            "integration" in name.split(".") or name.startswith("..") for name in imports
        ), relative
        calls = set(_call_names(tree))
        assert not (calls & _VERIFIER_CALL_NAMES), relative
        assert not (calls & _SHELL_MECHANISM_NAMES), relative
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                parameters = [
                    *node.args.posonlyargs,
                    *node.args.args,
                    *node.args.kwonlyargs,
                ]
                names = {parameter.arg for parameter in parameters}
                assert not (names & _PUBLISHER_OBJECT_FIELD_NAMES), (relative, node.name)
            if isinstance(node, ast.ClassDef):
                for item in node.body:
                    if isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name):
                        assert item.target.id not in _PUBLISHER_OBJECT_FIELD_NAMES, (
                            relative,
                            node.name,
                        )
        assert not any(
            isinstance(node, ast.Name) and node.id == "SuccinctReceiptVerifierV1"
            for node in ast.walk(tree)
        ), relative

    proof_tree = _parse(_CORE_ROOT_EPOCH_MODULES[0])
    protocol = [
        node
        for node in proof_tree.body
        if isinstance(node, ast.ClassDef) and node.name == "SuccinctReceiptVerifierV1"
    ]
    assert protocol == []
    assert "SuccinctReceiptVerifierV1" not in proof.__all__
    assert "PreparedEconomicEpochV1" in proof.__all__
    assert "prepare_economic_epoch_v1" in proof.__all__
    assert not (_MOVED_NAMES & set(proof.__all__))
    assert not any(hasattr(proof, name) for name in _MOVED_NAMES)
    assert not any(hasattr(initial_core, name) for name in _MOVED_NAMES)
    import src.core.global_settlement_abi_v1 as facade

    assert not any(hasattr(facade, name) for name in _MOVED_NAMES)
    for relative, marker, _reason in _LEGACY_CORE_CALLBACK_DEBT:
        assert marker in (REPO_ROOT / relative).read_text(encoding="utf-8"), (relative, marker)


def _assert_closed_callback_core_module(relative: str) -> None:
    tree = _parse(relative)
    text = (REPO_ROOT / relative).read_text(encoding="utf-8")
    assert "receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1" not in text, relative
    assert "ZDEXLaneSuccinctReceiptVerifierV1" not in text, relative
    assert not (set(_call_names(tree)) & _VERIFIER_CALL_NAMES), relative
    assert not (set(_call_names(tree)) & _SHELL_MECHANISM_NAMES), relative
    imports = _import_targets(tree)
    assert not any(name.split(".")[0] in {"threading", "weakref"} for name in imports), relative
    assert not any(
        "integration" in name.split(".") or name.startswith("..") for name in imports
    ), relative
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            parameters = [
                *node.args.posonlyargs,
                *node.args.args,
                *node.args.kwonlyargs,
            ]
            assert "receipt_verifier" not in {parameter.arg for parameter in parameters}, (
                relative,
                getattr(node, "name", "<lambda>"),
            )


def test_closed_tokenomics_callback_debt_stays_a_pure_core_boundary() -> None:
    for relative in _CLOSED_TOKENOMICS_CALLBACK_CORE_MODULES:
        _assert_closed_callback_core_module(relative)
    shell_calls = _call_names(_parse(_TOKENOMICS_SHELL_MODULE))
    assert shell_calls.count("verify_succinct_receipt") == 1


def test_closed_fee_leaf_callback_debt_stays_a_pure_core_boundary() -> None:
    for relative in _CLOSED_FEE_LEAF_CALLBACK_CORE_MODULES:
        _assert_closed_callback_core_module(relative)
    shell_calls = _call_names(_parse(_FEE_LEAF_SHELL_MODULE))
    assert shell_calls.count("verify_succinct_receipt") == 1
    assert not any(
        name.startswith("..") and not name.startswith("..core")
        for name in _import_targets(_parse(_FEE_LEAF_SHELL_MODULE))
    )
    # Direct regression: the former core entry point is gone, preparation takes no
    # verifier, and it runs to a prepared subject with no verifier object anywhere.
    assert not hasattr(fee_leaf_core, "verify_zdex_fee_allocation_receipt_v1")
    assert not any(name.startswith("verify_") for name in fee_leaf_core.__all__)
    assert tuple(
        inspect.signature(fee_leaf_core.prepare_zdex_fee_allocation_receipt_v1).parameters
    ) == ("candidate", "governed")
    assert tuple(
        inspect.signature(fee_leaf_shell.verify_zdex_fee_allocation_receipt_v1).parameters
    ) == ("candidate", "governed", "receipt_verifier")
    candidate, governed = _fee_receipt_candidate_fixture()
    prepared = fee_leaf_core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)
    assert type(prepared) is fee_leaf_core.PreparedZDEXFeeAllocationReceiptV1
    assert prepared.expected_image_id == governed._fields.module_release.guest_image_id
    assert prepared.receipt_bytes == candidate.receipt.receipt_bytes
    assert prepared.expected_journal_bytes == canonical_global_bytes_v1(candidate.journal)


def test_closed_purchase_burn_callback_debt_stays_a_pure_preparation_boundary() -> None:
    for relative in _CLOSED_PURCHASE_BURN_PREPARATION_CORE_MODULES:
        _assert_closed_callback_core_module(relative)
    shell_calls = _call_names(_parse(_PURCHASE_BURN_SHELL_MODULE))
    assert shell_calls.count("verify_succinct_receipt") == 1
    assert shell_calls.count("verify_profile_lane_receipt") == 1
    assert not any(
        name.startswith("..") and not name.startswith("..core")
        for name in _import_targets(_parse(_PURCHASE_BURN_SHELL_MODULE))
    )
    # The old core module no longer owns any receipt callback; its remaining Bound
    # registry read is the open debt row named above, not a closed one.
    legacy_text = (REPO_ROOT / _PURCHASE_BURN_LEGACY_CORE_MODULE).read_text(encoding="utf-8")
    assert "receipt_verifier.verify_succinct_receipt(" not in legacy_text
    assert "ZDEXLaneSuccinctReceiptVerifierV1" not in legacy_text
    assert not (set(_call_names(_parse(_PURCHASE_BURN_LEGACY_CORE_MODULE))) & _VERIFIER_CALL_NAMES)
    assert "receipt_verifier.require_binding(" in legacy_text
    assert not any(hasattr(purchase_burn_core, name) for name in _PURCHASE_BURN_MOVED_NAMES)
    assert not any(name.startswith("verify_") for name in purchase_burn_core.__all__)
    assert not any(name.startswith("verify_") for name in purchase_burn_prep.__all__)
    assert tuple(
        inspect.signature(purchase_burn_prep.prepare_zdex_amm_purchase_receipt_v1).parameters
    ) == ("candidate",)
    for relative in (_FEE_LEAF_SHELL_MODULE, _TOKENOMICS_SHELL_MODULE):
        protocol_imports = [
            (node.level, node.module)
            for node in ast.walk(_parse(relative))
            if isinstance(node, ast.ImportFrom)
            and any(alias.name == "ZDEXLaneSuccinctReceiptVerifierV1" for alias in node.names)
        ]
        assert protocol_imports == [(1, "zdex_purchase_burn_receipt_verification_v1")], relative


def test_shell_modules_own_execution_registry_lock_and_consumer_imports() -> None:
    epoch_tree = _parse(_SHELL_MODULES[0])
    epoch_calls = _call_names(epoch_tree)
    assert epoch_calls.count("verify_succinct_receipt") == 1
    assert "Lock" in epoch_calls
    assert "WeakKeyDictionary" in epoch_calls
    assert any(
        isinstance(node, ast.ClassDef) and node.name == "VerifiedEconomicEpochV1"
        for node in epoch_tree.body
    )
    protocol = [
        node
        for node in epoch_tree.body
        if isinstance(node, ast.ClassDef) and node.name == "SuccinctReceiptVerifierV1"
    ]
    assert len(protocol) == 1
    assert [ast.unparse(base) for base in protocol[0].bases] == ["Protocol"]
    initial_tree = _parse(_SHELL_MODULES[1])
    assert _call_names(initial_tree).count("verify_succinct_receipt") == 1
    for relative in _SHELL_MODULES:
        assert not any(
            name.startswith("..") and not name.startswith("..core")
            for name in _import_targets(_parse(relative))
        ), relative
    for relative in _CONSUMER_MODULES:
        for node in ast.walk(_parse(relative)):
            if isinstance(node, ast.ImportFrom) and (node.module or "").startswith("core."):
                assert not ({alias.name for alias in node.names} & _MOVED_NAMES), relative
    assert shell.__all__ == [
        "SuccinctReceiptVerifierV1",
        "VerifiedEconomicEpochV1",
        "verify_economic_epoch_v1",
    ]


# --- semantic mutant ---------------------------------------------------------


def test_execute_before_prepare_mutant_is_killed_by_the_no_call_law() -> None:
    original = shell._verify_economic_epoch_with_publisher_binding_v1
    source = inspect.getsource(original)
    target = (
        "    prepared = prepare_economic_epoch_v1(candidate)\n"
        "    prepared = _execute_prepared_economic_epoch_v1(prepared, receipt_verifier)\n"
    )
    mutant_body = (
        "    receipt_verifier.verify_succinct_receipt(\n"
        "        candidate.receipt_bytes,\n"
        "        expected_image_id=candidate.profile.root_image_id,\n"
        "        expected_journal_bytes=candidate.certificate.canonical_journal_bytes,\n"
        "    )\n"
        "    prepared = prepare_economic_epoch_v1(candidate)\n"
    )
    assert source.count(target) == 1, "ownership mutant target is no longer unique"
    namespace = dict(vars(shell))
    exec(  # noqa: S102 - deliberate structure-preserving mutant of shell ordering
        compile(source.replace(target, mutant_body, 1), "<execute-before-prepare-mutant>", "exec"),
        namespace,
    )
    mutant = namespace[original.__name__]
    tampered = replace(_epoch_admission_fixture(1), receipt_bytes=b"boundary-mutant-receipt")
    expected_request = (
        b"boundary-mutant-receipt",
        tampered.profile.root_image_id,
        tampered.certificate.canonical_journal_bytes,
    )

    # Control: the ordinary law holds on the unmutated shell.
    control_verifier = _RecordingReceiptVerifier()
    with pytest.raises(ValueError, match="receipt root mismatch"):
        original(
            tampered,
            control_verifier,
            publisher_binding_token=None,
            publisher_verifier_identity=None,
        )
    assert control_verifier.calls == []

    # Mutant: the same rejection is raised, but the law's assertion is reachable and fails.
    mutant_verifier = _RecordingReceiptVerifier()
    with pytest.raises(ValueError, match="receipt root mismatch"):
        mutant(
            tampered,
            mutant_verifier,
            publisher_binding_token=None,
            publisher_verifier_identity=None,
        )
    assert mutant_verifier.calls == [expected_request]
    with pytest.raises(AssertionError):
        assert mutant_verifier.calls == []

    # Exact no-effect under both: nothing registered for the tampered receipt.
    assert _digest(b"boundary-mutant-receipt") not in _registered_receipt_digests()
