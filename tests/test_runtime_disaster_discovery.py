"""WholeEconomyDisasterCoverageV1: denominator and evidence-association integrity tests.

Every test follows Arrange / Act / Assert.  Negative tests assert the exact
reject code and that nothing was written or executed.  Fake ports inject
deterministic race boundaries; no sleeps, no network, no wall clock.

Test Quality Contract V2 obligation record (oracle grade 2 throughout: fixed
vectors and decision tables plus independently re-read shell observations; no
theorem or independent implementation is claimed):

1. Provenance. RIPR rewrites every packet HEAD binding and premise together;
   the verifier-owned tree entries, registry relationship, and worktree state
   reveal the forgery. Tier-0 mutants ``TRUST_PACKET_HEAD_BINDING`` and
   ``OMIT_REGISTRY_HEAD`` are killed by the compound and registry tests.
2. Runner snapshot execution. RIPR replaces the live runner path after capture;
   the execution request reveals the captured bytes. Tier-0 mutant
   ``EXECUTE_LIVE_RUNNER_PATH`` is killed by the after-read replacement history.
   Tier-1 mutant ``OMIT_SEALED_IMPORT_ROOT`` is killed by executing the complete
   captured checker import graph. Tier-0 mutant
   ``HASH_EPHEMERAL_SANDBOX_PATH`` is killed by identical real-port executions
   that print ``__file__`` or raise an exception containing that path. Tier-0
   mutant ``COLLIDE_LITERAL_WORKSPACE_TOKEN`` is killed by distinguishing a
   literal marker-shaped string from the typed workspace-path frame.
3. Process lifecycle. RIPR faults selector setup after spawn; the tracked
   process-group terminator reveals cleanup. Tier-0 mutant
   ``CLEANUP_AFTER_SELECTOR_SETUP`` and Tier-1 mutant ``TERM_WITHOUT_KILL`` are
   covered by setup-fault and lock-holding child histories.
4. Resource bounds. Exact 1 MiB and one-byte-over outputs plus timeout histories
   reveal bounded capture. Tier-1 mutant ``OUTPUT_LIMIT_GE_INSTEAD_OF_GT`` and
   Tier-2 mutant ``TIMEOUT_RETURNS_SUCCESS`` are killed by BVA. Tier-0 mutant
   ``HASH_INCOMPLETE_CAPTURE_BYTES`` is killed by replaying concurrent
   dual-stream excess and requiring fixed, stream-separated outcome hashes.
5. Receipt replay. RIPR changes the verifier-side prover result while retaining
   the packet observation; exact observation comparison reveals the forgery.
   Tier-0 mutant ``TRUST_PACKET_OBSERVATION`` is killed before status promotion.
6. Denominator integrity. Fixed manifest vectors and zero/below/exact-floor
   neighbors reveal omissions or inflation. Tier-1 mutants
   ``DROP_GRID_AXIS`` and ``TRUST_PACKET_COUNTS`` are killed by exact roots and
   11,988-cell recomputation.
7. Claim ceiling. Caller-promoted statuses, VM gates, ratios, and whole-economy
   flags reveal exact typed rejections. Tier-0 mutant ``ALLOW_PROMOTION_FLAG``
   is killed by the substitution matrix.

Applicable histories are bounded to one capture/read/execute/replay cycle,
one registered runner substitution, one HEAD transition, and one process tree.
Crash/restart, CAS, outbox, migration, economic reachability, release, mount,
settlement, and production authority remain outside this research checker.
"""

from __future__ import annotations

import copy
import fcntl
import functools
import hashlib
import json
import os
import stat
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, cast

import pytest

from src.core.global_economic_capability_profile_binding_v1 import (
    M6_CAPABILITY_MANIFEST_ROOT_V1,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes
from tools import check_runtime_disaster_discovery_receipt as verifier_shell
from tools import run_runtime_disaster_discovery as runner_shell
from tools import runtime_disaster_discovery_ports_v1 as ports_shell
from tools.check_runtime_disaster_discovery_receipt import (
    read_receipt_bounded,
    verify_receipt_bytes,
)
from tools.run_runtime_disaster_discovery import render_source_pins, run_discovery
from tools.runtime_disaster_discovery import (
    AGGREGATE_FAMILIES_V1,
    CLAIM_CEILING_V1,
    EXPECTED_M6_CAPABILITY_MANIFEST_ROOT_V1,
    LEGACY_BRIDGE_SCHEMAS_V1,
    M6_MANIFEST_HASH_DOMAIN_V1,
    M6_MANIFEST_PATH_V1,
    MAX_RUNNER_OUTPUT_BYTES_V1,
    PACKET_NONCLAIMS_V1,
    PACKET_SCHEMA_V1,
    REGISTRY_PATH_V1,
    REQUIRED_SOURCE_PATHS_V1,
    UNSPECIFIED_V1,
    V1_FLOOR_APPLICABILITY_CELLS,
    V1_FLOOR_CAPABILITIES,
    V1_FLOOR_EXCLUSIONS,
    V1_FLOOR_ROUTES,
    WRITER_INVENTORY_PATH_V1,
    ApplicabilityV1,
    ArtifactRefV1,
    DiscoveryReject,
    EvidenceStatusV1,
    ExecutionObservationV1,
    ExecutionPremiseV1,
    HeadEntryV1,
    InvariantFamilyV1,
    LifecyclePhaseV1,
    NoEffectObservationV1,
    NoEffectOutcomeV1,
    NoEffectSurfaceV1,
    ObligationKeyV1,
    OracleVerdictV1,
    OwnedSourceV1,
    PacketV1,
    PathKindV1,
    RegisteredRunnerV1,
    RejectCodeV1,
    TargetKindV1,
    WitnessKindV1,
    WitnessV1,
    alias_key,
    argv_sha256,
    bind_sources,
    canonical_bytes,
    compute_result_status,
    compute_subject,
    decode_strict_json,
    derive_inventory,
    domain_root,
    domain_separator,
    git_blob_oid,
    parse_registry,
    parse_runner_argv,
    sha256_hex,
)
from tools.runtime_disaster_discovery_ports_v1 import (
    REPO_ROOT,
    FileReadV1,
    GitHeadStateV1,
    HeadLookupV1,
    RunnerExecutionRequestV1,
    ShellPortsV1,
    build_runner_execution_request_v1,
    default_ports,
    execute_registered_runner,
    read_file_bounded,
)

BASE_COMMIT = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
BASE_TREE = "7978c0df78428e806e5f19281df537fe1cfc7451"
OTHER_COMMIT = "1" * 40
OTHER_TREE = "2" * 40
WITNESS_PATH = "tools/test_hygiene_contract_v1.json"
CERTIFICATE_PATH = "docs/testing/TEST_HYGIENE_CONTRACT_V1.md"
REQUIRED_CELL = {
    "target_kind": "CAPABILITY",
    "target_id": "SPOT_LIQUIDITY:exact_in_swap",
    "lifecycle_phase": "ADMISSION",
    "invariant_family": "REPLAY_OCCURRENCE_UNIQUENESS",
}
PREDICATE_ID = "pred_stale_quote_replay"
MUTANT_ID = "mut_drop_nonce_check"
EXIT_RUNNER_ID = "runner_stale_quote_pytest"
PROVER_RUNNER_ID = "runner_stale_quote_prover"
EXIT_ORACLE_ID = "oracle_exit_code"
PROVER_ORACLE_ID = "oracle_lean_prover"
FORMAL_ID = "fo_stale_quote_model_proof"
GOLDEN_UNSPECIFIED_ID = "WEDC1-3ed3589779a5d03063552d739650239f2e8041ca2812056c88993e71dd72dbfc"
EXPECTED_ENTRY_COUNTS = {
    "AGGREGATE_FAMILY": 8,
    "BRIDGE_EXPANSION_AXIS": 125,
    "DANGEROUS_SURFACE": 10,
    "POKAYOKE_SCENARIO": 8,
    "SHAPEFORGE_CROSS_SLICE_INVARIANT": 27,
    "SHAPEFORGE_SCENARIO_TRANSFORM": 28,
    "WRITER_COVERAGE_ROW": 27,
    "WRITER_ENTRYPOINT": 27,
}


# --------------------------------------------------------------------------
# Fake repository ports
# --------------------------------------------------------------------------


def _disk_bytes(path: str) -> bytes:
    return (REPO_ROOT / path).read_bytes()


@dataclass
class FakeRepo:
    files: dict[str, bytes]
    kinds: dict[str, tuple[PathKindV1, bool]] = field(default_factory=dict)
    modes: dict[str, str] = field(default_factory=dict)
    not_in_tree: set[str] = field(default_factory=set)
    submodules: set[str] = field(default_factory=set)
    head_states: list[GitHeadStateV1 | None] = field(
        default_factory=lambda: [GitHeadStateV1(BASE_COMMIT, BASE_TREE, True)]
    )
    observations: dict[str, ExecutionObservationV1] = field(default_factory=dict)
    boundaries: dict[str, Callable[[], None]] = field(default_factory=dict)
    reads: Counter[str] = field(default_factory=Counter)
    executed: list[RegisteredRunnerV1] = field(default_factory=list)
    execution_requests: list[RunnerExecutionRequestV1] = field(default_factory=list)
    probed_trees: set[str] = field(default_factory=set)
    head_calls: int = 0

    def read_file(self, path: str) -> FileReadV1:
        self.reads[path] += 1
        if path in self.kinds:
            kind, ancestry = self.kinds[path]
            return FileReadV1(kind, ancestry, None)
        if path not in self.files:
            return FileReadV1(PathKindV1.MISSING, False, None)
        return FileReadV1(PathKindV1.REGULAR, False, self.files[path])

    def tree_entry(self, tree: str, path: str) -> HeadLookupV1:
        self.probed_trees.add(tree)
        if path in self.not_in_tree or path not in self.files:
            return HeadLookupV1(True, None)
        if path in self.submodules:
            return HeadLookupV1(True, HeadEntryV1(path, "160000", "commit", "3" * 40))
        mode = self.modes.get(path, "100644")
        return HeadLookupV1(True, HeadEntryV1(path, mode, "blob", git_blob_oid(self.files[path])))

    def head_state(self) -> GitHeadStateV1 | None:
        state = self.head_states[min(self.head_calls, len(self.head_states) - 1)]
        self.head_calls += 1
        return state

    def execute(self, request: RunnerExecutionRequestV1) -> ExecutionObservationV1:
        self.execution_requests.append(request)
        runner = request.runner
        self.executed.append(runner)
        return self.observations[runner.runner_id]

    def race_boundary(self, name: str) -> None:
        hook = self.boundaries.get(name)
        if hook is not None:
            hook()

    def ports(self) -> ShellPortsV1:
        return ShellPortsV1(
            read_file=self.read_file,
            tree_entry=self.tree_entry,
            head_state=self.head_state,
            execute=self.execute,
            race_boundary=self.race_boundary,
            now_utc_iso=lambda: "2026-08-27T00:00:00+00:00",
            python_version="3.12.3",
        )


def _base_files() -> dict[str, bytes]:
    files = {path: _disk_bytes(path) for path in REQUIRED_SOURCE_PATHS_V1}
    files[REGISTRY_PATH_V1] = _disk_bytes(REGISTRY_PATH_V1)
    files[WITNESS_PATH] = _disk_bytes(WITNESS_PATH)
    files[CERTIFICATE_PATH] = _disk_bytes(CERTIFICATE_PATH)
    return files


def _registry_obj() -> dict[str, Any]:
    value = json.loads(_disk_bytes(REGISTRY_PATH_V1))
    assert type(value) is dict
    return value


def _encode(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True).encode("utf-8")


def _repo(registry: dict[str, Any] | None = None) -> FakeRepo:
    repo = FakeRepo(files=_base_files())
    if registry is not None:
        repo.files[REGISTRY_PATH_V1] = _encode(registry)
    return repo


def _observation(
    runner_id: str,
    argv: list[str],
    returncode: int | None,
    stdout: bytes,
    timed_out: bool = False,
    output_limit_exceeded: bool = False,
) -> ExecutionObservationV1:
    return ExecutionObservationV1(
        runner_id,
        argv_sha256(argv),
        returncode,
        sha256_hex(stdout),
        sha256_hex(b""),
        timed_out,
        output_limit_exceeded,
    )


EXIT_ARGV = ["python3", "tools/runtime_disaster_discovery.py"]
PROVER_ARGV = ["python3", "tools/runtime_disaster_discovery_inventory_v1.py"]


def _registry_with_required_cell(*, prover: bool = False) -> dict[str, Any]:
    """Fixture registry: one REQUIRED cell, one predicate, one exit-code runner (+ optional prover)."""

    registry = _registry_obj()
    registry["applicability_registry"]["decisions"] = [
        {
            **REQUIRED_CELL,
            "classification": "REQUIRED",
            "basis": {
                "source_path": M6_MANIFEST_PATH_V1,
                "citation": "test fixture: exact_in_swap admission replay",
            },
            "certificate": None,
        }
    ]
    universe = registry["universe"]
    universe["bounds_profiles"] = [
        {
            "bounds_profile_id": "bp_small",
            "max_depth": 3,
            "max_frontier": 32,
            "max_participants": 2,
            "description": "small fixture bounds",
        }
    ]
    universe["bad_predicates"] = [
        {
            "bad_predicate_id": PREDICATE_ID,
            **REQUIRED_CELL,
            "attack_family": "ADVERSARY_MALLORY",
            "bounds_profile_id": "bp_small",
            "closure_mode": "BOUNDED_TEST_SEARCH",
            "ordered_participants": ["alice", "mallory"],
            "statement": "a stale quote receipt is admitted twice within the bounded sequence",
            "required_mutant_ids": [MUTANT_ID],
        }
    ]
    universe["mutants"] = [
        {
            "mutant_id": MUTANT_ID,
            "bad_predicate_id": PREDICATE_ID,
            "description": "drop the nonce monotonicity check",
        }
    ]
    registry["oracle_registry"]["oracles"] = [
        {
            "oracle_id": EXIT_ORACLE_ID,
            "kind": "EXIT_CODE_ONLY",
            "version": "1",
            "verifier_identity": "pytest_exit_code",
        }
    ]
    registry["runner_registry"]["runners"] = [
        {
            "runner_id": EXIT_RUNNER_ID,
            "bad_predicate_id": PREDICATE_ID,
            "oracle_id": EXIT_ORACLE_ID,
            "argv": EXIT_ARGV,
            "argv_sha256": argv_sha256(EXIT_ARGV),
            "timeout_s": 60,
            "witness_artifact_path": WITNESS_PATH,
        }
    ]
    if prover:
        registry["oracle_registry"]["oracles"].append(
            {
                "oracle_id": PROVER_ORACLE_ID,
                "kind": "FORMAL_PROVER",
                "version": "lean4",
                "verifier_identity": "lean_lake_build",
            }
        )
        universe["formal_obligations"] = [
            {
                "formal_obligation_id": FORMAL_ID,
                "bad_predicate_id": PREDICATE_ID,
                "certificate_kind": "MODEL_PROOF",
                "theorem_id": "thm_no_stale_quote_replay",
                "oracle_id": PROVER_ORACLE_ID,
                "certificate_artifact_path": CERTIFICATE_PATH,
            }
        ]
        registry["runner_registry"]["runners"].append(
            {
                "runner_id": PROVER_RUNNER_ID,
                "bad_predicate_id": PREDICATE_ID,
                "oracle_id": PROVER_ORACLE_ID,
                "argv": PROVER_ARGV,
                "argv_sha256": argv_sha256(PROVER_ARGV),
                "timeout_s": 60,
                "witness_artifact_path": None,
            }
        )
    return registry


def _run(repo: FakeRepo) -> PacketV1:
    return run_discovery(repo.ports())


def _reject_of(action: Callable[[], object]) -> DiscoveryReject:
    with pytest.raises(DiscoveryReject) as info:
        action()
    return info.value


def _packet_bytes(packet: PacketV1) -> bytes:
    return _encode(packet.to_canonical())


def _tampered(
    packet: PacketV1, mutate: Callable[[dict[str, Any]], None], *, reroot: bool = True
) -> bytes:
    obj = packet.to_canonical()
    core = cast(dict[str, Any], obj["canonical_core"])
    mutate(core)
    if reroot:
        obj["receipt_root"] = domain_root("wedc1-receipt-root", obj["canonical_core"])
    return _encode(obj)


def _verify(receipt: bytes, repo: FakeRepo) -> dict[str, object]:
    return verify_receipt_bytes(receipt, repo.ports())


# --------------------------------------------------------------------------
# Positive deterministic generation
# --------------------------------------------------------------------------


def test_positive_generation_is_deterministic_and_verifies() -> None:
    # Arrange
    repo = _repo()

    # Act
    packet = _run(repo)
    again = _run(_repo())
    report = _verify(_packet_bytes(packet), _repo())

    # Assert
    core = packet.core
    assert canonical_bytes(core.to_canonical()) == canonical_bytes(again.core.to_canonical())
    assert packet.receipt_root == again.receipt_root
    assert packet.receipt_root == domain_root("wedc1-receipt-root", core.to_canonical())
    assert (
        core.denominator.capabilities,
        core.denominator.routes,
        core.denominator.exclusions,
    ) == (103, 4, 4)
    assert core.denominator.targets == 111
    assert core.denominator.applicability_cells == 11988 == V1_FLOOR_APPLICABILITY_CELLS
    assert core.denominator.classification_counts == {
        "APPLICABILITY_UNKNOWN": 11988,
        "BLOCKED_SEMANTICS": 0,
        "NOT_APPLICABLE_PROVED": 0,
        "REQUIRED": 0,
    }
    assert core.denominator.obligation_rows == 11988 == core.denominator.unspecified_rows
    assert core.denominator.predicate_rows == 0
    assert core.denominator.inventory_entry_counts == EXPECTED_ENTRY_COUNTS
    assert core.denominator.composition_pending_entries == sum(EXPECTED_ENTRY_COUNTS.values())
    assert core.denominator.state.value == "DENOMINATOR_INCOMPLETE"
    assert core.denominator.coverage_ratio == "WITHHELD"
    assert (
        core.denominator.historical_strict_release_closure
        == "0_OF_967_MANIFEST_DERIVED_MINIMUM_EVIDENCE_CELLS"
    )
    assert core.denominator.evidence_status_counts["UNSPECIFIED_SEMANTICS"] == 11988
    assert core.flags.to_canonical() == {
        "integrity_ok": True,
        "execution_complete": False,
        "bounded_discovery_complete": False,
        "formal_closure_complete": False,
        "whole_economy_claim_allowed": False,
    }
    assert core.execution_premise is ExecutionPremiseV1.CLEAN_WORKTREE_HEAD_BOUND
    assert core.results == ()
    assert core.claim_ceiling == CLAIM_CEILING_V1
    assert core.nonclaims == PACKET_NONCLAIMS_V1
    assert core.subject.commit == BASE_COMMIT and core.subject.tree == BASE_TREE
    assert report["ok"] is True and report["findings"] == []
    assert report["receipt_root"] == packet.receipt_root
    assert repo.executed == []
    assert all(count == 1 for count in repo.reads.values())
    assert set(repo.reads) == set(REQUIRED_SOURCE_PATHS_V1) | {REGISTRY_PATH_V1}


def test_packet_json_and_report_ordering_are_stable() -> None:
    # Arrange
    packet = _run(_repo())

    # Act
    rendered = json.dumps(packet.to_canonical(), indent=2, sort_keys=True)
    reparsed = json.loads(rendered)

    # Assert
    assert list(reparsed) == ["canonical_core", "receipt_root", "schema", "telemetry"]
    assert reparsed["telemetry"] == {
        "duration_ms": packet.telemetry["duration_ms"],
        "generated_at": "2026-08-27T00:00:00+00:00",
        "python_version": "3.12.3",
        "stdout_previews": [],
    }
    assert "generated_at" not in json.dumps(reparsed["canonical_core"])
    universe_roots = reparsed["canonical_core"]["universe_roots"]
    assert list(universe_roots) == sorted(universe_roots)
    assert "%" not in json.dumps(reparsed["canonical_core"])


def test_packet_core_mappings_are_deeply_immutable_after_construction() -> None:
    # Arrange
    packet = _run(_repo())
    root_before = packet.core.receipt_root

    # Act / Assert
    with pytest.raises(TypeError):
        packet.core.universe_roots["CAPABILITY"] = "0x" + "ff" * 32  # type: ignore[index]
    with pytest.raises(TypeError):
        packet.core.denominator.classification_counts["APPLICABILITY_UNKNOWN"] = 0  # type: ignore[index]
    with pytest.raises(TypeError):
        packet.core.denominator.inventory_entry_counts["WRITER_ENTRYPOINT"] = 0  # type: ignore[index]
    with pytest.raises(TypeError):
        packet.core.denominator.evidence_status_counts["UNSPECIFIED_SEMANTICS"] = 0  # type: ignore[index]
    assert packet.core.receipt_root == root_before


def test_real_ports_smoke_run_and_verify() -> None:
    # Arrange
    ports = default_ports()

    # Act
    packet = run_discovery(ports)
    report = verify_receipt_bytes(_packet_bytes(packet), default_ports())

    # Assert
    assert packet.core.flags.integrity_ok is True
    assert packet.core.flags.whole_economy_claim_allowed is False
    assert packet.core.denominator.applicability_cells == 11988
    assert packet.core.denominator.inventory_entry_counts == EXPECTED_ENTRY_COUNTS
    assert report["ok"] is True
    assert report["production_authority"] == "NONE"


def test_render_source_pins_matches_registry_and_is_read_only() -> None:
    # Arrange
    registry = parse_registry(_disk_bytes(REGISTRY_PATH_V1))
    before = {path: _disk_bytes(path) for path in REQUIRED_SOURCE_PATHS_V1}

    # Act
    pins = render_source_pins(default_ports())

    # Assert
    assert [pin["sha256"] for pin in pins] == [pin.sha256 for pin in registry.source_pins]
    assert [pin["byte_size"] for pin in pins] == [pin.byte_size for pin in registry.source_pins]
    assert [pin["blob_oid"] for pin in pins] == [pin.blob_oid for pin in registry.source_pins]
    assert {path: _disk_bytes(path) for path in REQUIRED_SOURCE_PATHS_V1} == before


# --------------------------------------------------------------------------
# Identity, hashing, and alias rules
# --------------------------------------------------------------------------


def test_canonical_encoding_matches_repository_helpers_and_m6_root() -> None:
    # Arrange
    sample = {"b": [1, "x", True, None], "a": {"z": "ü", "y": []}}
    manifest = decode_strict_json(_disk_bytes(M6_MANIFEST_PATH_V1), name="m6", max_bytes=1 << 20)

    # Act
    root = domain_root(M6_MANIFEST_HASH_DOMAIN_V1, manifest)

    # Assert
    assert canonical_bytes(sample) == canonical_json_bytes(sample)
    assert domain_separator("wedc1-obligation-key") == domain_sep_bytes(
        "wedc1-obligation-key", version=1
    )
    assert root == M6_CAPABILITY_MANIFEST_ROOT_V1 == EXPECTED_M6_CAPABILITY_MANIFEST_ROOT_V1


def test_obligation_id_is_hash_stable_and_prefixed() -> None:
    # Arrange
    key = ObligationKeyV1(
        semantic_requirement_root=EXPECTED_M6_CAPABILITY_MANIFEST_ROOT_V1,
        target_kind=TargetKindV1.CAPABILITY,
        target_id="SPOT_LIQUIDITY:exact_in_swap",
        ordered_participants=(),
        lifecycle_phase=LifecyclePhaseV1.ADMISSION,
        invariant_family=InvariantFamilyV1.REPLAY_OCCURRENCE_UNIQUENESS,
        attack_family=UNSPECIFIED_V1,
        bad_predicate_id=UNSPECIFIED_V1,
        bounds_profile_id=UNSPECIFIED_V1,
        closure_mode=UNSPECIFIED_V1,
    )
    expected = (
        "WEDC1-"
        + hashlib.sha256(
            domain_separator("wedc1-obligation-key") + canonical_bytes(key.to_canonical())
        ).hexdigest()
    )

    # Act
    obligation_id = key.obligation_id

    # Assert
    assert obligation_id == expected == GOLDEN_UNSPECIFIED_ID
    assert len(obligation_id) == len("WEDC1-") + 64


def test_grid_ids_are_unique_and_ordered_by_manifest_phase_family() -> None:
    # Arrange
    packet = _run(_repo())
    registry = parse_registry(_disk_bytes(REGISTRY_PATH_V1))

    # Act
    repo = _repo()
    owned = {path: _owned(repo, path) for path in REQUIRED_SOURCE_PATHS_V1}
    bound = {source.pin.path: source for source in bind_sources(registry.source_pins, owned)}
    inventory = derive_inventory(
        registry, bound, subject_commit=BASE_COMMIT, subject_tree=BASE_TREE, artifacts={}
    )

    # Assert
    ids = [row.obligation_id for row in inventory.rows]
    assert len(ids) == len(set(ids)) == 11988
    assert inventory.rows[0].key.target_id == "ASSET_TRANSFER:account_lifecycle"
    assert inventory.rows[0].key.lifecycle_phase is LifecyclePhaseV1.ADMISSION
    assert inventory.rows[0].key.invariant_family is InvariantFamilyV1.VALUE_CONSERVATION
    assert inventory.rows[-1].key.target_id == "caller_selected_route_or_proof_profile"
    assert inventory.rows[-1].key.target_kind is TargetKindV1.EXPLICIT_EXCLUSION
    assert inventory.inventory_root() == packet.core.inventory_root
    assert {
        entry.entry_id for entry in inventory.entries if entry.universe.value == "AGGREGATE_FAMILY"
    } == {family.value for family in AGGREGATE_FAMILIES_V1}


def _owned(repo: FakeRepo, path: str) -> OwnedSourceV1:
    read = repo.read_file(path)
    lookup = repo.tree_entry(BASE_TREE, path)
    return OwnedSourceV1(
        path, read.kind, read.symlink_in_ancestry, read.data, lookup.entry, lookup.available
    )


@pytest.mark.parametrize(
    ("ids", "code"),
    [
        (["pred_a", "pred_a"], RejectCodeV1.ID_DUPLICATE),
        (["pred_a", "Pred-A"], RejectCodeV1.ID_ALIAS_COLLISION),
        (["pred_a", "pred.a"], RejectCodeV1.ID_ALIAS_COLLISION),
        (["pred_a", "PRED_A"], RejectCodeV1.ID_ALIAS_COLLISION),
    ],
)
def test_duplicate_and_alias_predicate_ids_reject(ids: list[str], code: RejectCodeV1) -> None:
    # Arrange
    registry = _registry_with_required_cell()
    predicate = registry["universe"]["bad_predicates"][0]
    registry["universe"]["bad_predicates"] = [
        {**predicate, "bad_predicate_id": item} for item in ids
    ]

    # Act
    reject = _reject_of(lambda: parse_registry(_encode(registry)))

    # Assert
    assert reject.code is code


@pytest.mark.parametrize("bad_id", ["pred a", "pred_a ", "prеd_a", "", "-pred", "pred​"])
def test_whitespace_confusable_and_malformed_ids_reject(bad_id: str) -> None:
    # Arrange
    registry = _registry_with_required_cell()
    registry["universe"]["bad_predicates"][0]["bad_predicate_id"] = bad_id
    registry["universe"]["mutants"][0]["bad_predicate_id"] = bad_id

    # Act
    reject = _reject_of(lambda: parse_registry(_encode(registry)))

    # Assert
    assert reject.code in (RejectCodeV1.TOKEN_INVALID, RejectCodeV1.VALUE_OUT_OF_RANGE)
    assert alias_key("Exact-In Swap") == alias_key("exact_in_swap")


# --------------------------------------------------------------------------
# Hard floors and denominator monotonicity
# --------------------------------------------------------------------------


def test_hard_floor_constants_are_exact() -> None:
    assert (V1_FLOOR_CAPABILITIES, V1_FLOOR_ROUTES, V1_FLOOR_EXCLUSIONS) == (103, 4, 4)
    assert V1_FLOOR_APPLICABILITY_CELLS == (103 + 4 + 4) * 9 * 12 == 11988
    assert (
        len(LifecyclePhaseV1) == 9
        and len(InvariantFamilyV1) == 12
        and len(AGGREGATE_FAMILIES_V1) == 8
    )


@pytest.mark.parametrize(
    ("floor", "code"),
    [
        (
            {"capabilities": 102, "routes": 4, "exclusions": 4, "applicability_cells": 110 * 108},
            RejectCodeV1.DENOMINATOR_BELOW_FLOOR,
        ),
        (
            {"capabilities": 103, "routes": 3, "exclusions": 4, "applicability_cells": 110 * 108},
            RejectCodeV1.DENOMINATOR_BELOW_FLOOR,
        ),
        (
            {"capabilities": 103, "routes": 4, "exclusions": 3, "applicability_cells": 110 * 108},
            RejectCodeV1.DENOMINATOR_BELOW_FLOOR,
        ),
        (
            {"capabilities": 103, "routes": 4, "exclusions": 4, "applicability_cells": 11987},
            RejectCodeV1.DENOMINATOR_MISMATCH,
        ),
        (
            {"capabilities": 1, "routes": 1, "exclusions": 1, "applicability_cells": 3 * 108},
            RejectCodeV1.DENOMINATOR_BELOW_FLOOR,
        ),
    ],
)
def test_registry_cannot_lower_any_hard_floor_number(
    floor: dict[str, int], code: RejectCodeV1
) -> None:
    # Arrange
    registry = _registry_obj()
    registry["denominator_floor"] = floor
    repo = _repo(registry)

    # Act
    reject = _reject_of(lambda: _run(repo))

    # Assert
    assert reject.code is code
    assert repo.executed == []


def test_registry_may_raise_the_floor_but_manifest_must_then_meet_it() -> None:
    # Arrange
    registry = _registry_obj()
    registry["denominator_floor"] = {
        "capabilities": 104,
        "routes": 4,
        "exclusions": 4,
        "applicability_cells": 112 * 108,
    }

    # Act
    reject = _reject_of(lambda: _run(_repo(registry)))

    # Assert
    assert reject.code is RejectCodeV1.DENOMINATOR_BELOW_FLOOR


def _manifest_mutant(mutate: Callable[[dict[str, Any]], None]) -> bytes:
    manifest = json.loads(_disk_bytes(M6_MANIFEST_PATH_V1))
    mutate(manifest)
    return _encode(manifest)


def _repo_with_repinned_source(path: str, data: bytes) -> FakeRepo:
    registry = _registry_obj()
    for pin in registry["source_pins"]:
        if pin["path"] == path:
            pin["sha256"] = sha256_hex(data)
            pin["blob_oid"] = git_blob_oid(data)
            pin["byte_size"] = len(data)
    repo = _repo(registry)
    repo.files[path] = data
    return repo


@pytest.mark.parametrize(
    "mutate",
    [
        lambda manifest: manifest["lanes"][1]["capabilities"].remove("lp_burn"),
        lambda manifest: manifest["required_cross_lane_routes"].pop(),
        lambda manifest: manifest["explicit_exclusions"].pop(),
    ],
)
def test_omitted_capability_route_or_exclusion_rejects_even_when_repinned(
    mutate: Callable[[dict[str, Any]], None],
) -> None:
    # Arrange
    data = _manifest_mutant(mutate)
    repinned = _repo_with_repinned_source(M6_MANIFEST_PATH_V1, data)
    unpinned = _repo()
    unpinned.files[M6_MANIFEST_PATH_V1] = data

    # Act
    repinned_reject = _reject_of(lambda: _run(repinned))
    unpinned_reject = _reject_of(lambda: _run(unpinned))

    # Assert
    assert repinned_reject.code is RejectCodeV1.MANIFEST_ROOT_DRIFT
    assert unpinned_reject.code in (RejectCodeV1.SOURCE_SIZE_DRIFT, RejectCodeV1.SOURCE_HASH_DRIFT)


def test_omitted_inventory_category_rejects() -> None:
    # Arrange: drop a dangerous surface that bridge axes reference and an entire writer entry
    surfaces = json.loads(_disk_bytes("tools/acceptance_tcb_dangerous_surfaces.json"))
    surfaces["surfaces"] = []
    writers = json.loads(_disk_bytes(WRITER_INVENTORY_PATH_V1))
    writers["entries"] = writers["entries"][1:]

    # Act
    surface_reject = _reject_of(
        lambda: _run(
            _repo_with_repinned_source(
                "tools/acceptance_tcb_dangerous_surfaces.json", _encode(surfaces)
            )
        )
    )
    writer_reject = _reject_of(
        lambda: _run(_repo_with_repinned_source(WRITER_INVENTORY_PATH_V1, _encode(writers)))
    )

    # Assert
    assert surface_reject.code is RejectCodeV1.INVENTORY_SOURCE_INVALID
    assert writer_reject.code is RejectCodeV1.INVENTORY_SOURCE_INVALID
    assert "unregistered writer" in writer_reject.detail


def test_packet_omitting_one_cell_or_filtering_denominator_rejects() -> None:
    # Arrange
    packet = _run(_repo())

    def drop_cell(core: dict[str, Any]) -> None:
        core["denominator"]["applicability_cells"] = 11987

    def empty(core: dict[str, Any]) -> None:
        core["denominator"]["applicability_cells"] = 0
        core["denominator"]["targets"] = 0

    def filtered_root(core: dict[str, Any]) -> None:
        core["cells_root"] = "0x" + "ab" * 32

    # Act / Assert
    assert (
        _reject_of(lambda: _verify(_tampered(packet, drop_cell), _repo())).code
        is RejectCodeV1.DENOMINATOR_BELOW_FLOOR
    )
    assert (
        _reject_of(lambda: _verify(_tampered(packet, empty), _repo())).code
        is RejectCodeV1.DENOMINATOR_EMPTY
    )
    assert (
        _reject_of(lambda: _verify(_tampered(packet, filtered_root), _repo())).code
        is RejectCodeV1.INVENTORY_ROOT_MISMATCH
    )
    assert (
        _reject_of(lambda: _verify(_tampered(packet, drop_cell, reroot=False), _repo())).code
        is RejectCodeV1.RECEIPT_ROOT_MISMATCH
    )


def test_stale_not_applicable_certificate_never_leaves_the_denominator() -> None:
    # Arrange
    registry = _registry_obj()
    certificate = {
        "formal_obligation_id": "fo_na",
        "theorem_id": "thm_na",
        "subject_commit": OTHER_COMMIT,
        "subject_tree": OTHER_TREE,
        "artifact_path": CERTIFICATE_PATH,
        "artifact_sha256": sha256_hex(_disk_bytes(CERTIFICATE_PATH)),
    }
    registry["applicability_registry"]["decisions"] = [
        {
            **REQUIRED_CELL,
            "classification": "NOT_APPLICABLE_PROVED",
            "basis": {"source_path": M6_MANIFEST_PATH_V1, "citation": "stale"},
            "certificate": certificate,
        }
    ]
    current = copy.deepcopy(registry)
    current["applicability_registry"]["decisions"][0]["certificate"].update(
        subject_commit=BASE_COMMIT, subject_tree=BASE_TREE
    )
    bad_hash = copy.deepcopy(current)
    bad_hash["applicability_registry"]["decisions"][0]["certificate"]["artifact_sha256"] = "0" * 64

    # Act
    stale_packet = _run(_repo(registry))
    current_packet = _run(_repo(current))
    reject = _reject_of(lambda: _run(_repo(bad_hash)))

    # Assert
    assert stale_packet.core.denominator.classification_counts["APPLICABILITY_UNKNOWN"] == 11988
    assert stale_packet.core.denominator.stale_certificate_cells == 1
    assert current_packet.core.denominator.classification_counts["NOT_APPLICABLE_PROVED"] == 1
    assert current_packet.core.denominator.applicability_cells == 11988
    assert current_packet.core.denominator.state.value == "DENOMINATOR_INCOMPLETE"
    assert reject.code is RejectCodeV1.ARTIFACT_HASH_MISMATCH


# --------------------------------------------------------------------------
# Hostile JSON shapes
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("data", "code"),
    [
        (b'{"a": 1, "a": 2}', RejectCodeV1.JSON_DUPLICATE_KEY),
        (b'{"a": 1.5}', RejectCodeV1.JSON_FLOAT_FORBIDDEN),
        (b'{"a": 1e3}', RejectCodeV1.JSON_FLOAT_FORBIDDEN),
        (b'{"a": NaN}', RejectCodeV1.JSON_NONFINITE_FORBIDDEN),
        (b'{"a": Infinity}', RejectCodeV1.JSON_NONFINITE_FORBIDDEN),
        (b'{"a": -Infinity}', RejectCodeV1.JSON_NONFINITE_FORBIDDEN),
        (b"[" * 40 + b"]" * 40, RejectCodeV1.JSON_TOO_DEEP),
        (b"[" * 5000 + b"]" * 5000, RejectCodeV1.JSON_TOO_DEEP),
        (b"\xef\xbb\xbf{}", RejectCodeV1.JSON_ENCODING),
        (b"\xff\xfe", RejectCodeV1.JSON_ENCODING),
        (b"{", RejectCodeV1.JSON_MALFORMED),
        (b"{}" + b" " * 20000, RejectCodeV1.JSON_TOO_LARGE),
    ],
)
def test_hostile_json_shapes_reject(data: bytes, code: RejectCodeV1) -> None:
    # Act
    reject = _reject_of(lambda: decode_strict_json(data, name="hostile", max_bytes=16384))

    # Assert
    assert reject.code is code


@pytest.mark.parametrize(
    ("mutate", "code"),
    [
        (lambda registry: registry.update(registry_version=True), RejectCodeV1.TYPE_MISMATCH),
        (
            lambda registry: registry["denominator_floor"].update(capabilities=True),
            RejectCodeV1.TYPE_MISMATCH,
        ),
        (
            lambda registry: registry["source_pins"][0].update(byte_size=True),
            RejectCodeV1.TYPE_MISMATCH,
        ),
        (lambda registry: registry.update(extra="x"), RejectCodeV1.UNKNOWN_FIELD),
        (lambda registry: registry.pop("nonclaims"), RejectCodeV1.MISSING_FIELD),
        (
            lambda registry: registry.update(claim_ceiling="PRODUCTION_READY"),
            RejectCodeV1.CALLER_SUPPLIED_CEILING,
        ),
        (
            lambda registry: registry["implementation_base"].update(commit=OTHER_COMMIT),
            RejectCodeV1.SUBJECT_COMMIT_INVALID,
        ),
        (
            lambda registry: registry["historical_baseline"].update(
                minimum_release_evidence_cell_count=966
            ),
            RejectCodeV1.VALUE_OUT_OF_RANGE,
        ),
        (
            lambda registry: registry["universe"]["lifecycle_phases"].pop(),
            RejectCodeV1.ENUMERATION_DRIFT,
        ),
        (
            lambda registry: registry["universe"]["invariant_families"][4].update(aggregate=False),
            RejectCodeV1.AGGREGATE_FAMILY_MISSING,
        ),
        (
            lambda registry: registry["composition_registry"].update(state="COMPLETE"),
            RejectCodeV1.VALUE_OUT_OF_RANGE,
        ),
    ],
)
def test_registry_shape_and_ceiling_mutants_reject(
    mutate: Callable[[dict[str, Any]], None], code: RejectCodeV1
) -> None:
    # Arrange
    registry = _registry_obj()
    mutate(registry)

    # Act
    reject = _reject_of(lambda: parse_registry(_encode(registry)))

    # Assert
    assert reject.code is code


def test_registry_duplicate_json_key_and_nan_reject_before_use() -> None:
    # Arrange
    text = _disk_bytes(REGISTRY_PATH_V1).decode("utf-8")
    duplicated = text.replace(
        '"registry_version": 1,', '"registry_version": 1, "registry_version": 1,', 1
    ).encode()
    nan = text.replace('"registry_version": 1,', '"registry_version": NaN,', 1).encode()
    repo = _repo()

    # Act
    repo.files[REGISTRY_PATH_V1] = duplicated
    duplicate_reject = _reject_of(lambda: _run(repo))
    repo.files[REGISTRY_PATH_V1] = nan
    nan_reject = _reject_of(lambda: _run(repo))

    # Assert
    assert duplicate_reject.code is RejectCodeV1.JSON_DUPLICATE_KEY
    assert nan_reject.code is RejectCodeV1.JSON_NONFINITE_FORBIDDEN
    assert repo.executed == []


# --------------------------------------------------------------------------
# Runner registry: fixed argv only
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("argv", "code"),
    [
        (["python3", "-c", "print('ok')"], RejectCodeV1.RUNNER_ARGV_FORBIDDEN),
        (["python3", "-m", "pytest"], RejectCodeV1.RUNNER_ARGV_FORBIDDEN),
        ("python3 tools/check_x.py", RejectCodeV1.RUNNER_ARGV_FORBIDDEN),
        (["bash", "tools/check_x.sh"], RejectCodeV1.RUNNER_ARGV_FORBIDDEN),
        (["python3", "/usr/bin/evil.py"], RejectCodeV1.PATH_INVALID),
        (["python3", "../tools/check_x.py"], RejectCodeV1.PATH_INVALID),
        (["python3", "src/core/dex.py"], RejectCodeV1.RUNNER_ARGV_FORBIDDEN),
        (["python3", "tools/check_x.py", "--exec", "rm"], RejectCodeV1.RUNNER_ARGV_FORBIDDEN),
        (["python3"], RejectCodeV1.RUNNER_ARGV_FORBIDDEN),
    ],
)
def test_arbitrary_runner_argv_rejects_with_zero_executor_calls(
    argv: object, code: RejectCodeV1
) -> None:
    # Arrange
    registry = _registry_with_required_cell()
    registry["runner_registry"]["runners"][0]["argv"] = argv
    repo = _repo(registry)
    repo.observations[EXIT_RUNNER_ID] = _observation(EXIT_RUNNER_ID, EXIT_ARGV, 0, b"ok")

    # Act
    reject = _reject_of(lambda: _run(repo))
    direct = _reject_of(lambda: parse_runner_argv(argv, "argv"))

    # Assert
    assert reject.code is code and direct.code is code
    assert repo.executed == []


def test_unknown_command_field_and_argv_hash_drift_reject() -> None:
    # Arrange
    with_command = _registry_with_required_cell()
    with_command["runner_registry"]["runners"][0]["command"] = "python3 -c print(ok)"
    drifted = _registry_with_required_cell()
    drifted["runner_registry"]["runners"][0]["argv_sha256"] = argv_sha256(
        ["python3", "tools/check_x.py"]
    )

    # Act
    command_reject = _reject_of(lambda: parse_registry(_encode(with_command)))
    drift_reject = _reject_of(lambda: parse_registry(_encode(drifted)))

    # Assert
    assert command_reject.code is RejectCodeV1.UNKNOWN_FIELD
    assert drift_reject.code is RejectCodeV1.RUNNER_ARGV_HASH_MISMATCH


def test_valid_but_unpinned_runner_source_rejects_before_executor_call() -> None:
    # Arrange
    registry = _registry_with_required_cell()
    argv = ["python3", "tools/check_test_hygiene_v1.py"]
    registry["runner_registry"]["runners"][0].update(argv=argv, argv_sha256=argv_sha256(argv))
    repo = _repo(registry)

    # Act
    reject = _reject_of(lambda: _run(repo))

    # Assert
    assert reject.code is RejectCodeV1.RUNNER_SOURCE_UNBOUND
    assert repo.executed == []


def test_registered_runner_source_missing_from_captured_head_rejects_before_executor_call() -> None:
    # Arrange
    repo = _exit_repo(0, b"ok")
    repo.not_in_tree.add(EXIT_ARGV[1])

    # Act
    reject = _reject_of(lambda: _run(repo))

    # Assert
    assert reject.code is RejectCodeV1.RUNNER_SOURCE_UNBOUND
    assert repo.executed == []


@pytest.mark.parametrize(
    ("mutate", "code"),
    [
        (
            lambda registry: registry["universe"]["bad_predicates"][0].update(
                bounds_profile_id="bp_missing"
            ),
            RejectCodeV1.BOUNDS_PROFILE_UNREGISTERED,
        ),
        (
            lambda registry: registry["runner_registry"]["runners"][0].update(
                oracle_id="oracle_missing"
            ),
            RejectCodeV1.ORACLE_UNREGISTERED,
        ),
        (
            lambda registry: registry["universe"]["mutants"].clear(),
            RejectCodeV1.MUTANT_SET_MISMATCH,
        ),
        (
            lambda registry: registry["universe"]["mutants"][0].update(
                bad_predicate_id="pred_missing"
            ),
            RejectCodeV1.PREDICATE_UNREGISTERED,
        ),
        (
            lambda registry: registry["applicability_registry"]["decisions"].clear(),
            RejectCodeV1.PREDICATE_CELL_NOT_REQUIRED,
        ),
        (
            lambda registry: registry["applicability_registry"]["decisions"][0].update(
                classification="BLOCKED_SEMANTICS"
            ),
            RejectCodeV1.PREDICATE_CELL_NOT_REQUIRED,
        ),
        (
            lambda registry: registry["applicability_registry"]["decisions"][0].update(
                classification="APPLICABILITY_UNKNOWN"
            ),
            RejectCodeV1.APPLICABILITY_DECISION_INVALID,
        ),
        (
            lambda registry: registry["applicability_registry"]["decisions"][0].update(
                target_id="SPOT_LIQUIDITY:ghost"
            ),
            RejectCodeV1.PREDICATE_CELL_NOT_REQUIRED,
        ),
        (
            lambda registry: registry["universe"]["formal_obligations"].append(
                {
                    "formal_obligation_id": "fo_x",
                    "bad_predicate_id": PREDICATE_ID,
                    "certificate_kind": "MODEL_PROOF",
                    "theorem_id": "t",
                    "oracle_id": EXIT_ORACLE_ID,
                    "certificate_artifact_path": CERTIFICATE_PATH,
                }
            ),
            RejectCodeV1.VALUE_OUT_OF_RANGE,
        ),
    ],
)
def test_missing_bound_oracle_mutant_or_proof_obligation_rejects(
    mutate: Callable[[dict[str, Any]], None], code: RejectCodeV1
) -> None:
    # Arrange
    registry = _registry_with_required_cell()
    mutate(registry)

    # Act
    reject = _reject_of(lambda: parse_registry(_encode(registry)))

    # Assert
    assert reject.code is code


# --------------------------------------------------------------------------
# Evidence lattice: exit zero is never proof
# --------------------------------------------------------------------------


def _exit_repo(
    returncode: int | None,
    stdout: bytes,
    *,
    timed_out: bool = False,
    output_limit_exceeded: bool = False,
    witness: bool = True,
) -> FakeRepo:
    registry = _registry_with_required_cell()
    if not witness:
        registry["runner_registry"]["runners"][0]["witness_artifact_path"] = None
    repo = _repo(registry)
    repo.observations[EXIT_RUNNER_ID] = _observation(
        EXIT_RUNNER_ID,
        EXIT_ARGV,
        returncode,
        stdout,
        timed_out,
        output_limit_exceeded,
    )
    return repo


def test_generic_exit_zero_with_test_looking_stdout_stays_not_witnessed_in_tests() -> None:
    # Arrange
    output = b"===== 4213 passed in 3.14s =====\nPROVED\nMODEL_PROVED_UNREACHABLE"
    repo = _exit_repo(0, output, witness=False)

    # Act
    packet = _run(repo)
    report = _verify(_packet_bytes(packet), _exit_repo(0, output, witness=False))

    # Assert
    assert [runner.runner_id for runner in repo.executed] == [EXIT_RUNNER_ID]
    (result,) = packet.core.results
    assert result.computed_status is EvidenceStatusV1.NOT_WITNESSED_IN_TESTS
    assert result.oracle_verdict.value == "PASS"
    assert (
        result.witness.kind.value == "REPLAY_TRANSCRIPT"
        and result.witness.replay_sha256 == result.observation.replay_sha256
    )
    assert result.required_mutant_ids == (MUTANT_ID,) and result.killed_mutant_ids == ()
    assert all(item.outcome.value == "UNOBSERVED" for item in result.no_effect_observations)
    assert packet.core.denominator.evidence_status_counts["NOT_WITNESSED_IN_TESTS"] == 1
    assert (
        packet.core.denominator.predicate_rows == 1
        and packet.core.denominator.obligation_rows == 11988
    )
    assert (
        packet.core.flags.execution_complete is False
        and packet.core.flags.bounded_discovery_complete is False
    )
    report_counts = cast(dict[str, int], report["evidence_status_counts"])
    assert report["ok"] is True and report_counts["NOT_WITNESSED_IN_TESTS"] == 1


def test_output_limit_excess_is_inconclusive_even_with_exit_zero() -> None:
    # Arrange
    repo = _exit_repo(0, b"partial", output_limit_exceeded=True, witness=False)

    # Act
    packet = _run(repo)

    # Assert
    (result,) = packet.core.results
    assert result.observation.output_limit_exceeded is True
    assert result.oracle_verdict is OracleVerdictV1.INCONCLUSIVE
    assert result.computed_status is EvidenceStatusV1.INCONCLUSIVE


@pytest.mark.parametrize(
    ("returncode", "stdout", "timed_out", "witness", "status"),
    [
        (1, b"passed passed passed", False, False, EvidenceStatusV1.INCONCLUSIVE),
        (None, b"", True, True, EvidenceStatusV1.INCONCLUSIVE),
        (1, b"witness found", False, True, EvidenceStatusV1.WITNESSED_REACHABLE),
    ],
)
def test_fabricated_stdout_timeouts_and_bad_traces(
    returncode: int | None, stdout: bytes, timed_out: bool, witness: bool, status: EvidenceStatusV1
) -> None:
    # Arrange
    repo = _exit_repo(returncode, stdout, timed_out=timed_out, witness=witness)

    # Act
    packet = _run(repo)
    report = _verify(
        _packet_bytes(packet), _exit_repo(returncode, stdout, timed_out=timed_out, witness=witness)
    )

    # Assert
    (result,) = packet.core.results
    assert result.computed_status is status
    assert report["ok"] is True
    if status is EvidenceStatusV1.WITNESSED_REACHABLE:
        assert result.witness.artifact is not None and result.witness.artifact.path == WITNESS_PATH
        assert result.witness.artifact.sha256 == sha256_hex(_disk_bytes(WITNESS_PATH))


def test_mutable_worktree_execution_is_external_premise() -> None:
    # Arrange
    repo = _exit_repo(0, b"passed", witness=False)
    repo.head_states = [GitHeadStateV1(BASE_COMMIT, BASE_TREE, False)]

    # Act
    packet = _run(repo)

    # Assert
    assert packet.core.execution_premise is ExecutionPremiseV1.EXTERNAL_PREMISE_MUTABLE_WORKTREE
    assert packet.core.results[0].computed_status is EvidenceStatusV1.EXTERNAL_PREMISE


def test_registry_must_match_captured_head_for_clean_execution_premise() -> None:
    # Arrange
    producer = _repo()
    producer.not_in_tree.add(REGISTRY_PATH_V1)
    packet = _run(producer)
    verifier = _repo()
    verifier.not_in_tree.add(REGISTRY_PATH_V1)

    # Act
    reject = _reject_of(
        lambda: _verify(
            _tampered(
                packet,
                lambda core: core.update(execution_premise="CLEAN_WORKTREE_HEAD_BOUND"),
            ),
            verifier,
        )
    )

    # Assert
    assert packet.core.execution_premise is ExecutionPremiseV1.EXTERNAL_PREMISE_MUTABLE_WORKTREE
    assert reject.code is RejectCodeV1.FLAGS_MISMATCH


def test_rows_without_results_are_search_pending_or_unknown_reachability() -> None:
    # Arrange
    registry = _registry_with_required_cell()
    registry["runner_registry"]["runners"] = []
    repo_no_runner = _repo(registry)

    # Act
    packet = _run(repo_no_runner)

    # Assert
    assert packet.core.denominator.evidence_status_counts["UNKNOWN_REACHABILITY"] == 1
    assert packet.core.results == ()


def test_formal_prover_with_registered_certificate_closes_model_only_on_exact_binding() -> None:
    # Arrange
    def prover_repo() -> FakeRepo:
        repo = _repo(_registry_with_required_cell(prover=True))
        repo.observations[EXIT_RUNNER_ID] = _observation(EXIT_RUNNER_ID, EXIT_ARGV, 0, b"passed")
        repo.observations[PROVER_RUNNER_ID] = _observation(
            PROVER_RUNNER_ID, PROVER_ARGV, 0, b"lake build ok"
        )
        return repo

    # Act
    packet = _run(prover_repo())
    report = _verify(_packet_bytes(packet), prover_repo())
    missing = prover_repo()
    del missing.files[CERTIFICATE_PATH]
    missing_packet = _run(missing)

    # Assert
    statuses = {result.runner_id: result.computed_status for result in packet.core.results}
    assert statuses == {
        EXIT_RUNNER_ID: EvidenceStatusV1.NOT_WITNESSED_IN_TESTS,
        PROVER_RUNNER_ID: EvidenceStatusV1.MODEL_PROVED_UNREACHABLE,
    }
    assert packet.core.denominator.evidence_status_counts["MODEL_PROVED_UNREACHABLE"] == 1
    assert packet.core.flags.formal_closure_complete is False
    assert report["ok"] is True
    assert {r.runner_id: r.computed_status for r in missing_packet.core.results}[
        PROVER_RUNNER_ID
    ] is EvidenceStatusV1.INCONCLUSIVE


def _prover_repo_factory() -> FakeRepo:
    repo = _repo(_registry_with_required_cell(prover=True))
    repo.observations[EXIT_RUNNER_ID] = _observation(EXIT_RUNNER_ID, EXIT_ARGV, 0, b"passed")
    repo.observations[PROVER_RUNNER_ID] = _observation(PROVER_RUNNER_ID, PROVER_ARGV, 0, b"ok")
    return repo


@functools.lru_cache(maxsize=1)
def _cached_prover_packet() -> PacketV1:
    """Deterministic and immutable, so one derivation serves every mutant case."""

    return _run(_prover_repo_factory())


def _prover_packet() -> tuple[PacketV1, Callable[[], FakeRepo]]:
    return _cached_prover_packet(), _prover_repo_factory


def _prover_result(core: dict[str, Any]) -> dict[str, Any]:
    return next(result for result in core["results"] if result["runner_id"] == PROVER_RUNNER_ID)


def _exit_result(core: dict[str, Any]) -> dict[str, Any]:
    return next(result for result in core["results"] if result["runner_id"] == EXIT_RUNNER_ID)


@pytest.mark.parametrize(
    ("mutate", "code"),
    [
        (
            lambda core: _exit_result(core).update(computed_status="MODEL_PROVED_UNREACHABLE"),
            RejectCodeV1.CALLER_PROMOTED_STATUS,
        ),
        (
            lambda core: _exit_result(core).update(computed_status="RUNTIME_REFINEMENT_CLOSED"),
            RejectCodeV1.CALLER_PROMOTED_STATUS,
        ),
        (
            lambda core: _exit_result(core).update(oracle_verdict="FAIL"),
            RejectCodeV1.CALLER_PROMOTED_STATUS,
        ),
        (
            lambda core: _exit_result(core).update(
                formal_certificates=_prover_result(core)["formal_certificates"]
            ),
            RejectCodeV1.FORMAL_OBLIGATION_UNREGISTERED,
        ),
        (
            lambda core: _prover_result(core)["formal_certificates"][0].update(
                formal_obligation_id="fo_fake"
            ),
            RejectCodeV1.FORMAL_OBLIGATION_UNREGISTERED,
        ),
        (
            lambda core: _prover_result(core)["formal_certificates"][0].update(
                theorem_id="thm_other"
            ),
            RejectCodeV1.FORMAL_OBLIGATION_UNREGISTERED,
        ),
        (
            lambda core: _prover_result(core)["formal_certificates"][0].update(
                kind="REFINEMENT_PROOF"
            ),
            RejectCodeV1.FORMAL_OBLIGATION_UNREGISTERED,
        ),
        (
            lambda core: _prover_result(core)["formal_certificates"][0]["artifact"].update(
                sha256="0" * 64
            ),
            RejectCodeV1.ARTIFACT_HASH_MISMATCH,
        ),
        (
            lambda core: _prover_result(core)["formal_certificates"][0].update(
                toolchain_manifest_root="0x" + "cd" * 32
            ),
            RejectCodeV1.CALLER_PROMOTED_STATUS,
        ),
        (
            lambda core: _prover_result(core).update(claim_ceiling="PRODUCTION_CLOSED"),
            RejectCodeV1.CALLER_SUPPLIED_CEILING,
        ),
        (
            lambda core: _prover_result(core).update(vm_gate_effect="CLOSES"),
            RejectCodeV1.VM_GATE_CLOSURE_FORBIDDEN,
        ),
        (
            lambda core: _prover_result(core).update(contributes_to_vm_gates=["VM-07"]),
            RejectCodeV1.VM_GATE_CLOSURE_FORBIDDEN,
        ),
        (
            lambda core: _prover_result(core).update(required_mutant_ids=[]),
            RejectCodeV1.MUTANT_SET_MISMATCH,
        ),
        (
            lambda core: _prover_result(core).update(killed_mutant_ids=["mut_ghost"]),
            RejectCodeV1.MUTANT_UNREGISTERED,
        ),
        (
            lambda core: _prover_result(core)["cells"][0].update(lifecycle_phase="CLAIM"),
            RejectCodeV1.RESULT_CELL_MISMATCH,
        ),
        (
            lambda core: _prover_result(core).update(predicate_root="0x" + "ef" * 32),
            RejectCodeV1.PREDICATE_ROOT_MISMATCH,
        ),
        (
            lambda core: _prover_result(core).update(bounds_root="0x" + "ef" * 32),
            RejectCodeV1.BOUNDS_ROOT_MISMATCH,
        ),
        (
            lambda core: _prover_result(core).update(schema_root="0x" + "ef" * 32),
            RejectCodeV1.SCHEMA_ROOT_MISMATCH,
        ),
        (
            lambda core: _prover_result(core).update(source_pins_root="0x" + "ef" * 32),
            RejectCodeV1.SOURCE_PINS_ROOT_MISMATCH,
        ),
        (
            lambda core: _prover_result(core).update(subject_root="0x" + "ef" * 32),
            RejectCodeV1.SUBJECT_MISMATCH,
        ),
        (
            lambda core: _prover_result(core).update(
                argv_sha256=argv_sha256(["python3", "tools/other.py"])
            ),
            RejectCodeV1.RUNNER_ARGV_HASH_MISMATCH,
        ),
        (
            lambda core: _prover_result(core)["key"].update(lifecycle_phase="CLAIM"),
            RejectCodeV1.OBLIGATION_ID_MISMATCH,
        ),
        (
            lambda core: _prover_result(core)["no_effect_observations"].pop(),
            RejectCodeV1.NO_EFFECT_OBSERVATIONS_INCOMPLETE,
        ),
        (
            lambda core: _prover_result(core)["witness"].update(
                kind="BAD_TRACE_WITNESS",
                artifact={"path": WITNESS_PATH, "sha256": sha256_hex(_disk_bytes(WITNESS_PATH))},
                replay_sha256=None,
            ),
            RejectCodeV1.ARTIFACT_UNBOUND,
        ),
        (
            lambda core: core.update(results=list(reversed(core["results"]))),
            RejectCodeV1.RESULT_ORDER_INVALID,
        ),
        (
            lambda core: core.update(results=core["results"] + [core["results"][0]]),
            RejectCodeV1.RESULT_DUPLICATE,
        ),
        (lambda core: core.update(results=core["results"][:1]), RejectCodeV1.RESULT_MISSING),
        (
            lambda core: core["results"].insert(
                0, {**core["results"][1], "runner_id": "runner_ghost"}
            ),
            RejectCodeV1.RESULT_UNEXPECTED,
        ),
        (
            lambda core: core["results"].append(
                {**core["results"][1], "runner_id": "runner_zzz_ghost"}
            ),
            RejectCodeV1.RESULT_UNEXPECTED,
        ),
        (
            lambda core: core["flags"].update(whole_economy_claim_allowed=True),
            RejectCodeV1.WHOLE_ECONOMY_CLAIM_FORBIDDEN,
        ),
        (
            lambda core: core["flags"].update(formal_closure_complete=True),
            RejectCodeV1.FLAGS_MISMATCH,
        ),
        (
            lambda core: core.update(claim_ceiling="PRODUCTION"),
            RejectCodeV1.CALLER_SUPPLIED_CEILING,
        ),
        (
            lambda core: core.update(nonclaims=["closed 100 percent"]),
            RejectCodeV1.PERCENTAGE_FORBIDDEN,
        ),
        (
            lambda core: core.update(nonclaims=["different nonclaims"]),
            RejectCodeV1.NONCLAIMS_MISMATCH,
        ),
        (
            lambda core: core["denominator"].update(coverage_ratio="COMPLETE"),
            RejectCodeV1.DENOMINATOR_MISMATCH,
        ),
        (
            lambda core: core["denominator"]["evidence_status_counts"].update(
                NOT_WITNESSED_IN_TESTS=0, MODEL_PROVED_UNREACHABLE=2
            ),
            RejectCodeV1.DENOMINATOR_MISMATCH,
        ),
        (lambda core: core["subject"].update(commit=OTHER_COMMIT), RejectCodeV1.SUBJECT_MISMATCH),
        (lambda core: core["subject"].update(tree=OTHER_TREE), RejectCodeV1.SUBJECT_MISMATCH),
        (
            lambda core: core["subject"].update(toolchain_manifest_root="0x" + "ab" * 32),
            RejectCodeV1.SUBJECT_MISMATCH,
        ),
        (
            lambda core: core["subject"].update(registry_sha256="0" * 64),
            RejectCodeV1.REGISTRY_STALE,
        ),
        (
            lambda core: core["source_bindings"][0]["pin"].update(blob_oid="0" * 40),
            RejectCodeV1.SOURCE_PINS_ROOT_MISMATCH,
        ),
        (
            lambda core: core.update(execution_premise="EXTERNAL_PREMISE_MUTABLE_WORKTREE"),
            RejectCodeV1.FLAGS_MISMATCH,
        ),
        (
            lambda core: core["source_bindings"][0].update(head_binding="NOT_IN_HEAD"),
            RejectCodeV1.SOURCE_PINS_ROOT_MISMATCH,
        ),
        (
            lambda core: core.update(
                schema="zenodex/stateful-disaster-search-expansion-receipt/v1"
            ),
            RejectCodeV1.SCHEMA_MISMATCH,
        ),
        (lambda core: core.update(bonus="x"), RejectCodeV1.UNKNOWN_FIELD),
    ],
)
def test_receipt_mutants_reject_with_exact_codes(
    mutate: Callable[[dict[str, Any]], None], code: RejectCodeV1
) -> None:
    # Arrange
    packet, make = _prover_packet()

    # Act
    reject = _reject_of(lambda: _verify(_tampered(packet, mutate), make()))

    # Assert
    assert reject.code is code


def test_compound_head_provenance_rewrite_cannot_forge_clean_premise() -> None:
    # Arrange: the checker source is byte-pinned but absent from the captured
    # tree, and the worktree is independently reported dirty.
    source_path = "tools/runtime_disaster_discovery_packet_v1.py"
    producer = _repo()
    producer.not_in_tree.add(source_path)
    producer.head_states = [GitHeadStateV1(BASE_COMMIT, BASE_TREE, False)]
    packet = _run(producer)

    def forge_clean_head(core: dict[str, Any]) -> None:
        core["execution_premise"] = "CLEAN_WORKTREE_HEAD_BOUND"
        for binding in core["source_bindings"]:
            binding["head_binding"] = "HEAD_BLOB_MATCH"

    receipt = _tampered(packet, forge_clean_head)
    verifier = _repo()
    verifier.not_in_tree.add(source_path)
    verifier.head_states = [GitHeadStateV1(BASE_COMMIT, BASE_TREE, False)]

    # Act
    reject = _reject_of(lambda: _verify(receipt, verifier))

    # Assert: verifier-owned HEAD observations outrank packet-supplied claims.
    assert reject.code is RejectCodeV1.SOURCE_PINS_ROOT_MISMATCH
    assert verifier.executed == []


def test_receipt_replays_runner_and_rejects_forged_execution_observation() -> None:
    # Arrange
    packet = _run(_prover_repo_factory())
    verifier = _prover_repo_factory()
    verifier.observations[PROVER_RUNNER_ID] = _observation(
        PROVER_RUNNER_ID,
        PROVER_ARGV,
        1,
        b"prover failed on replay",
    )

    # Act
    reject = _reject_of(lambda: _verify(_packet_bytes(packet), verifier))

    # Assert
    assert reject.code is RejectCodeV1.RUNNER_OBSERVATION_MISMATCH
    assert {runner.runner_id for runner in verifier.executed} == {
        EXIT_RUNNER_ID,
        PROVER_RUNNER_ID,
    }


def test_receipt_root_mismatch_and_telemetry_outside_root() -> None:
    # Arrange
    packet, make = _prover_packet()
    obj = packet.to_canonical()
    telemetry = cast(dict[str, Any], obj["telemetry"])
    telemetry["duration_ms"] = 999_999
    telemetry["stdout_previews"] = ["PASSED everything"]
    telemetry_changed = _encode(obj)
    unrooted = _tampered(
        packet, lambda core: core["flags"].update(execution_complete=True), reroot=False
    )

    # Act
    report = _verify(telemetry_changed, make())
    reject = _reject_of(lambda: _verify(unrooted, make()))

    # Assert
    assert report["ok"] is True and report["receipt_root"] == packet.receipt_root
    assert reject.code is RejectCodeV1.RECEIPT_ROOT_MISMATCH


@pytest.mark.parametrize("schema", sorted(LEGACY_BRIDGE_SCHEMAS_V1))
def test_legacy_bridge_receipts_are_categorically_rejected(schema: str) -> None:
    # Arrange
    legacy = _encode(
        {
            "schema": schema,
            "command": ["python3", "-c", "print('ok')"],
            "stdout": "ok",
            "ok": True,
            "status": "passed",
        }
    )

    # Act
    reject = _reject_of(lambda: _verify(legacy, _repo()))

    # Assert
    assert reject.code is RejectCodeV1.LEGACY_BRIDGE_RECEIPT_REJECTED
    assert (
        _reject_of(lambda: _verify(_encode({"schema": "zenodex/other/v9"}), _repo())).code
        is RejectCodeV1.SCHEMA_MISMATCH
    )


# --------------------------------------------------------------------------
# Source pins, paths, and subject drift
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("field_name", "value", "code"),
    [
        ("sha256", "0" * 64, RejectCodeV1.SOURCE_HASH_DRIFT),
        ("blob_oid", "0" * 40, RejectCodeV1.SOURCE_BLOB_DRIFT),
        ("byte_size", 12, RejectCodeV1.SOURCE_SIZE_DRIFT),
        ("git_mode", "100755", RejectCodeV1.SOURCE_GIT_MODE_INVALID),
        ("git_mode", "120000", RejectCodeV1.SOURCE_GIT_MODE_INVALID),
        ("git_mode", "160000", RejectCodeV1.SOURCE_SUBMODULE),
        ("path", "/etc/passwd", RejectCodeV1.PATH_INVALID),
        ("path", "../docs/x.json", RejectCodeV1.PATH_INVALID),
        ("path", "docs\\research\\x.json", RejectCodeV1.PATH_INVALID),
        ("path", "docs/./x.json", RejectCodeV1.PATH_INVALID),
        (
            "path",
            "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json ",
            RejectCodeV1.PATH_INVALID,
        ),
    ],
)
def test_stale_or_hostile_source_pins_reject(
    field_name: str, value: object, code: RejectCodeV1
) -> None:
    # Arrange
    registry = _registry_obj()
    pin = next(pin for pin in registry["source_pins"] if pin["path"] == M6_MANIFEST_PATH_V1)
    pin[field_name] = value
    repo = _repo(registry)

    # Act
    reject = _reject_of(lambda: _run(repo))

    # Assert
    assert (
        reject.code in (code, RejectCodeV1.SOURCE_PIN_MISSING)
        if field_name == "path"
        else reject.code is code
    )
    assert repo.executed == []


def test_stale_toolchain_pin_rejects() -> None:
    # Arrange
    registry = _registry_obj()
    pin = next(
        pin for pin in registry["source_pins"] if pin["path"] == "lean-mathlib/lean-toolchain"
    )
    pin["sha256"] = "0" * 64

    # Act
    reject = _reject_of(lambda: _run(_repo(registry)))

    # Assert
    assert reject.code is RejectCodeV1.SOURCE_HASH_DRIFT


@pytest.mark.parametrize(
    ("kind", "ancestry", "code"),
    [
        (PathKindV1.SYMLINK, False, RejectCodeV1.PATH_SYMLINK),
        (PathKindV1.REGULAR, True, RejectCodeV1.PATH_SYMLINK),
        (PathKindV1.FIFO, False, RejectCodeV1.PATH_NOT_REGULAR_FILE),
        (PathKindV1.DEVICE, False, RejectCodeV1.PATH_NOT_REGULAR_FILE),
        (PathKindV1.DIRECTORY, False, RejectCodeV1.PATH_NOT_REGULAR_FILE),
        (PathKindV1.MISSING, False, RejectCodeV1.PATH_NOT_REGULAR_FILE),
        (PathKindV1.OVERSIZE, False, RejectCodeV1.SOURCE_OVERSIZE),
    ],
)
def test_symlink_fifo_device_missing_and_oversize_sources_reject(
    kind: PathKindV1, ancestry: bool, code: RejectCodeV1
) -> None:
    # Arrange
    repo = _repo()
    repo.kinds[M6_MANIFEST_PATH_V1] = (kind, ancestry)

    # Act
    reject = _reject_of(lambda: _run(repo))

    # Assert
    assert reject.code is code


def test_submodule_and_uncommitted_semantic_source_reject() -> None:
    # Arrange
    submodule = _repo()
    submodule.submodules.add("tools/stateful_scenario_bridge.py")
    uncommitted = _repo()
    uncommitted.not_in_tree.add(M6_MANIFEST_PATH_V1)
    unprobed = _repo()
    unprobed.tree_entry = lambda _tree, _path: HeadLookupV1(False, None)  # type: ignore[assignment]

    # Act / Assert
    assert _reject_of(lambda: _run(submodule)).code is RejectCodeV1.SOURCE_SUBMODULE
    assert _reject_of(lambda: _run(uncommitted)).code is RejectCodeV1.SOURCE_BLOB_DRIFT
    assert _reject_of(lambda: _run(unprobed)).code is RejectCodeV1.GIT_PROBE_UNAVAILABLE


def test_swapped_subject_commit_or_tree_is_visible_in_subject_and_rejected_by_verifier() -> None:
    # Arrange
    packet = _run(_repo())
    other = _repo()
    other.head_states = [GitHeadStateV1(OTHER_COMMIT, BASE_TREE, True)]

    # Act
    reject = _reject_of(lambda: _verify(_packet_bytes(packet), other))

    # Assert
    assert reject.code is RejectCodeV1.SUBJECT_MISMATCH and "commit or tree" in reject.detail


def test_head_moving_between_capture_read_and_execute_boundaries_rejects() -> None:
    # Arrange
    moved_after_read = _exit_repo(0, b"ok", witness=False)
    moved_after_read.head_states = [
        GitHeadStateV1(BASE_COMMIT, BASE_TREE, True),
        GitHeadStateV1(OTHER_COMMIT, OTHER_TREE, True),
    ]
    moved_after_execute = _exit_repo(0, b"ok", witness=False)
    moved_after_execute.head_states = [
        GitHeadStateV1(BASE_COMMIT, BASE_TREE, True),
        GitHeadStateV1(BASE_COMMIT, BASE_TREE, True),
        GitHeadStateV1(BASE_COMMIT, OTHER_TREE, True),
    ]
    packet = _run(_repo())
    verifier_moved = _repo()
    verifier_moved.head_states = [
        GitHeadStateV1(BASE_COMMIT, BASE_TREE, True),
        GitHeadStateV1(OTHER_COMMIT, BASE_TREE, True),
    ]
    unavailable = _repo()
    unavailable.head_states = [None]

    # Act
    read_reject = _reject_of(lambda: _run(moved_after_read))
    execute_reject = _reject_of(lambda: _run(moved_after_execute))
    verify_reject = _reject_of(lambda: _verify(_packet_bytes(packet), verifier_moved))
    unavailable_reject = _reject_of(lambda: _run(unavailable))

    # Assert
    assert read_reject.code is RejectCodeV1.HEAD_MOVED and read_reject.detail == "after_read"
    assert (
        execute_reject.code is RejectCodeV1.HEAD_MOVED and execute_reject.detail == "after_execute"
    )
    assert moved_after_read.executed == []
    assert verify_reject.code is RejectCodeV1.HEAD_MOVED
    assert unavailable_reject.code is RejectCodeV1.GIT_PROBE_UNAVAILABLE


def test_runner_execution_request_uses_captured_bytes_after_path_replacement() -> None:
    # Arrange
    repo = _exit_repo(0, b"ok", witness=False)
    runner_path = EXIT_ARGV[1]
    captured = repo.files[runner_path]
    replacement = b"raise SystemExit('replacement executed')\n"
    repo.boundaries["after_read"] = lambda: repo.files.__setitem__(
        runner_path,
        replacement,
    )

    # Act
    packet = _run(repo)

    # Assert
    assert len(packet.core.results) == 1
    assert len(repo.execution_requests) == 1
    request_sources = dict(repo.execution_requests[0].source_tree)
    assert set(request_sources) == set(REQUIRED_SOURCE_PATHS_V1) | {REGISTRY_PATH_V1}
    assert request_sources[runner_path] == captured
    assert request_sources[runner_path] != repo.files[runner_path]


def test_source_swapped_at_injected_race_boundary_binds_first_read_and_verifier_detects_swap() -> (
    None
):
    # Arrange
    repo = _repo()
    original = repo.files[M6_MANIFEST_PATH_V1]
    swapped = original.replace(b'"lp_burn"', b'"lp_bxrn"')
    repo.boundaries["after_read"] = lambda: repo.files.update({M6_MANIFEST_PATH_V1: swapped})

    # Act
    packet = _run(repo)
    verifier_repo = _repo()
    verifier_repo.files[M6_MANIFEST_PATH_V1] = swapped
    reject = _reject_of(lambda: _verify(_packet_bytes(packet), verifier_repo))

    # Assert
    assert repo.reads[M6_MANIFEST_PATH_V1] == 1
    assert packet.core.subject.m6_manifest_root == EXPECTED_M6_CAPABILITY_MANIFEST_ROOT_V1
    binding = next(b for b in packet.core.source_bindings if b.pin.path == M6_MANIFEST_PATH_V1)
    assert binding.pin.sha256 == sha256_hex(original)
    assert reject.code is RejectCodeV1.SOURCE_HASH_DRIFT


# --------------------------------------------------------------------------
# Real filesystem port: no-follow walk and byte ceilings
# --------------------------------------------------------------------------


def test_read_file_bounded_refuses_symlinks_fifos_and_oversize_before_allocation(
    tmp_path: Path,
) -> None:
    # Arrange
    root = tmp_path / "repo"
    (root / "real").mkdir(parents=True)
    (root / "real" / "a.json").write_bytes(b'{"ok": true}')
    (root / "real" / "big.bin").write_bytes(b"x" * 33)
    os.symlink(root / "real", root / "linkdir")
    os.symlink(root / "real" / "a.json", root / "real" / "alias.json")
    os.mkfifo(root / "real" / "pipe")

    # Act
    regular = read_file_bounded(root, "real/a.json", 32)
    ancestry = read_file_bounded(root, "linkdir/a.json", 32)
    symlink = read_file_bounded(root, "real/alias.json", 32)
    fifo = read_file_bounded(root, "real/pipe", 32)
    oversize = read_file_bounded(root, "real/big.bin", 32)
    exact = read_file_bounded(root, "real/big.bin", 33)
    directory = read_file_bounded(root, "real", 32)
    missing = read_file_bounded(root, "real/nope.json", 32)

    # Assert
    assert regular == FileReadV1(PathKindV1.REGULAR, False, b'{"ok": true}')
    assert ancestry == FileReadV1(PathKindV1.SYMLINK, True, None)
    assert symlink == FileReadV1(PathKindV1.SYMLINK, False, None)
    assert fifo == FileReadV1(PathKindV1.FIFO, False, None)
    assert oversize == FileReadV1(PathKindV1.OVERSIZE, False, None)
    assert exact.kind is PathKindV1.REGULAR and exact.data == b"x" * 33
    assert directory.kind is PathKindV1.DIRECTORY and missing.kind is PathKindV1.MISSING
    assert stat.S_ISFIFO(os.lstat(root / "real" / "pipe").st_mode)


def _direct_runner(module: str, *, timeout_s: int = 5) -> RegisteredRunnerV1:
    argv = ("python3", module)
    return RegisteredRunnerV1(
        runner_id="runner_direct_port_test",
        bad_predicate_id="pred_direct_port_test",
        oracle_id="oracle_direct_port_test",
        argv=argv,
        argv_sha256=argv_sha256(argv),
        timeout_s=timeout_s,
        witness_artifact_path=None,
    )


def _direct_request(
    module: str,
    source: bytes,
    *,
    timeout_s: int = 5,
) -> RunnerExecutionRequestV1:
    return build_runner_execution_request_v1(
        _direct_runner(module, timeout_s=timeout_s),
        {module: source},
    )


def _complete_runner_stream_hash(data: bytes) -> str:
    return ports_shell._canonical_runner_stream_hash_v1(
        data,
        Path("/workspace-prefix-absent-from-test-vector"),
    )


def test_runner_output_ceiling_accepts_exact_limit_and_rejects_one_atom_over(
    tmp_path: Path,
) -> None:
    # Arrange: output sizes are source constants, so the registered argv stays fixed.
    root = tmp_path / "repo"
    tools_dir = root / "tools"
    tools_dir.mkdir(parents=True)
    exact_module = tools_dir / "exact_output.py"
    exact_module.write_text(
        f"import os\nos.write(1, b'x' * {MAX_RUNNER_OUTPUT_BYTES_V1})\n", encoding="utf-8"
    )
    excess_module = tools_dir / "excess_output.py"
    excess_module.write_text(
        f"import os\nos.write(1, b'x' * {MAX_RUNNER_OUTPUT_BYTES_V1 + 1})\n", encoding="utf-8"
    )

    # Act
    exact = execute_registered_runner(
        _direct_request("tools/exact_output.py", exact_module.read_bytes())
    )
    one_over = execute_registered_runner(
        _direct_request("tools/excess_output.py", excess_module.read_bytes())
    )

    # Assert
    assert exact.returncode == 0 and exact.output_limit_exceeded is False
    assert exact.stdout_sha256 == _complete_runner_stream_hash(b"x" * MAX_RUNNER_OUTPUT_BYTES_V1)
    assert one_over.returncode is None and one_over.output_limit_exceeded is True
    assert one_over.timed_out is False


def test_runner_timeout_terminates_the_registered_process_group(tmp_path: Path) -> None:
    # Arrange: the child takes a lock, acknowledges it, ignores SIGTERM, and
    # inherits the registered runner's process group.
    root = tmp_path / "repo"
    tools_dir = root / "tools"
    tools_dir.mkdir(parents=True)
    module = tools_dir / "process_tree.py"
    module.write_text(
        "import fcntl, os, signal, subprocess, sys\n"
        "from pathlib import Path\n"
        "if '--child' in sys.argv:\n"
        "    descriptor = os.open('child.lock', os.O_CREAT | os.O_RDWR, 0o600)\n"
        "    fcntl.flock(descriptor, fcntl.LOCK_EX)\n"
        "    Path('child-ready').write_text('ready', encoding='utf-8')\n"
        "    os.write(int(sys.argv[-1]), b'1')\n"
        "    signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
        "    signal.pause()\n"
        "else:\n"
        "    read_fd, write_fd = os.pipe()\n"
        "    subprocess.Popen([sys.executable, __file__, '--child', str(write_fd)], pass_fds=(write_fd,))\n"
        "    os.close(write_fd)\n"
        "    os.read(read_fd, 1)\n"
        "    os.close(read_fd)\n"
        "    signal.pause()\n",
        encoding="utf-8",
    )

    # Act
    observation = ports_shell._run_bounded_process(
        [sys.executable, "-s", "-P", str(module)],
        cwd=root,
        env={"HOME": str(root), "LC_ALL": "C", "PATH": os.defpath},
        timeout_s=1,
        max_output_bytes=MAX_RUNNER_OUTPUT_BYTES_V1,
        retain_output=False,
    )
    lock_descriptor = os.open(root / "child.lock", os.O_RDWR)
    try:
        fcntl.flock(lock_descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
    finally:
        os.close(lock_descriptor)

    # Assert
    assert observation.returncode is None and observation.timed_out is True
    assert observation.output_limit_exceeded is False
    assert (root / "child-ready").read_text(encoding="utf-8") == "ready"


def test_selector_setup_failure_terminates_spawned_process_group(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    terminated_pids: list[int] = []
    original_terminate = ports_shell._terminate_process_group

    def tracked_terminate(process: Any) -> None:
        terminated_pids.append(process.pid)
        original_terminate(process)

    monkeypatch.setattr(ports_shell, "_terminate_process_group", tracked_terminate)
    monkeypatch.setattr(
        ports_shell.selectors,
        "DefaultSelector",
        lambda: (_ for _ in ()).throw(OSError("selector setup failed")),
    )

    # Act
    capture = ports_shell._run_bounded_process(
        [sys.executable, "-s", "-P", "-c", "import signal; signal.pause()"],
        cwd=tmp_path,
        env={"HOME": str(tmp_path), "LC_ALL": "C", "PATH": os.defpath},
        timeout_s=5,
        max_output_bytes=MAX_RUNNER_OUTPUT_BYTES_V1,
        retain_output=False,
    )

    # Assert
    assert capture.returncode is None
    assert capture.timed_out is False
    assert len(terminated_pids) == 1


def test_runner_uses_exact_interpreter_and_sanitized_environment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange
    root = tmp_path / "repo"
    tools_dir = root / "tools"
    hostile = tmp_path / "hostile"
    hostile_bin = hostile / "bin"
    tools_dir.mkdir(parents=True)
    hostile_bin.mkdir(parents=True)
    (hostile / "sitecustomize.py").write_text(
        "open('sitecustomize-ran', 'w').write('bad')\n", encoding="utf-8"
    )
    fake_python = hostile_bin / "python3"
    fake_python.write_text("#!/bin/sh\nprintf bad > fake-python-ran\n", encoding="utf-8")
    fake_python.chmod(0o755)
    module = tools_dir / "environment_probe.py"
    module.write_text(
        "import json, os, sys\n"
        "os.write(1, json.dumps({\n"
        "  'home_is_hostile': os.environ.get('HOME') == os.environ.get('HOSTILE_HOME'),\n"
        "  'path': os.environ.get('PATH'),\n"
        "  'pythonpath_is_private_source': os.environ.get('PYTHONPATH', '').endswith('/source'),\n"
        "  'pytest_addopts': os.environ.get('PYTEST_ADDOPTS'),\n"
        "  'pytest_plugins': os.environ.get('PYTEST_PLUGINS'), 'executable': sys.executable\n"
        "}, sort_keys=True).encode('utf-8'))\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("HOME", str(hostile))
    monkeypatch.setenv("PATH", f"{hostile_bin}:{os.defpath}")
    monkeypatch.setenv("PYTHONPATH", str(hostile))
    monkeypatch.setenv("PYTEST_ADDOPTS", "--capture=no")
    monkeypatch.setenv("PYTEST_PLUGINS", "sitecustomize")

    # Act
    observation = execute_registered_runner(
        _direct_request("tools/environment_probe.py", module.read_bytes())
    )
    expected = json.dumps(
        {
            "executable": sys.executable,
            "home_is_hostile": False,
            "path": os.defpath,
            "pytest_addopts": None,
            "pytest_plugins": None,
            "pythonpath_is_private_source": True,
        },
        sort_keys=True,
    ).encode("utf-8")

    # Assert
    assert observation.returncode == 0
    assert observation.stdout_sha256 == _complete_runner_stream_hash(expected)
    assert not (root / "fake-python-ran").exists() and not (root / "sitecustomize-ran").exists()


def test_sealed_source_tree_executes_the_captured_checker_import_graph() -> None:
    # Arrange
    module = "tools/runtime_disaster_discovery.py"
    sources = {path: _disk_bytes(path) for path in REQUIRED_SOURCE_PATHS_V1}
    sources[REGISTRY_PATH_V1] = _disk_bytes(REGISTRY_PATH_V1)
    request = build_runner_execution_request_v1(_direct_runner(module), sources)

    # Act
    observation = execute_registered_runner(request)

    # Assert
    assert observation.returncode == 0
    assert observation.timed_out is False
    assert observation.output_limit_exceeded is False
    assert observation.stdout_sha256 == _complete_runner_stream_hash(b"")
    assert observation.stderr_sha256 == _complete_runner_stream_hash(b"")


@pytest.mark.parametrize(
    "source",
    [
        b"print(__file__)\n",
        b"raise RuntimeError(__file__)\n",
    ],
    ids=("file-output", "exception-traceback"),
)
def test_runner_observation_excludes_ephemeral_workspace_path(source: bytes) -> None:
    # Arrange
    request = _direct_request("tools/path_probe.py", source)

    # Act
    first = execute_registered_runner(request)
    second = execute_registered_runner(request)

    # Assert
    assert first == second


def test_runner_stream_framing_distinguishes_literal_token_from_workspace_path() -> None:
    # Arrange
    literal = _direct_request(
        "tools/literal_path.py",
        b"print('<wedc1-runner-workspace>')\n",
    )
    actual = _direct_request(
        "tools/actual_path.py",
        b"from pathlib import Path\nprint(Path(__file__).parents[2])\n",
    )

    # Act
    literal_observation = execute_registered_runner(literal)
    actual_observation = execute_registered_runner(actual)

    # Assert
    assert literal_observation.returncode == actual_observation.returncode == 0
    assert literal_observation.stdout_sha256 != actual_observation.stdout_sha256


def test_incomplete_dual_stream_capture_has_stable_domain_separated_hashes() -> None:
    # Arrange
    source = (
        b"import os, threading\n"
        b"def emit(descriptor, value):\n"
        b"    for _ in range(32):\n"
        b"        os.write(descriptor, value * 65536)\n"
        b"threads = [threading.Thread(target=emit, args=(1, b'a')), "
        b"threading.Thread(target=emit, args=(2, b'b'))]\n"
        b"[thread.start() for thread in threads]\n"
        b"[thread.join() for thread in threads]\n"
    )
    request = _direct_request("tools/dual_stream_excess.py", source)

    # Act
    first = execute_registered_runner(request)
    second = execute_registered_runner(request)

    # Assert
    assert first == second
    assert first.returncode is None and first.output_limit_exceeded is True
    assert first.stdout_sha256 != first.stderr_sha256


def test_read_receipt_bounded_rejects_symlink_fifo_and_oversize(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange
    receipt = tmp_path / "packet.json"
    receipt.write_bytes(b"{}")
    link = tmp_path / "link.json"
    os.symlink(receipt, link)
    pipe = tmp_path / "pipe"
    os.mkfifo(pipe)
    big = tmp_path / "big.json"
    big.write_bytes(b"{" + b" " * 40 + b"}")
    monkeypatch.setattr(verifier_shell, "MAX_PACKET_BYTES_V1", 16)

    # Act / Assert
    assert read_receipt_bounded(receipt) == b"{}"
    assert _reject_of(lambda: read_receipt_bounded(link)).code is RejectCodeV1.PATH_SYMLINK
    assert _reject_of(lambda: read_receipt_bounded(pipe)).code is RejectCodeV1.PATH_NOT_REGULAR_FILE
    assert _reject_of(lambda: read_receipt_bounded(big)).code is RejectCodeV1.JSON_TOO_LARGE
    assert (
        _reject_of(lambda: read_receipt_bounded(tmp_path / "missing.json")).code
        is RejectCodeV1.SOURCE_UNREADABLE
    )


# --------------------------------------------------------------------------
# Shell CLIs: rejects write nothing and execute nothing
# --------------------------------------------------------------------------


def _tree_snapshot() -> dict[str, str]:
    return {
        path: sha256_hex(_disk_bytes(path))
        for path in (*REQUIRED_SOURCE_PATHS_V1, REGISTRY_PATH_V1)
    }


def test_runner_cli_reject_writes_nothing_and_executes_nothing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    # Arrange
    before = _tree_snapshot()
    repo = _exit_repo(0, b"ok")
    repo.head_states = [None]
    monkeypatch.setattr(runner_shell, "default_ports", lambda _root=None: repo.ports())
    out = tmp_path / "packet.json"

    # Act
    code = runner_shell.main(["--out", str(out)])
    printed = json.loads(capsys.readouterr().out)

    # Assert
    assert code == 1
    assert printed == {"ok": False, "reject_code": "GIT_PROBE_UNAVAILABLE", "detail": "HEAD"}
    assert not out.exists()
    assert repo.executed == []
    assert _tree_snapshot() == before


def test_verifier_cli_rejects_legacy_receipt_and_accepts_fresh_packet(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    # Arrange
    before = _tree_snapshot()
    legacy = tmp_path / "legacy.json"
    legacy.write_bytes(
        _encode(
            {
                "schema": "zenodex/stateful-disaster-proof-obligation-closure-receipt/v1",
                "status": "passed",
            }
        )
    )
    fresh = tmp_path / "fresh.json"
    fresh.write_bytes(_packet_bytes(_run(_repo())))
    monkeypatch.setattr(verifier_shell, "default_ports", lambda _root=None: _repo().ports())

    # Act
    legacy_code = verifier_shell.main(["--receipt", str(legacy)])
    legacy_report = json.loads(capsys.readouterr().out)
    fresh_code = verifier_shell.main(["--receipt", str(fresh)])
    fresh_report = json.loads(capsys.readouterr().out)

    # Assert
    assert legacy_code == 1 and legacy_report["reject_code"] == "LEGACY_BRIDGE_RECEIPT_REJECTED"
    assert fresh_code == 0 and fresh_report["ok"] is True and fresh_report["findings"] == []
    assert (
        fresh_report["denominator_state"] == "DENOMINATOR_INCOMPLETE"
        and fresh_report["coverage_ratio"] == "WITHHELD"
    )
    assert fresh_report["flags"]["whole_economy_claim_allowed"] is False
    assert _tree_snapshot() == before


def test_packet_schema_constant_is_not_a_legacy_schema() -> None:
    assert PACKET_SCHEMA_V1 not in LEGACY_BRIDGE_SCHEMAS_V1
    assert all(status.value != "CLOSED_EXACT" for status in EvidenceStatusV1)
    assert ApplicabilityV1.APPLICABILITY_UNKNOWN.value == "APPLICABILITY_UNKNOWN"


# --------------------------------------------------------------------------
# Source pin set, every race boundary, exact no-effect and status recomputation
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("mutate", "code"),
    [
        (lambda pins: pins.pop(0), RejectCodeV1.SOURCE_PIN_MISSING),
        (
            lambda pins: pins.append({**pins[0], "path": "docs/extra_pin.json"}),
            RejectCodeV1.SOURCE_PIN_UNEXPECTED,
        ),
        (lambda pins: pins.reverse(), RejectCodeV1.RESULT_ORDER_INVALID),
        (lambda pins: pins.append(dict(pins[0])), RejectCodeV1.PATH_DUPLICATE),
        (lambda pins: pins[0].update(role="SEMANTIC_SOURCE"), RejectCodeV1.SOURCE_PIN_MISSING),
    ],
)
def test_missing_extra_reordered_duplicate_or_misrole_source_pins_reject(
    mutate: Callable[[list[dict[str, Any]]], None], code: RejectCodeV1
) -> None:
    # Arrange
    registry = _registry_obj()
    mutate(registry["source_pins"])
    repo = _repo(registry)

    # Act
    reject = _reject_of(lambda: _run(repo))

    # Assert
    assert reject.code is code
    assert repo.executed == []


def test_head_moving_at_the_render_boundary_rejects() -> None:
    # Arrange
    repo = _repo()
    repo.head_states = [
        GitHeadStateV1(BASE_COMMIT, BASE_TREE, True),
        GitHeadStateV1(OTHER_COMMIT, OTHER_TREE, True),
    ]

    # Act
    reject = _reject_of(lambda: render_source_pins(repo.ports()))

    # Assert
    assert reject.code is RejectCodeV1.HEAD_MOVED and reject.detail == "after_render"


def test_head_moving_before_capture_probes_the_captured_tree_and_rechecks_after_read() -> None:
    # Arrange: HEAD moves at the boundary before capture; capture must take the moved head,
    # every tree probe must use that captured tree, and the after-read recheck must notice the next move
    repo = _repo()
    repo.head_states = [GitHeadStateV1(BASE_COMMIT, BASE_TREE, True)]
    repo.boundaries["before_capture"] = lambda: repo.head_states.insert(
        0, GitHeadStateV1(OTHER_COMMIT, OTHER_TREE, True)
    )

    # Act
    reject = _reject_of(lambda: _run(repo))

    # Assert
    assert repo.probed_trees == {OTHER_TREE}
    assert reject.code is RejectCodeV1.HEAD_MOVED and reject.detail == "after_read"
    assert repo.executed == []


def test_every_probe_uses_the_captured_tree_object() -> None:
    # Arrange
    repo = _repo()

    # Act
    _run(repo)

    # Assert
    assert repo.probed_trees == {BASE_TREE}


def _derived(repo: FakeRepo) -> tuple[Any, Any, Any, Any]:
    from tools.runtime_disaster_discovery import parse_registry as _parse

    registry = _parse(repo.files[REGISTRY_PATH_V1])
    owned = {path: _owned(repo, path) for path in REQUIRED_SOURCE_PATHS_V1}
    bound = {source.pin.path: source for source in bind_sources(registry.source_pins, owned)}
    inventory = derive_inventory(
        registry, bound, subject_commit=BASE_COMMIT, subject_tree=BASE_TREE, artifacts={}
    )
    subject = compute_subject(
        commit=BASE_COMMIT,
        tree=BASE_TREE,
        registry=registry,
        bound=bound,
        m6_manifest_root=inventory.manifest.manifest_root,
    )
    return registry, bound, inventory, subject


def test_exact_no_effect_observations_and_status_recomputation() -> None:
    # Arrange
    from dataclasses import replace as dc_replace

    repo = _exit_repo(0, b"passed", witness=False)
    packet = _run(repo)
    registry, _bound, inventory, subject = _derived(_exit_repo(0, b"passed", witness=False))
    (result,) = packet.core.results
    row = inventory.row(result.obligation_id)
    assert row is not None
    unchanged = tuple(
        NoEffectObservationV1(surface, NoEffectOutcomeV1.UNCHANGED) for surface in NoEffectSurfaceV1
    )
    changed = (
        NoEffectObservationV1(NoEffectSurfaceV1.STATE, NoEffectOutcomeV1.CHANGED),
        *unchanged[1:],
    )
    witness = WitnessV1(
        WitnessKindV1.BAD_TRACE_WITNESS,
        ArtifactRefV1(WITNESS_PATH, sha256_hex(_disk_bytes(WITNESS_PATH))),
        None,
    )

    # Act
    status_unchanged = compute_result_status(
        row, dc_replace(result, no_effect_observations=unchanged), registry, subject
    )
    status_changed = compute_result_status(
        row, dc_replace(result, no_effect_observations=changed), registry, subject
    )
    status_external = compute_result_status(
        row,
        dc_replace(result, execution_premise=ExecutionPremiseV1.EXTERNAL_PREMISE_MUTABLE_WORKTREE),
        registry,
        subject,
    )
    status_stale = compute_result_status(
        row, dc_replace(result, source_pins_root="0x" + "ab" * 32), registry, subject
    )
    status_fail_no_witness = compute_result_status(
        row, dc_replace(result, oracle_verdict=OracleVerdictV1.FAIL), registry, subject
    )
    status_fail_witness = compute_result_status(
        row,
        dc_replace(result, oracle_verdict=OracleVerdictV1.FAIL, witness=witness),
        registry,
        subject,
    )
    status_inconclusive = compute_result_status(
        row, dc_replace(result, oracle_verdict=OracleVerdictV1.INCONCLUSIVE), registry, subject
    )

    # Assert
    assert result.computed_status is EvidenceStatusV1.NOT_WITNESSED_IN_TESTS
    assert status_unchanged is EvidenceStatusV1.NOT_WITNESSED_IN_TESTS
    assert status_changed is EvidenceStatusV1.INCONCLUSIVE
    assert status_external is EvidenceStatusV1.EXTERNAL_PREMISE
    assert status_stale is EvidenceStatusV1.STALE_EVIDENCE
    assert status_fail_no_witness is EvidenceStatusV1.INCONCLUSIVE
    assert status_fail_witness is EvidenceStatusV1.WITNESSED_REACHABLE
    assert status_inconclusive is EvidenceStatusV1.INCONCLUSIVE
    assert [item.surface.value for item in result.no_effect_observations] == [
        "STATE",
        "HISTORY",
        "RECEIPT",
        "OUTBOX",
    ]


def test_runner_cli_to_checker_cli_replay(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    # Arrange
    monkeypatch.setattr(runner_shell, "default_ports", lambda _root=None: _repo().ports())
    monkeypatch.setattr(verifier_shell, "default_ports", lambda _root=None: _repo().ports())
    out = tmp_path / "replay.json"

    # Act
    run_code = runner_shell.main(["--out", str(out)])
    summary = json.loads(capsys.readouterr().out)
    check_code = verifier_shell.main(["--receipt", str(out)])
    report = json.loads(capsys.readouterr().out)

    # Assert
    assert run_code == 0 and check_code == 0
    assert summary["applicability_cells"] == 11988 and summary["coverage_ratio"] == "WITHHELD"
    assert report["ok"] is True and report["receipt_root"] == summary["receipt_root"]
    assert report["classification_counts"]["APPLICABILITY_UNKNOWN"] == 11988
    assert report["flags"]["whole_economy_claim_allowed"] is False
    assert "%" not in out.read_text(encoding="utf-8")
