from __future__ import annotations

import ast
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PRODUCTION_ROOTS = tuple(ROOT / name for name in ("src", "tools", "bin", "scripts"))
PRODUCTION_FILES = (ROOT / "sitecustomize.py",)
CORE = ROOT / "src/core/recursive_stark_admission.py"
PINNED_ADAPTER = ROOT / "src/integration/recursive_stark_verifier_adapter.py"
DURABLE_STORE = ROOT / "src/integration/recursive_stark_admission_store.py"
DURABLE_ENGINE = ROOT / "src/integration/_recursive_stark_admission_store_engine.py"
DURABLE_HASHES = ROOT / "src/integration/_recursive_stark_admission_store_hashes.py"
SETTLEMENT_AUTHORITY = ROOT / "src/core/_zrpf_settlement_commit_authority.py"
SETTLEMENT_CERTIFICATE_AUTHORITY = (
    ROOT / "src/core/_zrpf_settlement_certificate_authority.py"
)
SETTLEMENT_VERIFIER_ADAPTER = (
    ROOT / "src/integration/zrpf_settlement_verifier_adapter.py"
)
SOURCE_OPENED_V6_VERIFIER_ADAPTER = (
    ROOT / "src/integration/zrpf_source_opened_spot_v6_verifier_adapter.py"
)
SPOT_V7_FIRECRACKER_AUTHORITY = (
    ROOT / "src/integration/_zrpf_spot_v7_firecracker_authority.py"
)
SPOT_V7_FIRECRACKER_OUTPUT = (
    ROOT / "src/integration/_zrpf_spot_v7_firecracker_output.py"
)
SPOT_V7_FIRECRACKER_EXECUTION_BINDING = (
    ROOT / "src/integration/_zrpf_spot_v7_firecracker_execution_binding.py"
)
SPOT_V7_SETTLEMENT_ENVELOPE_CODEC = (
    ROOT / "src/integration/_zrpf_spot_v7_settlement_envelope_codec.py"
)
SPOT_V7_SETTLEMENT_ENVELOPE_REPLAY = (
    ROOT / "src/integration/_zrpf_spot_v7_settlement_envelope_replay.py"
)
SPOT_V7_OPERATIONAL_GATE = ROOT / "src/integration/_zrpf_spot_v7_operational_gate.py"
SPOT_V7_OPERATIONAL_CAPABILITY_V2 = (
    ROOT / "src/integration/_zrpf_spot_v7_operational_capability_v2.py"
)
SPOT_V7_OPERATIONAL_POLICY_PROVENANCE = (
    ROOT / "src/integration/zrpf_spot_v7_operational_policy_provenance.py"
)
SPOT_V7_OPERATIONAL_POLICY_V3 = (
    ROOT / "src/integration/_zrpf_spot_v7_operational_policy_v3.py"
)
SPOT_V7_OPERATIONAL_POLICY_PROVENANCE_V2 = (
    ROOT / "src/integration/zrpf_spot_v7_operational_policy_provenance_v2.py"
)
SPOT_V7_LAGGED_CHECKPOINT_BEACON = (
    ROOT / "src/integration/zrpf_spot_v7_lagged_checkpoint_beacon.py"
)
SPOT_V7_OPERATIONAL_POLICY_STORE = (
    ROOT / "src/integration/_zrpf_spot_v7_operational_policy_store.py"
)
SPOT_V7_OPERATIONAL_STORE = ROOT / "src/integration/_zrpf_spot_v7_operational_store.py"
SPOT_V7_ZENO_LEDGER_FINALITY_ADAPTER = (
    ROOT / "src/integration/zrpf_spot_v7_zeno_ledger_finality_adapter.py"
)
SAMPLED_RETRIEVABILITY_VERIFIER = (
    ROOT / "src/integration/zrpf_sampled_retrievability_v1/verifier.py"
)
SPOT_V7_GOVERNED_DA_PREREQUISITE = (
    ROOT / "src/integration/zrpf_spot_v7_governed_da_prerequisite.py"
)
SPOT_V7_GOVERNED_DA_PREREQUISITE_V2 = (
    ROOT / "src/integration/zrpf_spot_v7_governed_da_prerequisite_v2.py"
)
SPOT_V7_ATOMIC_STORE = (
    ROOT / "src/integration/zrpf_spot_v7_atomic_settlement_store.py"
)
PRIVATE_CAPABILITY_TYPE = "_AuthenticatedRecursiveStarkRootFacts"
PRIVATE_SEAL = "_AUTHENTICATED_FACTS_SEAL"
PRIVATE_MINT = "_mint_recursive_stark_root_facts_after_verification"
PRIVATE_ADMISSION = "_admit_authenticated_recursive_stark_root"
PRIVATE_PROVENANCE = "_RecursiveStarkVerificationProvenance"
PRIVATE_SNAPSHOT = "_RecursiveStarkAdmissionIndexSnapshot"
PRIVATE_PLANNER = "_plan_authenticated_recursive_stark_root"
PRIVATE_DURABLE_COMMIT = "_commit_authenticated_recursive_stark_root"
PRIVATE_SOURCE_OPENED_V6_SEAL = "_seal_verified_result"
PRIVATE_FIRECRACKER_AUTHORITY_NAMES = frozenset(
    {
        "_GovernedRuntimeSealV1",
        "_GovernedBinderSealV1",
        "_GOVERNED_RUNTIME_SEAL_V1",
        "_GOVERNED_BINDER_SEAL_V1",
        "_GovernedJailedFirecrackerExecutionV1",
        "_GovernedFirecrackerSpotV7SettlementV1",
        "_bind_governed_firecracker_spot_v7_settlement_v1",
        "_require_governed_firecracker_spot_v7_authority_available_v1",
        "_commit_governed_firecracker_capability",
        "_candidate_for_binder",
        "_candidate_for_atomic_store",
        "_DecodedCommittedSpotV7OutputV1",
        "_BoundCommittedSpotV7CandidateV1",
        "_decode_exact_committed_spot_v7_output_v1",
        "_bind_decoded_spot_v7_output_to_candidate_v1",
        "_revalidate_bound_spot_v7_candidate_v1",
    }
)
PRIVATE_OPERATIONAL_POLICY_MINT_NAMES = frozenset(
    {
        "_GovernedOperationalPolicyMaterialV2",
        "_GOVERNED_OPERATIONAL_POLICY_SEAL_V2",
    }
)
PRIVATE_OPERATIONAL_POLICY_RELEASE_HANDOFF_NAMES = frozenset(
    {
        "_AuthenticatedSpotV7OperationalPolicyReleasePinsV1",
        "_AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V1",
        "load_governed_spot_v7_operational_policy_v2",
    }
)
PRIVATE_OPERATIONAL_POLICY_PROVENANCE_NAMES = frozenset(
    {"_GovernedOperationalPolicyProvenanceV1"}
)
PRIVATE_OPERATIONAL_POLICY_V3_NAMES = frozenset(
    {
        "_GovernedOperationalPolicyMaterialV3",
        "_GovernedOperationalPolicyProvenanceV2",
        "_GovernedOperationalPolicySealV3",
        "_GOVERNED_OPERATIONAL_POLICY_SEAL_V3",
        "_GovernedSpotV7OperationalPolicyV3",
        "_mint_governed_spot_v7_operational_policy_v3",
        "_require_governed_operational_policy_v3",
    }
)
PRIVATE_OPERATIONAL_POLICY_V3_RELEASE_HANDOFF_NAMES = frozenset(
    {
        "_AuthenticatedOperationalPolicyReleasePinsSealV2",
        "_AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V2",
        "_AuthenticatedSpotV7OperationalPolicyReleasePinsV2",
        "load_governed_spot_v7_operational_policy_v3",
    }
)
PRIVATE_LAGGED_CHECKPOINT_BEACON_NAMES = frozenset(
    {
        "_GovernedLaggedCheckpointBeaconSealV1",
        "_GOVERNED_LAGGED_CHECKPOINT_BEACON_SEAL_V1",
        "_GovernedSpotV7LaggedCheckpointBeaconV1",
        "_require_governed_lagged_checkpoint_beacon_v1",
    }
)
PRIVATE_SAMPLED_RETRIEVABILITY_AUTHORITY_NAMES = frozenset(
    {
        "_AuthenticatedEvidenceSealV1",
        "_AUTHENTICATED_EVIDENCE_SEAL_V1",
        "_AuthenticatedSampledRetrievabilityEvidenceV1",
        "_projection_for_spot_v7_da_prerequisite_v1",
    }
)
PRIVATE_SPOT_V7_GOVERNED_DA_AUTHORITY_NAMES = frozenset(
    {
        "_GovernedSpotV7DataAvailabilityPrerequisiteSealV1",
        "_GOVERNED_SPOT_V7_DA_PREREQUISITE_SEAL_V1",
        "_GovernedSpotV7DataAvailabilityPrerequisiteV1",
        "_bind_governed_spot_v7_da_prerequisite_v1",
        "_require_authenticated_sampled_response_v1",
        "_projection_for_downstream_binding_v1",
    }
)
PRIVATE_SPOT_V7_GOVERNED_DA_V2_AUTHORITY_NAMES = frozenset(
    {
        "_GovernedSampledResponseSealV1",
        "_GOVERNED_SAMPLED_RESPONSE_SEAL_V1",
        "_GovernedSpotV7SampledResponseV1",
        "_bind_governed_spot_v7_sampled_response_v1",
        "_require_governed_sampled_response",
        "_GovernedDaPrerequisiteSealV2",
        "_GOVERNED_DA_PREREQUISITE_SEAL_V2",
        "_GovernedSpotV7DataAvailabilityPrerequisiteV2",
        "_bind_governed_spot_v7_da_prerequisite_v2",
    }
)
PRIVATE_AUTHORITY_NAMES = frozenset(
    {
        PRIVATE_CAPABILITY_TYPE,
        PRIVATE_SEAL,
        PRIVATE_MINT,
        PRIVATE_ADMISSION,
        PRIVATE_PROVENANCE,
        PRIVATE_SNAPSHOT,
        PRIVATE_PLANNER,
    }
)
PROTECTED_AUTHORITY_NAMES = (
    PRIVATE_AUTHORITY_NAMES
    | frozenset({PRIVATE_SOURCE_OPENED_V6_SEAL})
    | PRIVATE_FIRECRACKER_AUTHORITY_NAMES
    | PRIVATE_OPERATIONAL_POLICY_MINT_NAMES
    | PRIVATE_OPERATIONAL_POLICY_PROVENANCE_NAMES
    | PRIVATE_OPERATIONAL_POLICY_RELEASE_HANDOFF_NAMES
    | PRIVATE_OPERATIONAL_POLICY_V3_NAMES
    | PRIVATE_OPERATIONAL_POLICY_V3_RELEASE_HANDOFF_NAMES
    | PRIVATE_LAGGED_CHECKPOINT_BEACON_NAMES
    | PRIVATE_SAMPLED_RETRIEVABILITY_AUTHORITY_NAMES
    | PRIVATE_SPOT_V7_GOVERNED_DA_AUTHORITY_NAMES
    | PRIVATE_SPOT_V7_GOVERNED_DA_V2_AUTHORITY_NAMES
)
PRIVATE_ADAPTER_IMPORTS = frozenset(
    {
        PRIVATE_CAPABILITY_TYPE,
        PRIVATE_MINT,
        PRIVATE_ADMISSION,
        PRIVATE_PROVENANCE,
    }
)
PRIVATE_STORE_IMPORTS = frozenset({PRIVATE_CAPABILITY_TYPE, PRIVATE_PLANNER})
PRIVATE_ENGINE_IMPORTS = frozenset({PRIVATE_CAPABILITY_TYPE, PRIVATE_SNAPSHOT})
PRIVATE_HASH_IMPORTS = frozenset({PRIVATE_CAPABILITY_TYPE})
PRIVATE_SETTLEMENT_AUTHORITY_IMPORTS = frozenset({PRIVATE_CAPABILITY_TYPE})
PRIVATE_SETTLEMENT_CERTIFICATE_IMPORTS = frozenset({PRIVATE_CAPABILITY_TYPE})
PRIVATE_SETTLEMENT_VERIFIER_IMPORTS = frozenset({PRIVATE_MINT, PRIVATE_PROVENANCE})
PRIVATE_SOURCE_OPENED_V6_REFERENCES = PRIVATE_SETTLEMENT_VERIFIER_IMPORTS | frozenset(
    {PRIVATE_SOURCE_OPENED_V6_SEAL}
)
PRIVATE_FIRECRACKER_STORE_REFERENCES = frozenset(
    {
        "_GovernedFirecrackerSpotV7SettlementV1",
        "_require_governed_firecracker_spot_v7_authority_available_v1",
    }
)
PRIVATE_FIRECRACKER_EXECUTION_BINDING_REFERENCES = frozenset(
    {
        "_BoundCommittedSpotV7CandidateV1",
        "_bind_decoded_spot_v7_output_to_candidate_v1",
        "_decode_exact_committed_spot_v7_output_v1",
    }
)
PRIVATE_FIRECRACKER_OPERATIONAL_REFERENCES = frozenset(
    {
        "_GovernedFirecrackerSpotV7SettlementV1",
        "_candidate_for_atomic_store",
    }
)
RETIRED_PUBLIC_AUTHORITY_NAMES = frozenset(
    {
        "VerifiedRecursiveStarkRootFacts",
        "admit_verified_recursive_stark_root",
        "parse_authenticated_recursive_facts",
    }
)
DATA_ONLY_ADMISSION_RESULT = "RecursiveStarkAdmissionResult"


def test_private_admission_symbols_are_absent_from_other_production_modules() -> None:
    violations: list[str] = []
    for path in _production_python_paths():
        if path in {CORE, SPOT_V7_FIRECRACKER_AUTHORITY, SPOT_V7_FIRECRACKER_OUTPUT}:
            continue
        allowed = {
            PINNED_ADAPTER: PRIVATE_ADAPTER_IMPORTS,
            DURABLE_STORE: PRIVATE_STORE_IMPORTS,
            DURABLE_ENGINE: PRIVATE_ENGINE_IMPORTS,
            DURABLE_HASHES: PRIVATE_HASH_IMPORTS,
            SETTLEMENT_AUTHORITY: PRIVATE_SETTLEMENT_AUTHORITY_IMPORTS,
            SETTLEMENT_CERTIFICATE_AUTHORITY: PRIVATE_SETTLEMENT_CERTIFICATE_IMPORTS,
            SETTLEMENT_VERIFIER_ADAPTER: PRIVATE_SETTLEMENT_VERIFIER_IMPORTS,
            SOURCE_OPENED_V6_VERIFIER_ADAPTER: PRIVATE_SOURCE_OPENED_V6_REFERENCES,
            SPOT_V7_ATOMIC_STORE: PRIVATE_FIRECRACKER_STORE_REFERENCES,
            SPOT_V7_FIRECRACKER_EXECUTION_BINDING: (
                PRIVATE_FIRECRACKER_EXECUTION_BINDING_REFERENCES
            ),
            SPOT_V7_SETTLEMENT_ENVELOPE_CODEC: (
                PRIVATE_FIRECRACKER_OPERATIONAL_REFERENCES
            ),
            SPOT_V7_SETTLEMENT_ENVELOPE_REPLAY: (
                PRIVATE_FIRECRACKER_OPERATIONAL_REFERENCES
            ),
            SPOT_V7_OPERATIONAL_GATE: PRIVATE_FIRECRACKER_OPERATIONAL_REFERENCES,
            SPOT_V7_OPERATIONAL_CAPABILITY_V2: (
                PRIVATE_FIRECRACKER_OPERATIONAL_REFERENCES
                | PRIVATE_OPERATIONAL_POLICY_MINT_NAMES
                | PRIVATE_OPERATIONAL_POLICY_PROVENANCE_NAMES
            ),
            SPOT_V7_OPERATIONAL_POLICY_PROVENANCE: (
                PRIVATE_OPERATIONAL_POLICY_MINT_NAMES
                | PRIVATE_OPERATIONAL_POLICY_PROVENANCE_NAMES
                | PRIVATE_OPERATIONAL_POLICY_RELEASE_HANDOFF_NAMES
            ),
            SPOT_V7_OPERATIONAL_POLICY_V3: (
                PRIVATE_OPERATIONAL_POLICY_MINT_NAMES
                | PRIVATE_OPERATIONAL_POLICY_V3_NAMES
            ),
            SPOT_V7_OPERATIONAL_POLICY_PROVENANCE_V2: (
                PRIVATE_OPERATIONAL_POLICY_V3_NAMES
                | PRIVATE_OPERATIONAL_POLICY_V3_RELEASE_HANDOFF_NAMES
            ),
            SPOT_V7_LAGGED_CHECKPOINT_BEACON: (
                PRIVATE_OPERATIONAL_POLICY_V3_NAMES
                | PRIVATE_LAGGED_CHECKPOINT_BEACON_NAMES
            ),
            SPOT_V7_OPERATIONAL_POLICY_STORE: (
                PRIVATE_OPERATIONAL_POLICY_PROVENANCE_NAMES
            ),
            SPOT_V7_OPERATIONAL_STORE: PRIVATE_OPERATIONAL_POLICY_PROVENANCE_NAMES,
            SPOT_V7_ZENO_LEDGER_FINALITY_ADAPTER: (
                PRIVATE_FIRECRACKER_OPERATIONAL_REFERENCES
            ),
            SAMPLED_RETRIEVABILITY_VERIFIER: (
                PRIVATE_SAMPLED_RETRIEVABILITY_AUTHORITY_NAMES
            ),
            SPOT_V7_GOVERNED_DA_PREREQUISITE: (
                PRIVATE_OPERATIONAL_POLICY_PROVENANCE_NAMES
                | PRIVATE_SAMPLED_RETRIEVABILITY_AUTHORITY_NAMES
                | PRIVATE_SPOT_V7_GOVERNED_DA_AUTHORITY_NAMES
            ),
            SPOT_V7_GOVERNED_DA_PREREQUISITE_V2: (
                PRIVATE_OPERATIONAL_POLICY_V3_NAMES
                | PRIVATE_LAGGED_CHECKPOINT_BEACON_NAMES
                | PRIVATE_SAMPLED_RETRIEVABILITY_AUTHORITY_NAMES
                | PRIVATE_SPOT_V7_GOVERNED_DA_V2_AUTHORITY_NAMES
            ),
        }.get(path, frozenset())
        tree = _parse(path)
        for node in ast.walk(tree):
            name = _private_authority_reference(node)
            if name is not None and name not in allowed:
                violations.append(f"{path.relative_to(ROOT)}:{_line(node)}:{name}")

    assert violations == []


def test_operational_policy_provenance_is_the_only_production_policy_mint() -> None:
    callers: list[str] = []
    for path in _production_python_paths():
        tree = _parse(path)
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Call)
                and _call_name(node) == "_GovernedSpotV7OperationalPolicyV2"
            ):
                callers.append(f"{path.relative_to(ROOT)}:{_line(node)}")

    assert len(callers) == 1
    assert callers[0].split(":", maxsplit=1)[0] == (
        "src/integration/zrpf_spot_v7_operational_policy_provenance.py"
    )

    tree = _parse(SPOT_V7_OPERATIONAL_POLICY_PROVENANCE)
    loader = _function(tree, "load_governed_spot_v7_operational_policy_v2")
    ordered_calls = (
        "_open_authenticated_release_context",
        "_parse_manifest_v1",
        "_require_manifest_binding",
        "_require_active_release_context",
        "_verify_release_quorum",
        "_GovernedSpotV7OperationalPolicyV2",
    )
    call_lines = {
        name: [
            _line(node)
            for node in ast.walk(loader)
            if isinstance(node, ast.Call) and _call_name(node) == name
        ]
        for name in ordered_calls
    }
    assert {name: len(lines) for name, lines in call_lines.items()} == {
        name: 1 for name in ordered_calls
    }
    assert tuple(call_lines[name][0] for name in ordered_calls) == tuple(
        sorted(call_lines[name][0] for name in ordered_calls)
    )


def test_operational_policy_release_handoff_has_no_production_mint_or_consumer() -> None:
    forbidden_calls: dict[str, list[str]] = {
        "_AuthenticatedSpotV7OperationalPolicyReleasePinsV1": [],
        "load_governed_spot_v7_operational_policy_v2": [],
    }
    for path in _production_python_paths():
        tree = _parse(path)
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            name = _call_name(node)
            if name in forbidden_calls:
                forbidden_calls[name].append(f"{path.relative_to(ROOT)}:{_line(node)}")

    assert forbidden_calls == {
        "_AuthenticatedSpotV7OperationalPolicyReleasePinsV1": [],
        "load_governed_spot_v7_operational_policy_v2": [],
    }


def test_operational_policy_v3_has_one_mint_and_no_production_loader_consumer() -> None:
    constructor_calls: list[str] = []
    mint_calls: list[str] = []
    loader_calls: list[str] = []
    for path in _production_python_paths():
        tree = _parse(path)
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            name = _call_name(node)
            location = f"{path.relative_to(ROOT)}:{_line(node)}"
            if name == "_GovernedSpotV7OperationalPolicyV3":
                constructor_calls.append(location)
            elif name == "_mint_governed_spot_v7_operational_policy_v3":
                mint_calls.append(location)
            elif name == "load_governed_spot_v7_operational_policy_v3":
                loader_calls.append(location)

    assert len(constructor_calls) == 1
    assert constructor_calls[0].split(":", maxsplit=1)[0] == (
        "src/integration/_zrpf_spot_v7_operational_policy_v3.py"
    )
    assert len(mint_calls) == 1
    assert mint_calls[0].split(":", maxsplit=1)[0] == (
        "src/integration/zrpf_spot_v7_operational_policy_provenance_v2.py"
    )
    assert loader_calls == []


@pytest.mark.parametrize(
    "path",
    (
        SPOT_V7_FIRECRACKER_AUTHORITY,
        SPOT_V7_FIRECRACKER_OUTPUT,
        SPOT_V7_FIRECRACKER_EXECUTION_BINDING,
        SPOT_V7_OPERATIONAL_GATE,
        SPOT_V7_OPERATIONAL_CAPABILITY_V2,
    ),
)
def test_firecracker_authority_symbols_have_no_public_alias_or_export(path: Path) -> None:
    tree = _parse(path)

    assert _public_authority_alias_violations(tree) == []
    assert _private_authority_all_exports(tree) == []
    assert _public_top_level_authority_reachability(tree) == []


def test_combined_da_authority_symbols_have_no_public_alias_or_export() -> None:
    tree = _parse(SPOT_V7_GOVERNED_DA_PREREQUISITE)

    assert _public_authority_alias_violations(tree) == []
    assert _private_authority_all_exports(tree) == []
    assert _public_top_level_authority_reachability(tree) == []


@pytest.mark.parametrize(
    ("path", "expected_public_reachability"),
    (
        (SPOT_V7_OPERATIONAL_POLICY_V3, []),
        (
            SPOT_V7_OPERATIONAL_POLICY_PROVENANCE_V2,
            [
                "load_governed_spot_v7_operational_policy_v3",
                "spot_v7_operational_policy_manifest_bytes_v2",
                "spot_v7_operational_policy_manifest_payload_hash_v2",
            ],
        ),
        (
            SPOT_V7_LAGGED_CHECKPOINT_BEACON,
            ["bind_governed_spot_v7_lagged_checkpoint_beacon_v1"],
        ),
        (SPOT_V7_GOVERNED_DA_PREREQUISITE_V2, []),
    ),
)
def test_v3_governed_da_authority_has_exact_public_reachability(
    path: Path,
    expected_public_reachability: list[str],
) -> None:
    tree = _parse(path)

    assert _public_authority_alias_violations(tree) == []
    assert _private_authority_all_exports(tree) == []
    assert _public_top_level_authority_reachability(tree) == (
        expected_public_reachability
    )


def test_sampled_retrievability_exposes_only_the_exact_verifier_mint() -> None:
    tree = _parse(SAMPLED_RETRIEVABILITY_VERIFIER)

    assert _public_authority_alias_violations(tree) == []
    assert _private_authority_all_exports(tree) == []
    assert _public_top_level_authority_reachability(tree) == [
        "verify_exact_evidence_v1"
    ]


def test_firecracker_static_binding_factory_and_expected_document_ratchets() -> None:
    tree = _parse(SPOT_V7_FIRECRACKER_EXECUTION_BINDING)
    classes = {
        node.name: node for node in tree.body if isinstance(node, ast.ClassDef)
    }
    result_class = classes["_AuthorityFalseSpotV7FirecrackerExecutionBindingV1"]
    assert not any(
        isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == "_from_verified"
        for node in result_class.body
    )

    immutable_names = {
        "_LIFECYCLE_AUTHORITY_NONCLAIM_ITEMS_V1",
        "_LAUNCH_CONTROL_FACT_ITEMS_V1",
        "_FINISH_CONTROL_FACT_ITEMS_V1",
    }
    assignments = {
        node.target.id: node.value
        for node in tree.body
        if isinstance(node, ast.AnnAssign)
        and isinstance(node.target, ast.Name)
        and node.target.id in immutable_names
    }
    assert set(assignments) == immutable_names
    assert all(isinstance(value, ast.Tuple) for value in assignments.values())

    verifier = next(
        node
        for node in tree.body
        if isinstance(node, ast.FunctionDef)
        and node.name
        == "_verify_authority_false_spot_v7_firecracker_execution_binding_v1"
    )
    all_result_allocations = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "object"
        and node.func.attr == "__new__"
    ]
    verifier_result_allocations = [
        node
        for node in ast.walk(verifier)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "object"
        and node.func.attr == "__new__"
    ]
    assert len(all_result_allocations) == 1
    assert verifier_result_allocations == all_result_allocations


def test_firecracker_authority_ratchet_rejects_seal_and_binder_alias_mutants() -> None:
    source = SPOT_V7_FIRECRACKER_AUTHORITY.read_text(encoding="utf-8")
    mutant = ast.parse(
        source
        + "\npublic_runtime_seal = _GOVERNED_RUNTIME_SEAL_V1\n"
        + "public_settlement_binder = _bind_governed_firecracker_spot_v7_settlement_v1\n",
        filename=str(SPOT_V7_FIRECRACKER_AUTHORITY),
    )

    assert _public_authority_alias_violations(mutant) == [
        "public_runtime_seal:_GOVERNED_RUNTIME_SEAL_V1",
        "public_settlement_binder:_bind_governed_firecracker_spot_v7_settlement_v1",
    ]

    public_wrapper = ast.parse(
        """
def public_capability(runtime):
    return _GovernedFirecrackerSpotV7SettlementV1(
        runtime_execution=runtime,
        seal=_GOVERNED_BINDER_SEAL_V1,
    )
""",
        filename="public_firecracker_capability_wrapper.py",
    )
    assert _public_top_level_authority_reachability(public_wrapper) == [
        "public_capability"
    ]


@pytest.mark.parametrize(
    ("path", "class_name", "method_name"),
    [
        (
            SETTLEMENT_VERIFIER_ADAPTER,
            "PinnedSettlementCertificateVerifierV1",
            "_verify_authenticated_certificate",
        ),
        (
            SOURCE_OPENED_V6_VERIFIER_ADAPTER,
            "PinnedSourceOpenedSpotSettlementVerifierV6",
            "_seal_verified_result",
        ),
    ],
)
def test_settlement_adapters_mint_recursive_authority_once_inside_verification(
    path: Path,
    class_name: str,
    method_name: str,
) -> None:
    tree = _parse(path)
    verifier = _class(tree, class_name)
    minting_method = _method(verifier, method_name)

    private_imports = {
        (imported.name, imported.asname)
        for node in tree.body
        if isinstance(node, ast.ImportFrom) and node.module == "src.core.recursive_stark_admission"
        for imported in node.names
        if imported.name in PRIVATE_AUTHORITY_NAMES
    }
    assert private_imports == {
        (name, None) for name in PRIVATE_SETTLEMENT_VERIFIER_IMPORTS
    }
    assert (
        _reserved_adapter_binding_violations(
            tree,
            allowed_imports=PRIVATE_SETTLEMENT_VERIFIER_IMPORTS,
            allowed_definitions=(
                frozenset({PRIVATE_SOURCE_OPENED_V6_SEAL})
                if path == SOURCE_OPENED_V6_VERIFIER_ADAPTER
                else frozenset()
            ),
        )
        == []
    )
    assert _private_adapter_reference_violations(tree, minting_method) == []
    assert _public_authority_alias_violations(tree) == []
    assert _private_authority_all_exports(tree) == []
    assert _direct_name_call_count(minting_method, PRIVATE_MINT) == 1
    assert _direct_name_call_count(minting_method, PRIVATE_PROVENANCE) == 1
    for method in verifier.body:
        if not isinstance(method, ast.FunctionDef) or method is minting_method:
            continue
        assert _direct_name_call_count(method, PRIVATE_MINT) == 0
        assert _direct_name_call_count(method, PRIVATE_PROVENANCE) == 0


def test_source_opened_v6_authority_seal_has_one_ordered_production_caller() -> None:
    tree = _parse(SOURCE_OPENED_V6_VERIFIER_ADAPTER)
    verifier = _class(tree, "PinnedSourceOpenedSpotSettlementVerifierV6")
    verify_and_seal = _method(verifier, "_verify_and_seal")
    seal = _method(verifier, PRIVATE_SOURCE_OPENED_V6_SEAL)

    calls = {
        name: [
            node
            for node in ast.walk(verify_and_seal)
            if isinstance(node, ast.Call) and _call_name(node) == name
        ]
        for name in (
            "_execute_verifier_once",
            "_parse_source_opened_spot_v6_response",
            PRIVATE_SOURCE_OPENED_V6_SEAL,
        )
    }
    assert {name: len(nodes) for name, nodes in calls.items()} == {
        "_execute_verifier_once": 1,
        "_parse_source_opened_spot_v6_response": 1,
        PRIVATE_SOURCE_OPENED_V6_SEAL: 1,
    }
    assert (
        _line(calls["_execute_verifier_once"][0])
        < _line(calls["_parse_source_opened_spot_v6_response"][0])
        < _line(calls[PRIVATE_SOURCE_OPENED_V6_SEAL][0])
        < _line(seal)
    )

    callers = _production_authority_method_callers(PRIVATE_SOURCE_OPENED_V6_SEAL)
    assert len(callers) == 1
    assert callers[0] == (
        "src/integration/zrpf_source_opened_spot_v6_verifier_adapter.py:"
        f"{_line(calls[PRIVATE_SOURCE_OPENED_V6_SEAL][0])}"
    )


def test_source_opened_v6_authority_seal_rejects_public_alias_and_external_call_mutants() -> None:
    source = SOURCE_OPENED_V6_VERIFIER_ADAPTER.read_text(encoding="utf-8")
    alias_mutant = ast.parse(
        source
        + "\n\npublic_authority_alias = "
        + "PinnedSourceOpenedSpotSettlementVerifierV6._seal_verified_result\n",
        filename=str(SOURCE_OPENED_V6_VERIFIER_ADAPTER),
    )
    external_call_mutant = ast.parse(
        "verifier._seal_verified_result(parsed, request)\n",
        filename="external_authority_bypass.py",
    )
    class_alias_mutant = ast.parse(
        source,
        filename=str(SOURCE_OPENED_V6_VERIFIER_ADAPTER),
    )
    mutant_verifier = _class(
        class_alias_mutant,
        "PinnedSourceOpenedSpotSettlementVerifierV6",
    )
    mutant_verifier.body.append(
        ast.parse(
            f"public_seal = {PRIVATE_SOURCE_OPENED_V6_SEAL}\n",
            filename="class_scope_authority_alias.py",
        ).body[0]
    )

    assert _public_authority_alias_violations(alias_mutant) == [
        f"public_authority_alias:{PRIVATE_SOURCE_OPENED_V6_SEAL}"
    ]
    assert _authority_method_call_lines(
        external_call_mutant,
        PRIVATE_SOURCE_OPENED_V6_SEAL,
    ) == [1]
    assert _public_authority_alias_violations(class_alias_mutant) == [
        "PinnedSourceOpenedSpotSettlementVerifierV6.public_seal:"
        f"{PRIVATE_SOURCE_OPENED_V6_SEAL}"
    ]


@pytest.mark.parametrize(
    "path",
    [SETTLEMENT_VERIFIER_ADAPTER, SOURCE_OPENED_V6_VERIFIER_ADAPTER],
)
def test_settlement_adapter_ratchet_rejects_public_recursive_authority_alias_mutant(
    path: Path,
) -> None:
    source = path.read_text(encoding="utf-8")
    mutant = ast.parse(
        source + f"\n\npublic_mint_alias = {PRIVATE_MINT}\n",
        filename=str(path),
    )

    assert _public_authority_alias_violations(mutant) == [
        f"public_mint_alias:{PRIVATE_MINT}"
    ]
    assert _private_adapter_reference_violations(
        mutant,
        _method(
            _class(
                mutant,
                (
                    "PinnedSettlementCertificateVerifierV1"
                    if path == SETTLEMENT_VERIFIER_ADAPTER
                    else "PinnedSourceOpenedSpotSettlementVerifierV6"
                ),
            ),
            (
                "_verify_authenticated_certificate"
                if path == SETTLEMENT_VERIFIER_ADAPTER
                else "_seal_verified_result"
            ),
        ),
    ) != []


@pytest.mark.parametrize(
    "path",
    [SETTLEMENT_VERIFIER_ADAPTER, SOURCE_OPENED_V6_VERIFIER_ADAPTER],
)
def test_settlement_adapter_ratchet_rejects_reserved_binding_and_export_mutants(
    path: Path,
) -> None:
    source = path.read_text(encoding="utf-8")
    shadow = ast.parse(
        source + f"\n\ndef {PRIVATE_MINT}(*_args, **_kwargs):\n    return None\n",
        filename=str(path),
    )
    exported = ast.parse(
        source + f'\n\n__all__ = ["{PRIVATE_MINT}"]\n',
        filename=str(path),
    )

    assert (
        _reserved_adapter_binding_violations(
            shadow,
            allowed_imports=PRIVATE_SETTLEMENT_VERIFIER_IMPORTS,
        )
        != []
    )
    assert _private_authority_all_exports(exported) == [f"__all__:{PRIVATE_MINT}"]


def test_automatic_root_python_hook_is_in_governed_inventory() -> None:
    assert ROOT / "sitecustomize.py" in _production_python_paths()


def test_pinned_adapter_has_one_exact_post_parse_mint_and_two_admission_paths() -> None:
    tree = _parse(PINNED_ADAPTER)
    verifier = _class(tree, "PinnedRecursiveStarkVerifier")
    verifier_method = _method(verifier, "_verify_authenticated_root")
    in_memory_method = _method(verifier, "verify_and_admit")
    durable_method = _method(verifier, "verify_and_commit")

    private_imports = {
        (imported.name, imported.asname)
        for node in tree.body
        if isinstance(node, ast.ImportFrom) and node.module == "src.core.recursive_stark_admission"
        for imported in node.names
        if imported.name in PRIVATE_AUTHORITY_NAMES
    }
    assert private_imports == {(name, None) for name in PRIVATE_ADAPTER_IMPORTS}
    assert _reserved_adapter_binding_violations(tree) == []

    calls: dict[str, list[ast.Call]] = {}
    for name in ("parse_recursive_stark_root_facts", PRIVATE_PROVENANCE, PRIVATE_MINT):
        calls[name] = [
            node
            for node in ast.walk(verifier_method)
            if isinstance(node, ast.Call) and _call_name(node) == name
        ]
    assert {name: len(nodes) for name, nodes in calls.items()} == {
        "parse_recursive_stark_root_facts": 1,
        PRIVATE_PROVENANCE: 1,
        PRIVATE_MINT: 1,
    }
    assert (
        _line(calls["parse_recursive_stark_root_facts"][0])
        < _line(calls[PRIVATE_PROVENANCE][0])
        < _line(calls[PRIVATE_MINT][0])
    )

    assert _call_counts(in_memory_method) == {
        "_verify_authenticated_root": 1,
        PRIVATE_ADMISSION: 1,
    }
    assert _call_counts(durable_method) == {
        "_require_durable_release_authority": 1,
        "_verify_authenticated_root": 1,
        PRIVATE_DURABLE_COMMIT: 1,
        "TypeError": 1,
        "type": 1,
    }


def test_durable_store_consumes_private_authority_only_in_one_private_method() -> None:
    tree = _parse(DURABLE_STORE)
    store = _class(tree, "SQLiteRecursiveStarkAdmissionStore")
    commit_method = _method(store, PRIVATE_DURABLE_COMMIT)
    execute_method = _method(store, "_execute_transaction")
    validate_method = _method(store, "_validate_commit_inputs")
    locked_reader = _function(tree, "_read_locked_evaluation")

    assert _call_counts(commit_method).get("_execute_transaction") == 1
    assert _direct_name_call_count(execute_method, "_read_locked_evaluation") == 1
    assert _direct_name_call_count(locked_reader, PRIVATE_PLANNER) == 1
    assert PRIVATE_CAPABILITY_TYPE in {
        name for node in ast.walk(commit_method) if (name := _node_name(node)) is not None
    }
    for method in store.body:
        if not isinstance(method, ast.FunctionDef) or method in {
            commit_method,
            execute_method,
            validate_method,
        }:
            continue
        references = {name for node in ast.walk(method) if (name := _node_name(node)) is not None}
        assert references.isdisjoint({PRIVATE_CAPABILITY_TYPE, PRIVATE_PLANNER, PRIVATE_SNAPSHOT})


def test_private_durable_commit_has_one_production_caller() -> None:
    callers: list[str] = []
    for path in _production_python_paths():
        tree = _parse(path)
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == PRIVATE_DURABLE_COMMIT
            ):
                callers.append(f"{path.relative_to(ROOT)}:{_line(node)}")

    assert len(callers) == 1
    assert callers[0].split(":", maxsplit=1)[0] == (
        "src/integration/recursive_stark_verifier_adapter.py"
    )


def test_architecture_ratchet_rejects_public_adapter_bypass_mutant() -> None:
    source = PINNED_ADAPTER.read_text(encoding="utf-8")
    mutant = ast.parse(
        source
        + "\n\ndef public_unverified_admission(state, facts, policy):\n"
        + f"    cap = {PRIVATE_MINT}(facts, policy)\n"
        + f"    return {PRIVATE_ADMISSION}(state, cap)\n",
        filename=str(PINNED_ADAPTER),
    )
    assert "public_unverified_admission" in _public_top_level_authority_reachability(mutant)


def test_architecture_ratchet_rejects_adapter_shadow_and_qualified_call_mutants() -> None:
    source = PINNED_ADAPTER.read_text(encoding="utf-8")
    for name in sorted(PRIVATE_ADAPTER_IMPORTS):
        shadow = ast.parse(
            source + f"\n\ndef {name}(*_args, **_kwargs):\n    return None\n",
            filename=str(PINNED_ADAPTER),
        )
        assert _reserved_adapter_binding_violations(shadow) != []

    for name, method_name in (
        (PRIVATE_PROVENANCE, "_verify_authenticated_root"),
        (PRIVATE_MINT, "_verify_authenticated_root"),
        (PRIVATE_ADMISSION, "verify_and_admit"),
    ):
        qualified_source = source.replace(f"{name}(", f"alternate.{name}(", 1)
        assert qualified_source != source
        qualified = ast.parse(qualified_source, filename=str(PINNED_ADAPTER))
        verifier = _class(qualified, "PinnedRecursiveStarkVerifier")
        method = _method(verifier, method_name)
        assert _direct_name_call_count(method, name) == 0


def test_core_exposes_no_public_capability_constructor_or_admission_wrapper() -> None:
    tree = _parse(CORE)
    top_level_names = {
        node.name
        for node in tree.body
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
    }
    top_level_names.update(
        target.id
        for node in tree.body
        if isinstance(node, ast.Assign)
        for target in node.targets
        if isinstance(target, ast.Name)
    )
    assert PRIVATE_AUTHORITY_NAMES <= top_level_names

    violations: list[str] = []
    for node in tree.body:
        if not isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name.startswith("_"):
            continue
        for descendant in ast.walk(node):
            name = _node_name(descendant)
            if name in PRIVATE_AUTHORITY_NAMES:
                violations.append(f"{node.name}:{_line(descendant)}:{name}")
    violations.extend(_public_top_level_authority_reachability(tree))
    violations.extend(_public_authority_alias_violations(tree))
    violations.extend(_private_authority_all_exports(tree))
    assert violations == []


def test_architecture_detector_rejects_public_wrapper_through_private_bridge() -> None:
    tree = ast.parse(
        """
def _admit_authenticated_recursive_stark_root():
    return None

def _private_bridge():
    return _admit_authenticated_recursive_stark_root()

def admit_without_verification():
    return _private_bridge()
"""
    )

    assert _public_top_level_authority_reachability(tree) == ["admit_without_verification"]


def test_architecture_detector_rejects_public_method_through_private_bridge() -> None:
    tree = ast.parse(
        """
def _admit_authenticated_recursive_stark_root():
    return None

def _private_bridge():
    return _admit_authenticated_recursive_stark_root()

class PublicAdmission:
    def admit_without_verification(self):
        return _private_bridge()
"""
    )

    assert _public_top_level_authority_reachability(tree) == [
        "PublicAdmission.admit_without_verification"
    ]


def test_architecture_detector_rejects_public_alias_and_all_export_mutants() -> None:
    tree = ast.parse(
        """
def _admit_authenticated_recursive_stark_root():
    return None

_private_alias = _admit_authenticated_recursive_stark_root
public_admit_alias = _private_alias
public_lambda = lambda: _admit_authenticated_recursive_stark_root()
__all__ = ["_private_alias"]
"""
    )

    assert _public_authority_alias_violations(tree) == [
        "public_admit_alias:_private_alias",
        "public_lambda:_admit_authenticated_recursive_stark_root",
    ]
    assert _private_authority_all_exports(tree) == ["__all__:_private_alias"]


def test_architecture_detector_rejects_public_async_wrapper_mutant() -> None:
    tree = ast.parse(
        """
def _admit_authenticated_recursive_stark_root():
    return None

async def admit_without_verification():
    return _admit_authenticated_recursive_stark_root()
"""
    )

    assert _public_top_level_authority_reachability(tree) == ["admit_without_verification"]


def test_public_shape_parser_cannot_mint_or_admit_authority() -> None:
    tree = _parse(PINNED_ADAPTER)
    parser = _function(tree, "parse_recursive_stark_root_facts")
    references = {name for node in ast.walk(parser) if (name := _node_name(node)) is not None}

    assert references.isdisjoint(PRIVATE_AUTHORITY_NAMES)


def test_retired_public_authority_symbols_do_not_reappear() -> None:
    violations: list[str] = []
    for path in _production_python_paths():
        source = path.read_text(encoding="utf-8")
        for name in sorted(RETIRED_PUBLIC_AUTHORITY_NAMES):
            if name in source:
                violations.append(f"{path.relative_to(ROOT)}:{name}")

    assert violations == []


def test_data_only_admission_result_has_no_production_consumer() -> None:
    violations: list[str] = []
    for path in _production_python_paths():
        if path in {CORE, PINNED_ADAPTER}:
            continue
        tree = _parse(path)
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and node.attr == "verify_and_admit":
                violations.append(f"{path.relative_to(ROOT)}:{_line(node)}:verify_and_admit")
            if _node_name(node) == DATA_ONLY_ADMISSION_RESULT:
                violations.append(
                    f"{path.relative_to(ROOT)}:{_line(node)}:{DATA_ONLY_ADMISSION_RESULT}"
                )
            if isinstance(node, ast.ImportFrom) and any(
                imported.name == DATA_ONLY_ADMISSION_RESULT for imported in node.names
            ):
                violations.append(
                    f"{path.relative_to(ROOT)}:{_line(node)}:{DATA_ONLY_ADMISSION_RESULT}"
                )

    assert violations == []


def test_production_consumer_detector_rejects_normal_and_aliased_method_use() -> None:
    tree = ast.parse(
        """
result = verifier.verify_and_admit(state=state, proof=proof, recursive_input=input)
admit = verifier.verify_and_admit
store.commit(result.state)
"""
    )

    references = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Attribute) and node.attr == "verify_and_admit"
    ]
    assert len(references) == 2


def _production_python_paths() -> tuple[Path, ...]:
    return tuple(
        sorted(
            set(PRODUCTION_FILES)
            | {path for root in PRODUCTION_ROOTS if root.is_dir() for path in root.rglob("*.py")}
        )
    )


def _parse(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def _private_authority_reference(node: ast.AST) -> str | None:
    if isinstance(node, ast.ImportFrom):
        for imported in node.names:
            if imported.name in PROTECTED_AUTHORITY_NAMES:
                return imported.name
    name = _node_name(node)
    return name if name in PROTECTED_AUTHORITY_NAMES else None


def _node_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def _is_direct_call_target(node: ast.AST, parents: dict[ast.AST, ast.AST]) -> bool:
    parent = parents.get(node)
    return isinstance(parent, ast.Call) and parent.func is node


def _call_name(node: ast.Call) -> str | None:
    return _node_name(node.func)


def _call_counts(node: ast.AST) -> dict[str, int]:
    counts: dict[str, int] = {}
    for descendant in ast.walk(node):
        if not isinstance(descendant, ast.Call):
            continue
        name = _call_name(descendant)
        if name is not None:
            counts[name] = counts.get(name, 0) + 1
    return counts


def _direct_name_call_count(node: ast.AST, name: str) -> int:
    return sum(
        1
        for descendant in ast.walk(node)
        if isinstance(descendant, ast.Call)
        and isinstance(descendant.func, ast.Name)
        and descendant.func.id == name
    )


def _public_top_level_authority_reachability(tree: ast.Module) -> list[str]:
    function_names = {
        node.name for node in tree.body if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    authority_reaching = _authority_reaching_top_level_function_names(tree)
    violations = {
        name for name in function_names if not name.startswith("_") and name in authority_reaching
    }
    for node in tree.body:
        if not isinstance(node, ast.ClassDef) or node.name.startswith("_"):
            continue
        method_graph = {
            method.name: {
                name
                for descendant in ast.walk(method)
                if isinstance(descendant, ast.Call)
                if (name := _call_name(descendant)) is not None
            }
            for method in node.body
            if isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        reaching_methods = {
            name for name, calls in method_graph.items() if not calls.isdisjoint(authority_reaching)
        }
        while True:
            discovered = {
                name
                for name, calls in method_graph.items()
                if name not in reaching_methods and not calls.isdisjoint(reaching_methods)
            }
            if not discovered:
                break
            reaching_methods.update(discovered)
        violations.update(
            f"{node.name}.{name}" for name in reaching_methods if not name.startswith("_")
        )
    return sorted(violations)


def _public_authority_alias_violations(tree: ast.Module) -> list[str]:
    violations: set[str] = set()
    module_authority_names = _authority_alias_names(tree)
    violations.update(
        _public_authority_alias_violations_in_body(
            tree.body,
            authority_names=module_authority_names,
            scope_name="",
        )
    )
    violations.update(
        _public_class_authority_alias_violations(
            tree.body,
            inherited_authority_names=module_authority_names,
            parent_scope="",
        )
    )
    return sorted(violations)


def _public_authority_alias_violations_in_body(
    body: list[ast.stmt],
    *,
    authority_names: set[str],
    scope_name: str,
) -> set[str]:
    violations: set[str] = set()
    for node in body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        sources = (
            _expression_names(node.value) & authority_names if node.value is not None else set()
        )
        if not sources:
            continue
        violations.update(
            f"{scope_name + '.' if scope_name else ''}{target}:{source}"
            for target in _assignment_names(node)
            if not target.startswith("_")
            for source in sources
        )
    return violations


def _public_class_authority_alias_violations(
    body: list[ast.stmt],
    *,
    inherited_authority_names: set[str],
    parent_scope: str,
) -> set[str]:
    violations: set[str] = set()
    for node in body:
        if not isinstance(node, ast.ClassDef):
            continue
        scope_name = f"{parent_scope}.{node.name}" if parent_scope else node.name
        authority_names = _authority_alias_names_in_body(
            node.body,
            initial_names=inherited_authority_names,
        )
        violations.update(
            _public_authority_alias_violations_in_body(
                node.body,
                authority_names=authority_names,
                scope_name=scope_name,
            )
        )
        violations.update(
            _public_class_authority_alias_violations(
                node.body,
                inherited_authority_names=authority_names,
                parent_scope=scope_name,
            )
        )
    return violations


def _private_authority_all_exports(tree: ast.Module) -> list[str]:
    authority_names = _authority_alias_names(tree)
    violations: list[str] = []
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        if "__all__" not in _assignment_names(node) or node.value is None:
            continue
        if not isinstance(node.value, (ast.List, ast.Tuple, ast.Set)):
            violations.append("__all__:dynamic")
            continue
        for element in node.value.elts:
            if (
                isinstance(element, ast.Constant)
                and isinstance(element.value, str)
                and element.value in authority_names
            ):
                violations.append(f"__all__:{element.value}")
    return sorted(violations)


def _authority_alias_names(tree: ast.Module) -> set[str]:
    authority_names = set(PROTECTED_AUTHORITY_NAMES)
    authority_names.update(_authority_reaching_top_level_function_names(tree))
    return _authority_alias_names_in_body(
        tree.body,
        initial_names=authority_names,
    )


def _authority_alias_names_in_body(
    body: list[ast.stmt],
    *,
    initial_names: set[str],
) -> set[str]:
    authority_names = set(initial_names)
    assignments = tuple(
        node for node in body if isinstance(node, (ast.Assign, ast.AnnAssign))
    )
    while True:
        discovered = {
            target
            for node in assignments
            if node.value is not None
            if not _expression_names(node.value).isdisjoint(authority_names)
            for target in _assignment_names(node)
            if target not in authority_names
        }
        if not discovered:
            return authority_names
        authority_names.update(discovered)


def _authority_reaching_top_level_function_names(tree: ast.Module) -> set[str]:
    call_graph = {
        node.name: {
            name
            for descendant in ast.walk(node)
            if isinstance(descendant, ast.Call)
            if (name := _call_name(descendant)) is not None
        }
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    authority_reaching = set(PROTECTED_AUTHORITY_NAMES)
    while True:
        discovered = {
            name
            for name, calls in call_graph.items()
            if name not in authority_reaching and not calls.isdisjoint(authority_reaching)
        }
        if not discovered:
            return authority_reaching
        authority_reaching.update(discovered)


def _assignment_names(node: ast.Assign | ast.AnnAssign) -> tuple[str, ...]:
    targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
    return tuple(name for target in targets for name in _target_names(target))


def _target_names(target: ast.expr) -> tuple[str, ...]:
    if isinstance(target, ast.Name):
        return (target.id,)
    if isinstance(target, ast.Attribute):
        return (target.attr,)
    if isinstance(target, (ast.List, ast.Tuple)):
        return tuple(name for element in target.elts for name in _target_names(element))
    return ()


def _expression_names(value: ast.expr) -> set[str]:
    return {name for node in ast.walk(value) if (name := _node_name(node)) is not None}


def _private_adapter_reference_violations(
    tree: ast.Module,
    allowed_method: ast.FunctionDef,
) -> list[str]:
    method_nodes = frozenset(ast.walk(allowed_method))
    parents = _parent_map(tree)
    violations: list[str] = []
    for node in ast.walk(tree):
        reference = _node_name(node)
        if reference not in PRIVATE_AUTHORITY_NAMES:
            continue
        if (
            not isinstance(node, ast.Name)
            or node not in method_nodes
            or not _is_direct_call_target(node, parents)
        ):
            violations.append(f"{_line(node)}:{reference}")
    return violations


def _reserved_adapter_binding_violations(
    tree: ast.Module,
    *,
    allowed_imports: frozenset[str] = PRIVATE_ADAPTER_IMPORTS,
    allowed_definitions: frozenset[str] = frozenset(),
) -> list[str]:
    parents = _parent_map(tree)
    violations: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if (
                node.name in PROTECTED_AUTHORITY_NAMES
                and node.name not in allowed_definitions
            ):
                violations.append(f"{_line(node)}:definition:{node.name}")
        elif isinstance(node, ast.arg) and node.arg in PROTECTED_AUTHORITY_NAMES:
            violations.append(f"{_line(node)}:argument:{node.arg}")
        elif (
            isinstance(node, ast.Name)
            and isinstance(node.ctx, ast.Store)
            and node.id in PROTECTED_AUTHORITY_NAMES
        ):
            violations.append(f"{_line(node)}:binding:{node.id}")
        elif isinstance(node, ast.alias):
            local_name = node.asname or node.name.rsplit(".", 1)[-1]
            if local_name not in PROTECTED_AUTHORITY_NAMES:
                continue
            parent = parents.get(node)
            is_exact_allowed_import = (
                isinstance(parent, ast.ImportFrom)
                and parent.module == "src.core.recursive_stark_admission"
                and node.name in allowed_imports
                and node.asname is None
            )
            if not is_exact_allowed_import:
                violations.append(f"{_line(node)}:import:{local_name}")
    return violations


def _authority_method_call_lines(tree: ast.AST, method_name: str) -> list[int]:
    return sorted(
        _line(node)
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == method_name
    )


def _production_authority_method_callers(method_name: str) -> list[str]:
    callers: list[str] = []
    for path in _production_python_paths():
        for line in _authority_method_call_lines(_parse(path), method_name):
            callers.append(f"{path.relative_to(ROOT)}:{line}")
    return sorted(callers)


def _line(node: ast.AST) -> int:
    return int(getattr(node, "lineno", 0))


def _class(tree: ast.Module, name: str) -> ast.ClassDef:
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == name:
            return node
    raise AssertionError(f"missing class {name}")


def _method(class_node: ast.ClassDef, name: str) -> ast.FunctionDef:
    for node in class_node.body:
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
    raise AssertionError(f"missing method {name}")


def _function(tree: ast.Module, name: str) -> ast.FunctionDef:
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
    raise AssertionError(f"missing function {name}")


def _parent_map(tree: ast.AST) -> dict[ast.AST, ast.AST]:
    return {child: parent for parent in ast.walk(tree) for child in ast.iter_child_nodes(parent)}
