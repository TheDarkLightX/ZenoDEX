"""Build and verify the compact source-bound O-007C registry."""

from __future__ import annotations

import ast
import hashlib
import json
import subprocess
from collections import defaultdict
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any, cast

from tools.check_o007b_cross_language_sink_closure_v3 import (
    check_o007b_cross_language_sink_closure_v3,
)
from tools.m6_indirect_value_sinks.dynamic import (
    DYNAMIC_CALLS,
    DYNAMIC_TARGET_SIGNATURES,
    LIFECYCLE_ORDER,
    scan_dynamic_declarations,
    scan_indirect_aliases,
    scan_lifecycle_records,
)
from tools.m6_indirect_value_sinks.model import (
    DynamicDeclarationV1,
    DynamicDispositionV1,
    GapDispositionV1,
    LifecycleDispositionV1,
    SourceDispositionV1,
    canonical_root,
    pretty_json_bytes,
    reject,
    require_relative_path,
    require_sha256,
)
from tools.m6_value_sinks.operations import combine_fingerprints
from tools.m6_value_sinks.report import build_report as build_o007a_inventory
from tools.m6_value_sinks.scanner import ValueSinkObservationV2, scan_module

REGISTRY_SCHEMA = "zenodex/m6-indirect-value-sink-registry/v1"
PROJECTION_SCHEMA = "zenodex/m6-indirect-value-sink-projection/v1"
REGISTRY_PATH = "tools/m6_indirect_value_sink_registry_v1.json"
MAX_REGISTRY_BYTES = 2 * 1024 * 1024
MAX_SOURCE_BYTES = 16 * 1024 * 1024
MAX_SOURCE_COUNT = 4096
MAX_TOTAL_SOURCE_BYTES = 512 * 1024 * 1024

EXCLUDED_PREFIXES = (
    ".agents/",
    ".claude/",
    ".codex/",
    "deprecated/",
    "docs/",
    "experiments/",
    "external/",
    "tests/",
)

# This exact exclusion keeps the reviewed runtime-source universe stable across
# Stage-A construction. It cannot absorb an unrelated tool by prefix.
EVIDENCE_TOOL_PATHS = (
    "tools/build_o007c_indirect_sink_closure_v1.py",
    "tools/check_m6_indirect_value_sinks_v1.py",
    "tools/check_o007c_indirect_sink_closure_v1.py",
    "tools/m6_indirect_value_sinks/__init__.py",
    "tools/m6_indirect_value_sinks/dynamic.py",
    "tools/m6_indirect_value_sinks/inventory.py",
    "tools/m6_indirect_value_sinks/model.py",
    "tools/m6_indirect_value_sinks/report.py",
    "tools/o007c_indirect_sink_closure_v1.py",
)

API_PREWARM_TARGETS = (
    "src/integration/api_server_settlement_parsers.py",
    "src/integration/operations.py",
    "src/integration/settlement_endogenous_lp_value_packet.py",
    "src/integration/settlement_end_to_end_certificate_packet.py",
    "src/integration/settlement_feature_extension_packet.py",
    "src/integration/settlement_lp_value_contract.py",
    "src/integration/settlement_price_attestation.py",
    "src/integration/settlement_price_provenance.py",
    "src/integration/settlement_value_contract.py",
    "src/integration/settlement_value_packet.py",
    "src/integration/settlement_witness_lifecycle.py",
)
FIRE_REFERENCE_TARGETS = (
    "src/fire/kernel/fire_burn_boost_call_v1_ref.py",
    "src/fire/kernel/fire_fee_note_v1_ref.py",
    "src/fire/kernel/fire_lp_loss_cover_v1_ref.py",
)
BATCH_REFERENCE_TARGET = (
    "generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
)
PERP_2P_TARGET = ("generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py",)
PERP_3P_TARGET = (
    "generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
)
EXACT_OUT_TARGET = ("src/integration/exact_out_route_certificate.py",)

DynamicIdentity = tuple[str, int, str, str]
GapIdentity = tuple[str, str]

# Exact reviewed identities prevent a later declaration from inheriting a
# closure or exclusion merely because it appears in a familiar file.
DYNAMIC_TARGET_SETS: dict[DynamicIdentity, tuple[str, ...]] = {
    (
        "src/fire/kernel/kernel_eval_receipt_v1.py",
        157,
        "import_module",
        "dfdfd073302b38937134ff8f02c24bc1e7ea62d34909741f04a44ffc5748cc22",
    ): FIRE_REFERENCE_TARGETS,
    (
        "src/fire/kernel/kernel_receipt_v1.py",
        115,
        "import_module",
        "4cd6c06ec788ff720089520b8440798d2df407edc1de5a7fd16536dfa5da58ab",
    ): FIRE_REFERENCE_TARGETS,
    (
        "src/fire/kernel/kernel_replay_receipt_v1.py",
        203,
        "import_module",
        "c771b1e5e515836ccafba5e5858d5b49b2fcfa4008286bb0988e5423c6eca45a",
    ): FIRE_REFERENCE_TARGETS,
    (
        "src/fire/kernel/kernel_settlement_receipt_v1.py",
        201,
        "import_module",
        "368d15aa1fa25105e7270d3605363e3e2c9eaae3a7bf14657dd7295842753a92",
    ): FIRE_REFERENCE_TARGETS,
    (
        "src/integration/api_server.py",
        100,
        "__import__",
        "eec4226d98b39224be786490b6ca21907dc697a3891f99e143e3a2b6627dbb3a",
    ): API_PREWARM_TARGETS,
    (
        "src/integration/perp_engine.py",
        810,
        "spec_from_file_location",
        "c4a49b1c6affeb19d6dfa4c72917f4eed94fe0a5c8ab91fa537f5a6614cdd383",
    ): PERP_2P_TARGET,
    (
        "src/integration/perp_engine.py",
        815,
        "exec_module",
        "b195feb479451c39cbaf1addc970938dbb4b8da013df9508cc37fa3bb5f7eccf",
    ): PERP_2P_TARGET,
    (
        "src/integration/perp_engine.py",
        868,
        "spec_from_file_location",
        "8fdc67dfb9e541459536624e5e9fd5a44f5a6a5546a5143d16af9313bec5daf5",
    ): PERP_3P_TARGET,
    (
        "src/integration/perp_engine.py",
        873,
        "exec_module",
        "e56e2f683d8afe1598adef741e0cf608030924e6f27ecc5c6c71a460b2247c9c",
    ): PERP_3P_TARGET,
    (
        "src/kernels/python/batch_auction_settler_v1_witness.py",
        207,
        "spec_from_file_location",
        "81ce952da0652917e8424aa305c61a06a3fc4338bf4b2fd8d78185d7faebbcc8",
    ): BATCH_REFERENCE_TARGET,
    (
        "src/kernels/python/batch_auction_settler_v1_witness.py",
        212,
        "exec_module",
        "e23a7f5381a831ed2186f75934ad7bf11c8cebbfb6e57420abea922fba3b7c54",
    ): BATCH_REFERENCE_TARGET,
    (
        "tools/zeno_ledger_run_local.py",
        514,
        "spec_from_file_location",
        "dd690bad3598d6f290f151f2f10dafb475f6e324e3daf1e57a0141162b5743e3",
    ): BATCH_REFERENCE_TARGET,
    (
        "tools/zeno_ledger_run_local.py",
        519,
        "exec_module",
        "9943715102aef3cf373ec1274c1a7d06e0adcc790dcc03a8b90512056714629c",
    ): BATCH_REFERENCE_TARGET,
}

RESEARCH_DYNAMIC_EXCLUSIONS: frozenset[DynamicIdentity] = frozenset(
    {
        (
            "src/agents/__init__.py",
            134,
            "import_module",
            "ec96c45e4f3bd617bf0f52d9b745a0ce5a31fc963c0b9f936666f16a928f4045",
        ),
        (
            "tools/bva/mine_bva.py",
            23,
            "spec_from_file_location",
            "687170e2692931baeb8a2b094bbc6e4a996abf6a792a4a7d3b86f3b345dca3d1",
        ),
        (
            "tools/bva/mine_bva.py",
            28,
            "exec_module",
            "8d9f83f2916512c4761acf898e32545190f19e805200568b48163981832394f8",
        ),
        (
            "tools/check_ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_20260629.py",
            18,
            "spec_from_file_location",
            "47ae736ff17d530253d854870244441e02f9a817b254e1579729c60f49a2750c",
        ),
        (
            "tools/check_ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_20260629.py",
            25,
            "exec_module",
            "6389423f4a3c5ee8dc9108a6bc1fcbf2ded22827f1e72dd2d8536f914b300955",
        ),
        (
            "tools/check_ab_child_frontier_bidirectional_transition_tau_certificate_20260629.py",
            18,
            "spec_from_file_location",
            "dc72b5a3c0b60e696adb1bbc963e16238846f12fd730804b7b529608c0ee124e",
        ),
        (
            "tools/check_ab_child_frontier_bidirectional_transition_tau_certificate_20260629.py",
            25,
            "exec_module",
            "0e645786fe81aeb498b0f1c6b041efac058082fcb3aa9aaf7121fad65778830b",
        ),
        (
            "tools/check_ab_child_frontier_corpus_root_tau_certificate_20260629.py",
            18,
            "spec_from_file_location",
            "8e1bbdd453b256d8b10718c5b795e0774f811ef6253e86a4fac35228dd51e3d1",
        ),
        (
            "tools/check_ab_child_frontier_corpus_root_tau_certificate_20260629.py",
            25,
            "exec_module",
            "f4f733a18a310d74406119466917255b31def9d224d61211bc3854ac8a934465",
        ),
        (
            "tools/check_ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_20260629.py",
            18,
            "spec_from_file_location",
            "8363c045cc3ea42f62f5a02672c0e811d58ad18925945801f9af8ee28f7f5544",
        ),
        (
            "tools/check_ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_20260629.py",
            25,
            "exec_module",
            "8a2533f99fb4ef9027b833c44155c1caa840d7bb5e23910cf8d1460f9eff5799",
        ),
        (
            "tools/check_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629.py",
            18,
            "spec_from_file_location",
            "4d3c17590f76b1d72eb2cc24ffc23afde2942d5de77e89a88e5c9c937008d819",
        ),
        (
            "tools/check_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629.py",
            25,
            "exec_module",
            "0e3dca413c0d254bcca947b3de0296f28da13ee9a5aa2eb850252cf490f5a738",
        ),
        (
            "tools/check_ab_child_frontier_transition_group_compression_tau_certificate_20260629.py",
            18,
            "spec_from_file_location",
            "57b06e79b849518783b40fac05b60595137671fe84f0ea3f9ca114669b775ef0",
        ),
        (
            "tools/check_ab_child_frontier_transition_group_compression_tau_certificate_20260629.py",
            25,
            "exec_module",
            "6991eeb17e822cea03dc7001215187f15d15f4ef31c9e8db798ab4ec33e0e35a",
        ),
        (
            "tools/check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_tau_certificate_20260629.py",
            18,
            "spec_from_file_location",
            "41d8cf33d5ea89eca83fae5eadcb6e0ed70a07ab5b6cf60f1d51bfe60bdd9a08",
        ),
        (
            "tools/check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_tau_certificate_20260629.py",
            25,
            "exec_module",
            "53b7f2ad6f48e6b1fe6b47786cc836782df71c8a1e87b722335cf286c46fd95a",
        ),
        (
            "tools/check_ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_20260629.py",
            18,
            "spec_from_file_location",
            "743d5f5cef1953db3e04a980a4a0e660634ff6609b88035d0ea4a40a61a22eaa",
        ),
        (
            "tools/check_ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_20260629.py",
            25,
            "exec_module",
            "09a14b6534e6f09cd13332dbd1a99df356fba6be77e9e156cf067555e3bf1bfa",
        ),
        (
            "tools/check_ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_20260629.py",
            19,
            "spec_from_file_location",
            "b89494072299f1be8c8ee65b4cfa4001dd565d5f540a825020d1a66b24a31df4",
        ),
        (
            "tools/check_ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_20260629.py",
            26,
            "exec_module",
            "a2808d374ee3c991d5947efdaef9ee3c31113a24cac20dccee8ea72b3b500ea3",
        ),
        (
            "tools/check_ab_transition_group_compression_lean_bridge_tau_certificate_20260629.py",
            19,
            "spec_from_file_location",
            "a04ae281db37fdd9ad6bc47690d39d1533a33c4c3e7298e95d91ee1a9364e91a",
        ),
        (
            "tools/check_ab_transition_group_compression_lean_bridge_tau_certificate_20260629.py",
            26,
            "exec_module",
            "3c5af046054fe80c7384e90be6d55c4260bd639c05f969150dbce978a6f10b84",
        ),
        (
            "tools/sealed_bid_disaster_catalog.py",
            111,
            "spec_from_file_location",
            "cb345c005c667110d7014a1465c015997b48e3c6c3b9c484f4f5594ba101d0ee",
        ),
        (
            "tools/sealed_bid_disaster_catalog.py",
            116,
            "exec_module",
            "6ffc7cc85ddb566ab010f8ce9d00d8b094094e952a890787a0a99de274b5e2f8",
        ),
        (
            "tools/zeno_oracle_workflow_evidence_status.py",
            61,
            "spec_from_file_location",
            "96eefe85307d00b4501f418f99856b178a1a6d143dbd5b9ee72e5300f4f7fb68",
        ),
        (
            "tools/zeno_oracle_workflow_evidence_status.py",
            69,
            "exec_module",
            "a917771b8ec6e432e4275bf1bc7999d3622da19d7de41c32c96fc304e0a20d38",
        ),
        (
            "tools/zenodex_ab_reserve_state_child_frontier_tau_certificate_20260629.py",
            19,
            "spec_from_file_location",
            "317d2a42be86983c5bae7b01c8c94a7e54bc4693dd0253244842755d33943c6c",
        ),
        (
            "tools/zenodex_ab_reserve_state_child_frontier_tau_certificate_20260629.py",
            26,
            "exec_module",
            "416525bef72aeec8d396b5d3430d1073dccc10b8c336f71f4c85ba728ea1495c",
        ),
        (
            "tools/zenodex_cpss_bc_research_scope_certificate_20260628.py",
            20,
            "spec_from_file_location",
            "adda22840fb54137c5e38969ee1b0a300f7e6acd589c6f6aa174a70b881825f7",
        ),
        (
            "tools/zenodex_cpss_bc_research_scope_certificate_20260628.py",
            27,
            "exec_module",
            "88423ab7a1d44b1e07ac37fa88b169a779b21d1f8e02dbef9b767a9a3f95b63c",
        ),
    }
)

GAP_DISPOSITIONS: dict[GapIdentity, tuple[GapDispositionV1, tuple[str, ...]]] = {
    (
        "generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
        "source_unscannable",
    ): (GapDispositionV1.GENERATED_SOURCE_SCANNED_AND_PINNED, PERP_3P_TARGET),
    ("src/integration/api_server.py", "__import__"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        API_PREWARM_TARGETS,
    ),
    ("src/integration/confidential_attestation_verifier.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.EXTERNAL_PROCESS_PORT_RECORDED,
        (),
    ),
    ("src/integration/dex_dispatch_exact_out_contract_handlers.py", "import_module"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        EXACT_OUT_TARGET,
    ),
    ("src/integration/dex_dispatch_exact_out_default_quote_handlers.py", "import_module"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        EXACT_OUT_TARGET,
    ),
    ("src/integration/dex_dispatch_exact_out_packet_common.py", "import_module"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        EXACT_OUT_TARGET,
    ),
    ("src/integration/dex_dispatch_exact_out_verify_handlers.py", "import_module"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        EXACT_OUT_TARGET,
    ),
    ("src/integration/perp_engine.py", "exec_module"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        PERP_2P_TARGET + PERP_3P_TARGET,
    ),
    ("src/integration/perp_source_admission_cli_verifier.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.EXTERNAL_PROCESS_PORT_RECORDED,
        (),
    ),
    ("src/integration/proof_verifier.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.EXTERNAL_PROCESS_PORT_RECORDED,
        (),
    ),
    ("src/integration/tau_runner.py", "import_module"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        (),
    ),
    ("src/integration/tau_runner.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.EXTERNAL_PROCESS_PORT_RECORDED,
        (),
    ),
    ("src/integration/zenodex_external_threshold_bls.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.EXTERNAL_PROCESS_PORT_RECORDED,
        (),
    ),
    ("tools/check_autogovnext_governance_lane_assurance_manifest.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.SOURCE_BOUND_RESEARCH_OR_OPERATOR_EXCLUSION,
        (),
    ),
    ("tools/gpu_env_check.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.SOURCE_BOUND_RESEARCH_OR_OPERATOR_EXCLUSION,
        (),
    ),
    ("tools/zeno_ledger_make_public_testnet_bundle.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
    ("tools/zeno_ledger_run_feature_suite.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
    ("tools/zeno_ledger_run_local.py", "exec_module"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        BATCH_REFERENCE_TARGET,
    ),
    ("tools/zeno_ledger_run_manifest.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
    ("tools/zenoctl.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
    ("tools/zenoctl_testnet_local/cli.py", "__import__"): (
        GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED,
        (),
    ),
    ("tools/zenoctl_testnet_local/compose.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
    ("tools/zenoctl_testnet_local/lifecycle.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
    ("tools/zenodex_oracle.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
    ("tools/zenodex_oracle.py", "unsupported_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
    ("tools/zenodex_oracle_cli.py", "unresolved_subprocess_dispatch"): (
        GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY,
        (),
    ),
}

NONCLAIMS = (
    "The registry classifies bounded source observations and grants no runtime reachability or writer authority.",
    "Source-bound research exclusions are exact records, not evidence that excluded code is semantically harmless.",
    "Dynamic target pins establish current local file identity only; they do not prove generator replay or behavioral equivalence.",
    "Callback and proof-callback syntax does not establish authenticated invocation or safe effect handling.",
    "A mounted outbox worker entrypoint is missing and migration remains unmounted in this evidence lane.",
    "O-007A and O-007B remain bounded dependencies; sole-publisher, terminal workflow, release, and production closure remain open.",
    "VM-01 remains OPEN and no production, settlement, release, migration, verifier, or value-movement authority is granted.",
)

_ROOT_KEYS = {
    "closure_gap_dispositions",
    "dynamic_dispositions",
    "inventory_summary",
    "lifecycle_dispositions",
    "nonclaims",
    "review_status",
    "schema",
    "scope",
    "source_sink_records",
    "special_statuses",
}
_SOURCE_KEYS = {
    "disposition",
    "identity_count",
    "observation_count",
    "observations_root",
    "path",
    "primary_reachable",
    "source_role",
    "source_sha256",
}
_DYNAMIC_KEYS = {
    "containment",
    "declaration_status",
    "declared_targets",
    "disposition",
    "fingerprint",
    "line",
    "mechanism",
    "path",
    "primary_reachable",
    "rationale",
    "resolved_target_class",
    "resolved_targets",
    "source_sha256",
    "target_expression",
    "target_kind",
    "target_pins",
}
_GAP_KEYS = {"disposition", "mechanism", "path", "rationale", "target_pins"}
_LIFECYCLE_KEYS = {
    "category",
    "disposition",
    "normative_ids",
    "rationale",
    "record_count",
    "records_root",
}
_TARGET_KEYS = {"path", "sha256"}
_SUMMARY_KEYS = {
    "candidate_source_root",
    "closure_gap_count",
    "closure_gaps_root",
    "dynamic_declaration_count",
    "dynamic_declarations_root",
    "dynamic_disposition_count",
    "derived_closed_static_registry_disposition_count",
    "derived_external_literal_disposition_count",
    "derived_local_literal_disposition_count",
    "closed_local_target_set_disposition_count",
    "closed_static_registry_dynamic_count",
    "evidence_tool_exclusion_count",
    "evidence_tool_exclusions_root",
    "indirect_alias_count",
    "indirect_aliases_root",
    "lifecycle_record_count",
    "lifecycle_records_root",
    "literal_dynamic_count",
    "mounted_migration_launcher_count",
    "mounted_migration_launchers_root",
    "mounted_worker_launcher_count",
    "mounted_worker_launchers_root",
    "nonprimary_candidate_count",
    "o007a_decoded_launcher_count",
    "o007a_decoded_launchers_root",
    "o007a_primary_candidate_count",
    "o007a_primary_module_count",
    "o007b_v3_artifact_sha256",
    "o007b_v3_certificate_root",
    "o007b_v3_stage_a_commit",
    "o007b_v3_stage_b_commit",
    "proof_callback_record_count",
    "proof_callback_records_root",
    "scope_candidate_count",
    "scope_formula",
    "source_sink_identity_count",
    "source_sink_observation_count",
    "source_sink_record_count",
    "source_sink_records_root",
    "source_bound_research_exclusion_disposition_count",
    "unresolved_dynamic_count",
    "unresolved_dynamic_nonprimary_count",
    "unresolved_dynamic_primary_count",
    "unresolved_dynamic_root",
    "workspace_candidate_count",
}
_SUMMARY_ROOT_KEYS = {
    key
    for key in _SUMMARY_KEYS
    if key.endswith("_root") or key in {"o007b_v3_artifact_sha256", "o007b_v3_certificate_root"}
}
_SUMMARY_COMMIT_KEYS = {"o007b_v3_stage_a_commit", "o007b_v3_stage_b_commit"}
_SUMMARY_COUNT_KEYS = {key for key in _SUMMARY_KEYS if key.endswith("_count")}
SCOPE_DESCRIPTION = (
    "All Git-tracked or unignored Python outside exact excluded prefixes, less the closed nine-file "
    "O-007C evidence-tool set; O-007A primary sources are dependencies and non-primary operation "
    "rows, dynamic declarations, lifecycle rows, and O-007A closure gaps are dispositioned here."
)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def workspace_python_candidate(path: str) -> bool:
    return path.endswith(".py") and not path.startswith(EXCLUDED_PREFIXES)


def scoped_python_candidate(path: str) -> bool:
    return workspace_python_candidate(path) and path not in EVIDENCE_TOOL_PATHS


def _workspace_paths(root: Path) -> tuple[str, ...]:
    process = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        check=False,
        capture_output=True,
    )
    if process.returncode != 0:
        reject("SOURCE_INVENTORY", "git", process.stderr.decode(errors="replace").strip())
    try:
        values = process.stdout.decode("utf-8", errors="strict").split("\0")
    except UnicodeDecodeError as exc:
        reject("SOURCE_INVENTORY", "git", f"non-UTF-8 path: {exc}")
    return tuple(sorted(set(value for value in values if value)))


def _contained_regular_file(root: Path, relative: str, *, label: str) -> Path:
    root = root.resolve()
    relative = require_relative_path(relative, path=label)
    candidate = root
    for component in Path(relative).parts:
        candidate = candidate / component
        if candidate.is_symlink():
            reject("TARGET_SYMLINK", relative, "symlink components are forbidden")
    if not candidate.exists():
        reject("TARGET_MISSING", relative, "source blob is absent")
    if not candidate.is_file():
        reject("TARGET_TYPE", relative, "source blob is not a regular file")
    try:
        resolved = candidate.resolve(strict=True)
    except (OSError, RuntimeError, ValueError) as exc:
        reject("TARGET_RESOLVE", relative, type(exc).__name__)
    if not resolved.is_relative_to(root):
        reject("TARGET_ESCAPE", relative, "resolved path escapes repository")
    return candidate


def _read_source(root: Path, relative: str, *, label: str) -> bytes:
    candidate = _contained_regular_file(root, relative, label=label)
    try:
        raw = candidate.read_bytes()
    except OSError as exc:
        reject("TARGET_READ", relative, type(exc).__name__)
    if len(raw) > MAX_SOURCE_BYTES:
        reject("SOURCE_LIMIT", relative, f"source exceeds {MAX_SOURCE_BYTES} bytes")
    return raw


def _source_role(path: str) -> str:
    if path.startswith("generated/"):
        return "GENERATED_REFERENCE"
    if path.startswith("src/"):
        return "RUNTIME_SOURCE"
    return "RESEARCH_OR_OPERATOR_TOOL"


def _source_disposition(path: str) -> SourceDispositionV1:
    if path.startswith("generated/"):
        return SourceDispositionV1.GENERATED_REFERENCE_SOURCE_BOUND
    if path.startswith("src/"):
        return SourceDispositionV1.INVENTORIED_NONPRIMARY_RUNTIME_WRITER
    return SourceDispositionV1.SOURCE_BOUND_RESEARCH_OR_OPERATOR_EXCLUSION


def _parse_sources(
    root: Path,
    candidates: Sequence[str],
    primary_modules: frozenset[str],
) -> tuple[list[dict[str, object]], dict[str, ast.Module], dict[str, bytes]]:
    if len(candidates) > MAX_SOURCE_COUNT:
        reject("SOURCE_COUNT_LIMIT", "runtime Python", str(len(candidates)))
    source_rows: list[dict[str, object]] = []
    trees: dict[str, ast.Module] = {}
    raws: dict[str, bytes] = {}
    total_bytes = 0
    for relative in candidates:
        raw = _read_source(root, relative, label="runtime Python source")
        total_bytes += len(raw)
        if total_bytes > MAX_TOTAL_SOURCE_BYTES:
            reject("SOURCE_BYTES_LIMIT", "runtime Python", str(total_bytes))
        try:
            source = raw.decode("utf-8", errors="strict")
            tree = ast.parse(source, filename=relative)
        except (UnicodeDecodeError, SyntaxError, ValueError) as exc:
            reject("SOURCE_PARSE", relative, type(exc).__name__)
        digest = _sha256(raw)
        source_rows.append(
            {
                "path": relative,
                "primary_reachable": relative in primary_modules,
                "sha256": digest,
                "size_bytes": len(raw),
                "source_role": _source_role(relative),
            }
        )
        raws[relative] = raw
        trees[relative] = tree
    return source_rows, trees, raws


def _writer_source_records(
    source_rows: Sequence[dict[str, object]],
    trees: Mapping[str, ast.Module],
    primary_modules: frozenset[str],
) -> tuple[list[dict[str, object]], int, int]:
    source_by_path = {cast(str, row["path"]): row for row in source_rows}
    grouped: dict[str, list[ValueSinkObservationV2]] = defaultdict(list)
    for path, tree in trees.items():
        if path in primary_modules:
            continue
        grouped[path].extend(scan_module(path, tree))
    records: list[dict[str, object]] = []
    occurrence_count = 0
    identity_count = 0
    for path, observations in sorted(grouped.items()):
        if not observations:
            continue
        by_identity: dict[tuple[str, str], list[ValueSinkObservationV2]] = defaultdict(list)
        for observation in observations:
            by_identity[(observation.symbol, observation.sink_kind)].append(observation)
        identity_rows = [
            {
                "fingerprint": combine_fingerprints(tuple(row.fingerprint for row in rows)),
                "occurrence_count": len(rows),
                "sink_kind": key[1],
                "symbol": key[0],
            }
            for key, rows in sorted(by_identity.items())
        ]
        source = source_by_path[path]
        records.append(
            {
                "disposition": _source_disposition(path).value,
                "identity_count": len(identity_rows),
                "observation_count": len(observations),
                "observations_root": canonical_root(
                    "zenodex/o007c-source-observations/v1", identity_rows
                ),
                "path": path,
                "primary_reachable": False,
                "source_role": source["source_role"],
                "source_sha256": source["sha256"],
            }
        )
        occurrence_count += len(observations)
        identity_count += len(identity_rows)
    return records, occurrence_count, identity_count


def _dynamic_identity(row: DynamicDeclarationV1) -> DynamicIdentity:
    return row.path, row.line, row.mechanism, row.fingerprint


def _target_pins(root: Path, paths: Sequence[str]) -> list[dict[str, str]]:
    return [
        {"path": path, "sha256": _sha256(_read_source(root, path, label="dynamic target"))}
        for path in sorted(set(paths))
    ]


def _module_candidate_paths(module_name: str) -> tuple[str, str]:
    parts = module_name.split(".")
    if not parts or any(not part.isidentifier() for part in parts):
        reject("DYNAMIC_LITERAL_TARGET", module_name, "module name is not canonical dotted Python")
    stem = "/".join(parts)
    return f"{stem}.py", f"{stem}/__init__.py"


def _existing_local_module_targets(root: Path, module_name: str) -> tuple[str, ...]:
    found: list[str] = []
    root = root.resolve()
    for relative in _module_candidate_paths(module_name):
        candidate = root / relative
        component_path = root
        for component in Path(relative).parts:
            component_path /= component
            if component_path.is_symlink():
                reject("TARGET_SYMLINK", relative, "literal module target crosses a symlink")
        if candidate.exists():
            _read_source(root, relative, label="literal dynamic module target")
            found.append(relative)
    if len(found) > 1:
        reject("AMBIGUOUS_LOCAL_MODULE", module_name, repr(found))
    return tuple(found)


def _derived_literal_disposition(
    root: Path, declaration: DynamicDeclarationV1
) -> tuple[DynamicDispositionV1, tuple[str, ...], str, str, str]:
    if len(declaration.targets) != 1:
        reject("DYNAMIC_LITERAL_TARGET", declaration.path, "literal declaration must have one target")
    literal = declaration.targets[0]
    if declaration.target_kind == "MODULE_NAME":
        local_targets = _existing_local_module_targets(root, literal)
        if local_targets:
            return (
                DynamicDispositionV1.DERIVED_LOCAL_LITERAL_TARGET,
                local_targets,
                "REPOSITORY_LOCAL_MODULE",
                "REPOSITORY_CONTAINED",
                "The literal module name resolves to one source-pinned repository module.",
            )
        return (
            DynamicDispositionV1.DERIVED_EXTERNAL_LITERAL_TARGET,
            (literal,),
            "EXTERNAL_MODULE",
            "EXTERNAL_MODULE_NOT_REPOSITORY_CONTAINED",
            "The literal module name has no repository module candidate and remains external with no authority.",
        )
    if declaration.target_kind == "FILE_LOCATION":
        try:
            relative = require_relative_path(literal, path="literal file location")
        except ValueError:
            return (
                DynamicDispositionV1.DERIVED_EXTERNAL_LITERAL_TARGET,
                (literal,),
                "EXTERNAL_FILE_LOCATION",
                "EXTERNAL_FILE_NOT_REPOSITORY_CONTAINED",
                "The literal file location is outside the canonical repository-relative namespace and has no authority.",
            )
        _read_source(root, relative, label="literal dynamic file target")
        return (
            DynamicDispositionV1.DERIVED_LOCAL_LITERAL_TARGET,
            (relative,),
            "REPOSITORY_LOCAL_FILE",
            "REPOSITORY_CONTAINED",
            "The literal file location names one source-pinned repository file.",
        )
    reject(
        "DYNAMIC_LITERAL_KIND",
        declaration.path,
        f"{declaration.line}:{declaration.target_kind}",
    )


def _dynamic_disposition_identity(row: Mapping[str, object]) -> DynamicIdentity:
    return (
        cast(str, row.get("path")),
        cast(int, row.get("line")),
        cast(str, row.get("mechanism")),
        cast(str, row.get("fingerprint")),
    )


def require_dynamic_disposition_completeness(
    declarations: Sequence[DynamicDeclarationV1], dispositions: Sequence[Mapping[str, object]]
) -> bool:
    declaration_ids = {_dynamic_identity(row) for row in declarations}
    disposition_ids = {_dynamic_disposition_identity(row) for row in dispositions}
    if len(declaration_ids) != len(declarations):
        reject("DUPLICATE_DYNAMIC_DECLARATION", "dynamic declarations", "identity collision")
    if len(disposition_ids) != len(dispositions):
        reject("DUPLICATE_DYNAMIC_DISPOSITION", "dynamic dispositions", "identity collision")
    missing = declaration_ids - disposition_ids
    if missing:
        reject("MISSING_DYNAMIC_DISPOSITION", "dynamic declarations", repr(sorted(missing)[:1]))
    surplus = disposition_ids - declaration_ids
    if surplus:
        reject("UNKNOWN_DYNAMIC_DISPOSITION", "dynamic dispositions", repr(sorted(surplus)[:1]))
    return declaration_ids == disposition_ids


def _require_registry_dynamic_declaration_binding(
    summary: Mapping[str, object], dispositions: Sequence[Mapping[str, object]]
) -> bool:
    reconstructed = [
        {
            "fingerprint": row["fingerprint"],
            "line": row["line"],
            "mechanism": row["mechanism"],
            "path": row["path"],
            "primary_reachable": row["primary_reachable"],
            "source_sha256": row["source_sha256"],
            "target_expression": row["target_expression"],
            "target_kind": row["target_kind"],
            "target_status": row["declaration_status"],
            "targets": row["declared_targets"],
        }
        for row in dispositions
    ]
    expected_root = summary.get("dynamic_declarations_root")
    actual_root = canonical_root("zenodex/o007c-dynamic-declarations/v1", reconstructed)
    if actual_root != expected_root:
        reject(
            "DYNAMIC_DECLARATION_ROOT",
            REGISTRY_PATH,
            "disposition declaration projection does not match discovered declaration root",
        )
    if len(dispositions) != summary.get("dynamic_declaration_count"):
        reject("DYNAMIC_DISPOSITION_COUNT", REGISTRY_PATH, "declaration count mismatch")
    return True


def _dynamic_dispositions(
    root: Path, declarations: Sequence[DynamicDeclarationV1]
) -> list[dict[str, object]]:
    expected_identities = set(DYNAMIC_TARGET_SETS) | set(RESEARCH_DYNAMIC_EXCLUSIONS)
    unresolved_identities = {
        _dynamic_identity(row)
        for row in declarations
        if row.target_status == "UNRESOLVED_SYNTACTIC"
    }
    if unresolved_identities != expected_identities:
        reject(
            "DYNAMIC_IDENTITY_SET",
            "unresolved dynamic declarations",
            f"missing={len(expected_identities - unresolved_identities)}, surplus={len(unresolved_identities - expected_identities)}",
        )
    rows: list[dict[str, object]] = []
    for declaration in declarations:
        identity = _dynamic_identity(declaration)
        if identity in DYNAMIC_TARGET_SETS:
            targets = DYNAMIC_TARGET_SETS[identity]
            disposition = DynamicDispositionV1.CLOSED_LOCAL_TARGET_SET
            resolved_target_class = "HUMAN_REVIEWED_LOCAL_TARGET_SET"
            containment = "REPOSITORY_CONTAINED"
            rationale = "A closed local target set is source-pinned; runtime behavior and authority remain unproved."
        elif identity in RESEARCH_DYNAMIC_EXCLUSIONS:
            targets = ()
            disposition = DynamicDispositionV1.SOURCE_BOUND_RESEARCH_EXCLUSION
            resolved_target_class = "SOURCE_BOUND_UNRESOLVED"
            containment = "UNRESOLVED"
            rationale = "The exact research or checker declaration is source-bound and excluded from authority claims."
        elif declaration.target_status == "LITERAL_TARGET":
            (
                disposition,
                targets,
                resolved_target_class,
                containment,
                rationale,
            ) = _derived_literal_disposition(root, declaration)
        elif declaration.target_status == "CLOSED_STATIC_REGISTRY":
            if declaration.target_kind != "MODULE_NAME" or not declaration.targets:
                reject(
                    "CLOSED_STATIC_REGISTRY",
                    declaration.path,
                    f"{declaration.line}:invalid derived registry",
                )
            targets = declaration.targets
            disposition = DynamicDispositionV1.DERIVED_CLOSED_STATIC_REGISTRY
            resolved_target_class = "REPOSITORY_LOCAL_MODULE_SET"
            containment = "REPOSITORY_CONTAINED"
            rationale = "The closed static registry resolves to source-pinned repository modules."
        else:
            reject(
                "UNKNOWN_DYNAMIC_DECLARATION",
                declaration.path,
                f"{declaration.line}:{declaration.mechanism}:{declaration.fingerprint}",
            )
        targets = tuple(sorted(set(targets)))
        pin_targets = (
            targets
            if disposition
            in {
                DynamicDispositionV1.CLOSED_LOCAL_TARGET_SET,
                DynamicDispositionV1.DERIVED_CLOSED_STATIC_REGISTRY,
                DynamicDispositionV1.DERIVED_LOCAL_LITERAL_TARGET,
            }
            else ()
        )
        rows.append(
            {
                "containment": containment,
                "declaration_status": declaration.target_status,
                "declared_targets": list(declaration.targets),
                "disposition": disposition.value,
                "fingerprint": declaration.fingerprint,
                "line": declaration.line,
                "mechanism": declaration.mechanism,
                "path": declaration.path,
                "primary_reachable": declaration.primary_reachable,
                "rationale": rationale,
                "resolved_target_class": resolved_target_class,
                "resolved_targets": list(targets),
                "source_sha256": declaration.source_sha256,
                "target_expression": declaration.target_expression,
                "target_kind": declaration.target_kind,
                "target_pins": _target_pins(root, pin_targets),
            }
        )
    require_dynamic_disposition_completeness(declarations, rows)
    return rows


def _gap_dispositions(root: Path, gaps: Sequence[Mapping[str, object]]) -> list[dict[str, object]]:
    actual_identities = {
        (cast(str, row.get("path")), cast(str, row.get("mechanism"))) for row in gaps
    }
    if actual_identities != set(GAP_DISPOSITIONS):
        reject(
            "CLOSURE_GAP_IDENTITY_SET",
            "O-007A closure gaps",
            f"missing={len(set(GAP_DISPOSITIONS) - actual_identities)}, surplus={len(actual_identities - set(GAP_DISPOSITIONS))}",
        )
    rows: list[dict[str, object]] = []
    for gap in sorted(gaps, key=lambda row: (str(row.get("path")), str(row.get("mechanism")))):
        path = cast(str, gap["path"])
        mechanism = cast(str, gap["mechanism"])
        selected = GAP_DISPOSITIONS.get((path, mechanism))
        if selected is None:
            reject("UNKNOWN_CLOSURE_GAP", path, mechanism)
        disposition, targets = selected
        if disposition is GapDispositionV1.GENERATED_SOURCE_SCANNED_AND_PINNED:
            rationale = "O-007C raises the source ceiling and scans and pins the generated target."
        elif disposition is GapDispositionV1.DYNAMIC_DECLARATION_DISPOSITIONED:
            rationale = "The exact dynamic declaration is represented in the O-007C dynamic registry."
        elif disposition is GapDispositionV1.EXTERNAL_PROCESS_PORT_RECORDED:
            rationale = "The unresolved external process boundary remains an explicit non-authoritative port."
        elif disposition is GapDispositionV1.UNRESOLVED_OPERATOR_PROCESS_BOUNDARY:
            rationale = "The exact operator process boundary remains unresolved and has no authority in this evidence lane."
        else:
            rationale = "The exact research or checker boundary is source-bound and excluded from authority claims."
        rows.append(
            {
                "disposition": disposition.value,
                "mechanism": mechanism,
                "path": path,
                "rationale": rationale,
                "target_pins": _target_pins(root, targets),
            }
        )
    return rows


_LIFECYCLE_DISPOSITIONS = {
    "RECOVERY": (
        LifecycleDispositionV1.INVENTORIED_RECOVERY_SURFACE,
        ("INV-011", "WF-13", "WF-14", "WF-17"),
        "Recovery-named surfaces are inventoried; exact PRE/POST reopen authority remains a separate gate.",
    ),
    "MIGRATION": (
        LifecycleDispositionV1.UNMOUNTED_MIGRATION_ENTRYPOINT,
        ("INV-011", "WF-13"),
        "O-007C records migration syntax and preserves the unmounted migration status.",
    ),
    "CALLBACK": (
        LifecycleDispositionV1.INVENTORIED_CALLBACK_SURFACE,
        ("WF-14", "WF-15"),
        "Callback and proof-callback surfaces are inventoried without invocation authority.",
    ),
    "WORKER": (
        LifecycleDispositionV1.MISSING_MOUNTED_WORKER_ENTRYPOINT,
        ("INV-011", "RSE-009", "WF-15"),
        "Worker-named surfaces are inventoried while a mounted committed-effect worker entrypoint remains missing.",
    ),
    "ADMINISTRATIVE": (
        LifecycleDispositionV1.INVENTORIED_ADMINISTRATIVE_SURFACE,
        ("INV-011", "WF-17"),
        "Administrative surfaces are inventoried without authorization or production claims.",
    ),
}


def _lifecycle_dispositions(records: Sequence[dict[str, object]]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for category in sorted(LIFECYCLE_ORDER):
        selected = [row for row in records if category in cast(list[str], row["categories"])]
        disposition, normative_ids, rationale = _LIFECYCLE_DISPOSITIONS[category]
        rows.append(
            {
                "category": category,
                "disposition": disposition.value,
                "normative_ids": list(normative_ids),
                "rationale": rationale,
                "record_count": len(selected),
                "records_root": canonical_root(
                    f"zenodex/o007c-lifecycle-{category.lower()}/v1", selected
                ),
            }
        )
    return rows


def collect_inventory_facts(
    root: Path,
    *,
    o007b_report: Mapping[str, object] | None = None,
) -> dict[str, object]:
    root = root.resolve()
    o007b = (
        check_o007b_cross_language_sink_closure_v3(root)
        if o007b_report is None
        else dict(o007b_report)
    )
    if o007b.get("ok") is not True:
        reject("O007B_V3_DEPENDENCY", "O-007B", json.dumps(o007b.get("finding"), sort_keys=True))
    o007a = build_o007a_inventory(root)
    if o007a.get("ok") is not True:
        reject("O007A_DEPENDENCY", "O-007A", json.dumps(o007a.get("findings"), sort_keys=True))
    primary_rows = cast(list[dict[str, object]], o007a["static_scanned_module_digests"])
    primary_modules = frozenset(cast(str, row["path"]) for row in primary_rows)
    paths = _workspace_paths(root)
    workspace_candidates = tuple(path for path in paths if workspace_python_candidate(path))
    excluded_present = tuple(path for path in EVIDENCE_TOOL_PATHS if path in workspace_candidates)
    if excluded_present != EVIDENCE_TOOL_PATHS:
        reject("EVIDENCE_TOOL_SET", "O-007C", "the exact nine Stage-A evidence tools must exist")
    candidates = tuple(path for path in workspace_candidates if scoped_python_candidate(path))
    source_rows, trees, _raws = _parse_sources(root, candidates, primary_modules)
    writer_records, occurrence_count, identity_count = _writer_source_records(
        source_rows, trees, primary_modules
    )
    source_sha = {cast(str, row["path"]): cast(str, row["sha256"]) for row in source_rows}
    dynamic = tuple(
        sorted(
            declaration
            for path, tree in trees.items()
            for declaration in scan_dynamic_declarations(
                path,
                tree,
                primary_reachable=path in primary_modules,
                source_sha256=source_sha[path],
            )
        )
    )
    unresolved = tuple(row for row in dynamic if row.target_status == "UNRESOLVED_SYNTACTIC")
    dynamic_dispositions = _dynamic_dispositions(root, dynamic)
    aliases = tuple(
        sorted(
            alias
            for path, tree in trees.items()
            for alias in scan_indirect_aliases(
                path, tree, primary_reachable=path in primary_modules
            )
        )
    )
    lifecycle = tuple(
        sorted(
            row
            for path, tree in trees.items()
            for row in scan_lifecycle_records(
                path, tree, primary_reachable=path in primary_modules
            )
        )
    )
    dynamic_json = [row.to_json() for row in dynamic]
    unresolved_json = [row.to_json() for row in unresolved]
    alias_json = [row.to_json() for row in aliases]
    lifecycle_json = [row.to_json() for row in lifecycle]
    proof_callbacks = [
        row
        for row in lifecycle_json
        if "CALLBACK" in cast(list[str], row["categories"])
        and "proof" in f"{row['path']}/{row['symbol']}".lower()
    ]
    closure_gaps = cast(list[dict[str, object]], o007a["declared_closure_gaps"])
    decoded_launchers = cast(list[dict[str, object]], o007a["decoded_launchers"])
    mounted_worker_launchers = [
        row
        for row in decoded_launchers
        if any(
            stem in f"{row.get('entrypoint_id', '')}/{row.get('target', '')}".lower()
            for stem in ("outbox", "worker", "deliver")
        )
    ]
    mounted_migration_launchers = [
        row
        for row in decoded_launchers
        if any(
            stem in f"{row.get('entrypoint_id', '')}/{row.get('target', '')}".lower()
            for stem in ("migration", "migrate", "cutover", "upgrade")
        )
    ]
    exclusion_rows = [
        {
            "path": path,
            "sha256": _sha256(_read_source(root, path, label="O-007C evidence tool")),
        }
        for path in EVIDENCE_TOOL_PATHS
    ]
    summary: dict[str, object] = {
        "candidate_source_root": canonical_root("zenodex/o007c-candidate-sources/v1", source_rows),
        "closure_gap_count": len(closure_gaps),
        "closure_gaps_root": canonical_root("zenodex/o007c-o007a-gaps/v1", closure_gaps),
        "dynamic_declaration_count": len(dynamic),
        "dynamic_declarations_root": canonical_root(
            "zenodex/o007c-dynamic-declarations/v1", dynamic_json
        ),
        "dynamic_disposition_count": len(dynamic_dispositions),
        "derived_closed_static_registry_disposition_count": sum(
            row["disposition"] == DynamicDispositionV1.DERIVED_CLOSED_STATIC_REGISTRY.value
            for row in dynamic_dispositions
        ),
        "derived_external_literal_disposition_count": sum(
            row["disposition"] == DynamicDispositionV1.DERIVED_EXTERNAL_LITERAL_TARGET.value
            for row in dynamic_dispositions
        ),
        "derived_local_literal_disposition_count": sum(
            row["disposition"] == DynamicDispositionV1.DERIVED_LOCAL_LITERAL_TARGET.value
            for row in dynamic_dispositions
        ),
        "closed_local_target_set_disposition_count": sum(
            row["disposition"] == DynamicDispositionV1.CLOSED_LOCAL_TARGET_SET.value
            for row in dynamic_dispositions
        ),
        "closed_static_registry_dynamic_count": sum(
            row.target_status == "CLOSED_STATIC_REGISTRY" for row in dynamic
        ),
        "evidence_tool_exclusion_count": len(exclusion_rows),
        "evidence_tool_exclusions_root": canonical_root(
            "zenodex/o007c-evidence-tool-exclusions/v1", exclusion_rows
        ),
        "indirect_alias_count": len(aliases),
        "indirect_aliases_root": canonical_root("zenodex/o007c-indirect-aliases/v1", alias_json),
        "lifecycle_record_count": len(lifecycle),
        "lifecycle_records_root": canonical_root("zenodex/o007c-lifecycle-records/v1", lifecycle_json),
        "literal_dynamic_count": sum(row.target_status == "LITERAL_TARGET" for row in dynamic),
        "mounted_migration_launcher_count": len(mounted_migration_launchers),
        "mounted_migration_launchers_root": canonical_root(
            "zenodex/o007c-mounted-migration-launchers/v1", mounted_migration_launchers
        ),
        "mounted_worker_launcher_count": len(mounted_worker_launchers),
        "mounted_worker_launchers_root": canonical_root(
            "zenodex/o007c-mounted-worker-launchers/v1", mounted_worker_launchers
        ),
        "nonprimary_candidate_count": sum(
            cast(str, row["path"]) not in primary_modules for row in source_rows
        ),
        "o007a_primary_candidate_count": sum(
            cast(str, row["path"]) in primary_modules for row in source_rows
        ),
        "o007a_primary_module_count": len(primary_modules),
        "o007b_v3_artifact_sha256": o007b["artifact_sha256"],
        "o007b_v3_certificate_root": o007b["certificate_root"],
        "o007b_v3_stage_a_commit": o007b["stage_a_commit"],
        "o007b_v3_stage_b_commit": o007b["stage_b_commit"],
        "o007a_decoded_launcher_count": len(decoded_launchers),
        "o007a_decoded_launchers_root": canonical_root(
            "zenodex/o007c-o007a-decoded-launchers/v1", decoded_launchers
        ),
        "proof_callback_record_count": len(proof_callbacks),
        "proof_callback_records_root": canonical_root(
            "zenodex/o007c-proof-callback-records/v1", proof_callbacks
        ),
        "scope_candidate_count": len(candidates),
        "scope_formula": (
            "workspace_candidate_count - evidence_tool_exclusion_count = scope_candidate_count"
        ),
        "source_sink_identity_count": identity_count,
        "source_sink_observation_count": occurrence_count,
        "source_sink_record_count": len(writer_records),
        "source_sink_records_root": canonical_root(
            "zenodex/o007c-source-sink-records/v1", writer_records
        ),
        "source_bound_research_exclusion_disposition_count": sum(
            row["disposition"] == DynamicDispositionV1.SOURCE_BOUND_RESEARCH_EXCLUSION.value
            for row in dynamic_dispositions
        ),
        "unresolved_dynamic_count": len(unresolved),
        "unresolved_dynamic_nonprimary_count": sum(not row.primary_reachable for row in unresolved),
        "unresolved_dynamic_primary_count": sum(row.primary_reachable for row in unresolved),
        "unresolved_dynamic_root": canonical_root(
            "zenodex/o007c-unresolved-dynamic/v1", unresolved_json
        ),
        "workspace_candidate_count": len(workspace_candidates),
    }
    return {
        "aliases": aliases,
        "closure_gaps": closure_gaps,
        "dynamic": dynamic,
        "dynamic_dispositions": dynamic_dispositions,
        "evidence_tool_exclusions": exclusion_rows,
        "lifecycle": lifecycle_json,
        "o007a": o007a,
        "o007b": o007b,
        "source_rows": source_rows,
        "source_sink_records": writer_records,
        "summary": summary,
        "unresolved": unresolved,
    }


def render_registry(root: Path, facts: Mapping[str, object], *, reviewed: bool) -> dict[str, object]:
    gaps = cast(Sequence[Mapping[str, object]], facts["closure_gaps"])
    lifecycle = cast(Sequence[dict[str, object]], facts["lifecycle"])
    summary = cast(Mapping[str, object], facts["summary"])
    if summary.get("mounted_worker_launcher_count") != 0:
        reject(
            "MOUNTED_WORKER_ENTRYPOINT_PRESENT",
            "O-007A decoded launchers",
            "worker status can no longer remain missing",
        )
    if summary.get("mounted_migration_launcher_count") != 0:
        reject(
            "MOUNTED_MIGRATION_ENTRYPOINT_PRESENT",
            "O-007A decoded launchers",
            "migration status can no longer remain unmounted",
        )
    return {
        "closure_gap_dispositions": _gap_dispositions(root, gaps),
        "dynamic_dispositions": facts["dynamic_dispositions"],
        "inventory_summary": facts["summary"],
        "lifecycle_dispositions": _lifecycle_dispositions(lifecycle),
        "nonclaims": list(NONCLAIMS),
        "review_status": "REVIEWED_CURRENT_SUBJECT" if reviewed else "UNREVIEWED",
        "schema": REGISTRY_SCHEMA,
        "scope": SCOPE_DESCRIPTION,
        "source_sink_records": facts["source_sink_records"],
        "special_statuses": [
            "MISSING_MOUNTED_WORKER_ENTRYPOINT",
            "UNMOUNTED_MIGRATION_ENTRYPOINT",
        ],
    }


def _reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            reject("DUPLICATE_JSON_KEY", REGISTRY_PATH, key)
        value[key] = item
    return value


def _require_string_list(row: Mapping[str, object], key: str, *, label: str) -> list[str]:
    value = row.get(key)
    if not isinstance(value, list) or any(type(item) is not str or not item for item in value):
        reject("DYNAMIC_ROW", f"{label}.{key}", "expected non-empty strings in a list")
    strings = cast(list[str], value)
    if strings != sorted(set(strings)):
        reject("DYNAMIC_ROW", f"{label}.{key}", "values must be sorted and unique")
    return strings


def _validate_dynamic_row(row: Mapping[str, object], *, label: str) -> None:
    mechanism = row.get("mechanism")
    if mechanism not in DYNAMIC_CALLS:
        reject("DYNAMIC_ROW", f"{label}.mechanism", "unsupported mechanism")
    expected_kind = DYNAMIC_TARGET_SIGNATURES[mechanism][2]
    if row.get("target_kind") != expected_kind:
        reject("DYNAMIC_ROW", f"{label}.target_kind", "mechanism target kind mismatch")
    if row.get("declaration_status") not in {
        "CLOSED_STATIC_REGISTRY",
        "LITERAL_TARGET",
        "UNRESOLVED_SYNTACTIC",
    }:
        reject("DYNAMIC_ROW", f"{label}.declaration_status", "unknown declaration status")
    if type(row.get("line")) is not int or cast(int, row["line"]) <= 0:
        reject("DYNAMIC_ROW", f"{label}.line", "positive integer required")
    if type(row.get("primary_reachable")) is not bool:
        reject("DYNAMIC_ROW", f"{label}.primary_reachable", "boolean required")
    for key in ("containment", "rationale", "resolved_target_class", "target_expression"):
        if type(row.get(key)) is not str or not cast(str, row[key]):
            reject("DYNAMIC_ROW", f"{label}.{key}", "non-empty string required")
    require_sha256(row.get("fingerprint"), path=f"{label}.fingerprint")
    declared = _require_string_list(row, "declared_targets", label=label)
    resolved = _require_string_list(row, "resolved_targets", label=label)
    pins = cast(list[dict[str, object]], row["target_pins"])
    pin_paths = [cast(str, pin["path"]) for pin in pins]
    try:
        disposition = DynamicDispositionV1(cast(str, row.get("disposition")))
    except ValueError:
        reject("DYNAMIC_ROW", f"{label}.disposition", "unknown disposition")
    status = row["declaration_status"]
    target_class = row["resolved_target_class"]
    containment = row["containment"]
    if disposition is DynamicDispositionV1.DERIVED_LOCAL_LITERAL_TARGET:
        valid = (
            status == "LITERAL_TARGET"
            and target_class in {"REPOSITORY_LOCAL_FILE", "REPOSITORY_LOCAL_MODULE"}
            and containment == "REPOSITORY_CONTAINED"
            and len(declared) == 1
            and bool(resolved)
            and pin_paths == resolved
        )
    elif disposition is DynamicDispositionV1.DERIVED_EXTERNAL_LITERAL_TARGET:
        valid = (
            status == "LITERAL_TARGET"
            and target_class in {"EXTERNAL_FILE_LOCATION", "EXTERNAL_MODULE"}
            and containment
            in {
                "EXTERNAL_FILE_NOT_REPOSITORY_CONTAINED",
                "EXTERNAL_MODULE_NOT_REPOSITORY_CONTAINED",
            }
            and len(declared) == 1
            and resolved == declared
            and not pin_paths
        )
    elif disposition is DynamicDispositionV1.DERIVED_CLOSED_STATIC_REGISTRY:
        valid = (
            status == "CLOSED_STATIC_REGISTRY"
            and target_class == "REPOSITORY_LOCAL_MODULE_SET"
            and containment == "REPOSITORY_CONTAINED"
            and bool(declared)
            and resolved == declared
            and pin_paths == resolved
        )
    elif disposition is DynamicDispositionV1.CLOSED_LOCAL_TARGET_SET:
        valid = (
            status == "UNRESOLVED_SYNTACTIC"
            and target_class == "HUMAN_REVIEWED_LOCAL_TARGET_SET"
            and containment == "REPOSITORY_CONTAINED"
            and not declared
            and bool(resolved)
            and pin_paths == resolved
        )
    else:
        valid = (
            status == "UNRESOLVED_SYNTACTIC"
            and target_class == "SOURCE_BOUND_UNRESOLVED"
            and containment == "UNRESOLVED"
            and not declared
            and not resolved
            and not pin_paths
        )
    if not valid:
        reject("DYNAMIC_ROW_RELATION", label, disposition.value)


def decode_registry(raw: bytes) -> dict[str, object]:
    if len(raw) > MAX_REGISTRY_BYTES:
        reject("REGISTRY_LIMIT", REGISTRY_PATH, str(len(raw)))
    try:
        value = json.loads(raw, object_pairs_hook=_reject_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        reject("REGISTRY_JSON", REGISTRY_PATH, type(exc).__name__)
    if not isinstance(value, dict):
        reject("REGISTRY_SHAPE", REGISTRY_PATH, "root must be an object")
    if pretty_json_bytes(value) != raw:
        reject("REGISTRY_CANONICAL", REGISTRY_PATH, "bytes must be canonical")
    _require_keys(value, _ROOT_KEYS, label="registry")
    if value.get("schema") != REGISTRY_SCHEMA:
        reject("REGISTRY_SCHEMA", REGISTRY_PATH, "schema mismatch")
    if value.get("review_status") not in {"UNREVIEWED", "REVIEWED_CURRENT_SUBJECT"}:
        reject("REGISTRY_REVIEW", REGISTRY_PATH, "unknown review status")
    if value.get("scope") != SCOPE_DESCRIPTION:
        reject("REGISTRY_SCOPE", REGISTRY_PATH, "scope mismatch")
    if value.get("nonclaims") != list(NONCLAIMS):
        reject("REGISTRY_NONCLAIMS", REGISTRY_PATH, "nonclaims mismatch")
    if value.get("special_statuses") != [
        "MISSING_MOUNTED_WORKER_ENTRYPOINT",
        "UNMOUNTED_MIGRATION_ENTRYPOINT",
    ]:
        reject("REGISTRY_STATUSES", REGISTRY_PATH, "special statuses mismatch")
    summary = value.get("inventory_summary")
    if not isinstance(summary, dict):
        reject("REGISTRY_SUMMARY", REGISTRY_PATH, "summary must be an object")
    _require_keys(summary, _SUMMARY_KEYS, label="inventory_summary")
    for key in _SUMMARY_ROOT_KEYS:
        require_sha256(summary[key], path=f"inventory_summary.{key}")
    for key in _SUMMARY_COMMIT_KEYS:
        item = summary[key]
        if type(item) is not str or len(item) != 40 or any(
            character not in "0123456789abcdef" for character in item
        ):
            reject("GIT_ID", f"inventory_summary.{key}", "expected lowercase Git object id")
    for key in _SUMMARY_COUNT_KEYS:
        if type(summary[key]) is not int or cast(int, summary[key]) < 0:
            reject("COUNT", f"inventory_summary.{key}", "expected non-negative integer")
    if summary.get("scope_formula") != (
        "workspace_candidate_count - evidence_tool_exclusion_count = scope_candidate_count"
    ):
        reject("SCOPE_FORMULA", REGISTRY_PATH, "formula label mismatch")
    for field, keys in (
        ("source_sink_records", _SOURCE_KEYS),
        ("dynamic_dispositions", _DYNAMIC_KEYS),
        ("closure_gap_dispositions", _GAP_KEYS),
        ("lifecycle_dispositions", _LIFECYCLE_KEYS),
    ):
        rows = value.get(field)
        if not isinstance(rows, list):
            reject("REGISTRY_FIELD", field, "must be a list")
        for index, row in enumerate(rows):
            if not isinstance(row, dict):
                reject("REGISTRY_ROW", f"{field}[{index}]", "must be an object")
            _require_keys(row, keys, label=f"{field}[{index}]")
            if "path" in row:
                require_relative_path(row["path"], path=f"{field}[{index}].path")
            if "source_sha256" in row:
                require_sha256(row["source_sha256"], path=f"{field}[{index}].source_sha256")
            if "observations_root" in row:
                require_sha256(row["observations_root"], path=f"{field}[{index}].observations_root")
            pins = row.get("target_pins", [])
            if not isinstance(pins, list):
                reject("TARGET_PINS", f"{field}[{index}]", "must be a list")
            for pin_index, pin in enumerate(pins):
                if not isinstance(pin, dict):
                    reject("TARGET_PIN", f"{field}[{index}].target_pins[{pin_index}]", "object required")
                _require_keys(pin, _TARGET_KEYS, label="target pin")
                require_relative_path(pin["path"], path="target pin path")
                require_sha256(pin["sha256"], path="target pin digest")
            pin_paths = [pin["path"] for pin in pins]
            if pin_paths != sorted(set(pin_paths)):
                reject("TARGET_PIN_ORDER", f"{field}[{index}]", "pins must be sorted and unique")
            if field == "dynamic_dispositions":
                _validate_dynamic_row(row, label=f"{field}[{index}]")
    _require_unique(cast(list[dict[str, object]], value["source_sink_records"]), ("path",))
    _require_unique(
        cast(list[dict[str, object]], value["dynamic_dispositions"]),
        ("path", "line", "mechanism", "fingerprint"),
    )
    _require_unique(
        cast(list[dict[str, object]], value["closure_gap_dispositions"]),
        ("path", "mechanism"),
    )
    _require_unique(cast(list[dict[str, object]], value["lifecycle_dispositions"]), ("category",))
    _require_registry_relations(value, summary)
    return value


def _require_keys(value: Mapping[str, object], expected: set[str], *, label: str) -> None:
    if set(value) != expected:
        reject(
            "UNKNOWN_FIELD",
            label,
            f"missing={sorted(expected - set(value))}, surplus={sorted(set(value) - expected)}",
        )


def _require_unique(rows: Sequence[Mapping[str, object]], fields: tuple[str, ...]) -> None:
    identities = [tuple(row.get(field) for field in fields) for row in rows]
    if len(identities) != len(set(identities)):
        reject("DUPLICATE_RECORD", REGISTRY_PATH, ",".join(fields))
    if identities != sorted(identities):
        reject("RECORD_ORDER", REGISTRY_PATH, ",".join(fields))


def _require_registry_relations(
    registry: Mapping[str, object], summary: Mapping[str, object]
) -> None:
    def count(key: str) -> int:
        return cast(int, summary[key])

    if count("workspace_candidate_count") - count("evidence_tool_exclusion_count") != count(
        "scope_candidate_count"
    ):
        reject("SCOPE_FORMULA", REGISTRY_PATH, "candidate arithmetic mismatch")
    if count("o007a_primary_candidate_count") + count("nonprimary_candidate_count") != count(
        "scope_candidate_count"
    ):
        reject("CANDIDATE_PARTITION", REGISTRY_PATH, "primary partition mismatch")
    if count("unresolved_dynamic_primary_count") + count(
        "unresolved_dynamic_nonprimary_count"
    ) != count("unresolved_dynamic_count"):
        reject("DYNAMIC_PARTITION", REGISTRY_PATH, "unresolved partition mismatch")
    if (
        count("literal_dynamic_count")
        + count("closed_static_registry_dynamic_count")
        + count("unresolved_dynamic_count")
        != count("dynamic_declaration_count")
    ):
        reject("DYNAMIC_STATUS_PARTITION", REGISTRY_PATH, "declaration status mismatch")
    if (
        count("derived_local_literal_disposition_count")
        + count("derived_external_literal_disposition_count")
        + count("derived_closed_static_registry_disposition_count")
        + count("closed_local_target_set_disposition_count")
        + count("source_bound_research_exclusion_disposition_count")
        != count("dynamic_disposition_count")
    ):
        reject("DYNAMIC_DISPOSITION_PARTITION", REGISTRY_PATH, "disposition status mismatch")
    if count("dynamic_disposition_count") != count("dynamic_declaration_count"):
        reject("DYNAMIC_DISPOSITION_COUNT", REGISTRY_PATH, "not every declaration is dispositioned")
    if count("evidence_tool_exclusion_count") != len(EVIDENCE_TOOL_PATHS):
        reject("EVIDENCE_TOOL_COUNT", REGISTRY_PATH, "exact exclusion count mismatch")
    if count("indirect_alias_count") != 0:
        reject("INDIRECT_ALIAS", REGISTRY_PATH, "reviewed indirect aliases must be absent")
    if count("mounted_worker_launcher_count") != 0:
        reject("MOUNTED_WORKER", REGISTRY_PATH, "missing-worker status is stale")
    if count("mounted_migration_launcher_count") != 0:
        reject("MOUNTED_MIGRATION", REGISTRY_PATH, "unmounted status is stale")
    collections = {
        "closure_gap_count": "closure_gap_dispositions",
        "dynamic_disposition_count": "dynamic_dispositions",
        "source_sink_record_count": "source_sink_records",
    }
    for count_key, collection_key in collections.items():
        rows = cast(list[object], registry[collection_key])
        if count(count_key) != len(rows):
            reject("RECORD_COUNT", collection_key, count_key)
    _require_registry_dynamic_declaration_binding(
        summary,
        cast(Sequence[Mapping[str, object]], registry["dynamic_dispositions"]),
    )


def validate_target_pins(root: Path, registry: Mapping[str, object]) -> None:
    for field in ("dynamic_dispositions", "closure_gap_dispositions"):
        for row in cast(list[dict[str, object]], registry[field]):
            for pin in cast(list[dict[str, str]], row["target_pins"]):
                raw = _read_source(root, pin["path"], label="registry target pin")
                if _sha256(raw) != pin["sha256"]:
                    reject("TARGET_DIGEST", pin["path"], "recorded digest mismatch")


def _record_identities(value: Mapping[str, object], field: str) -> set[tuple[object, ...]]:
    fields = {
        "source_sink_records": ("path",),
        "dynamic_dispositions": ("path", "line", "mechanism", "fingerprint"),
        "closure_gap_dispositions": ("path", "mechanism"),
        "lifecycle_dispositions": ("category",),
    }[field]
    return {
        tuple(row[name] for name in fields)
        for row in cast(list[dict[str, object]], value[field])
    }


def validate_registry(root: Path, facts: Mapping[str, object], raw: bytes) -> dict[str, object]:
    registry = decode_registry(raw)
    if registry.get("review_status") != "REVIEWED_CURRENT_SUBJECT":
        reject("REGISTRY_REVIEW", REGISTRY_PATH, "current subject is not reviewed")
    validate_target_pins(root, registry)
    expected = render_registry(root, facts, reviewed=True)
    for field in (
        "source_sink_records",
        "dynamic_dispositions",
        "closure_gap_dispositions",
        "lifecycle_dispositions",
    ):
        actual_ids = _record_identities(registry, field)
        expected_ids = _record_identities(expected, field)
        if actual_ids - expected_ids:
            reject("UNKNOWN_RECORD", field, repr(sorted(actual_ids - expected_ids)[:1]))
        if expected_ids - actual_ids:
            reject("MISSING_RECORD", field, repr(sorted(expected_ids - actual_ids)[:1]))
    if registry != expected:
        reject("COMPUTED_MISMATCH", REGISTRY_PATH, "reviewed registry differs from current facts")
    return registry


def build_projection(root: Path, facts: Mapping[str, object], registry: Mapping[str, object]) -> dict[str, object]:
    summary = cast(dict[str, object], facts["summary"])
    dynamic_dispositions = cast(
        Sequence[Mapping[str, object]], registry["dynamic_dispositions"]
    )
    if "dynamic" in facts:
        declarations = cast(Sequence[DynamicDeclarationV1], facts["dynamic"])
        all_discovered_rows_dispositioned = require_dynamic_disposition_completeness(
            declarations, dynamic_dispositions
        )
    else:
        all_discovered_rows_dispositioned = _require_registry_dynamic_declaration_binding(
            summary, dynamic_dispositions
        )
    projection: dict[str, object] = {
        "all_discovered_rows_dispositioned": all_discovered_rows_dispositioned,
        "closure_gap_disposition_count": len(
            cast(list[object], registry["closure_gap_dispositions"])
        ),
        "dynamic_disposition_count": len(cast(list[object], registry["dynamic_dispositions"])),
        "inventory_summary": summary,
        "lifecycle_dispositions": registry["lifecycle_dispositions"],
        "nonclaims": list(NONCLAIMS),
        "production_authority": "NONE",
        "release_ready": False,
        "schema": PROJECTION_SCHEMA,
        "settlement_authority": "NONE",
        "special_statuses": registry["special_statuses"],
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm01_status": "OPEN",
    }
    projection["projection_root"] = canonical_root(
        "zenodex/o007c-indirect-value-sink-projection/v1", projection
    )
    return projection
