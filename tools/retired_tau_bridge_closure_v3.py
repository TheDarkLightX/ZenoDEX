"""Pure O-003B historical Tau bridge classification and route evidence.

The artifact derives every ordinary static Python import of the named
historical bridge modules from a fixed O-002 baseline and an exact evidence
subject. It classifies the resulting 36-consumer seed and binds the finite route
refusals owned by O-003B. Test-source, generated-code, renamed-copy, dynamic,
cross-language, recovery, worker, callback, and administrative reachability
remain outside this certificate.
"""

from __future__ import annotations

import ast
import hashlib
import json
import re
from collections import Counter
from dataclasses import dataclass
from typing import Final, Iterable, Mapping, NoReturn, Sequence, cast

ARTIFACT_SCHEMA_V3: Final = "zenodex/retired-tau-bridge-closure/v3"
CHECK_SCHEMA_V3: Final = "zenodex/retired-tau-bridge-closure-check/v3"
GENERATOR_COMMAND_V3: Final = "python3 tools/build_retired_tau_bridge_closure_v3.py"
OUTPUT_PATH_V3: Final = "docs/research/ZENODEX_RETIRED_TAU_BRIDGE_CLOSURE_V3.json"

BASELINE_COMMIT_V3: Final = "59a3565b77d993a374631c2554734ce152438e15"
BASELINE_TREE_V3: Final = "5391c7713a7c4d06a2ece2db64501115034f1b1b"
PLAN_PATH_V3: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
PLAN_SHA256_V3: Final = "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f"
PLAN_ADMITTED_COMMIT_V3: Final = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
PLAN_ADMITTED_TREE_V3: Final = "7978c0df78428e806e5f19281df537fe1cfc7451"
PLAN_REGISTRY_SHA256_V3: Final = "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4"
PLAN_ADMISSION_RECEIPT_SHA256_V3: Final = (
    "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d"
)
PLAN_ADMISSION_PAYLOAD_SHA256_V3: Final = (
    "fdc2d69fe530e0098d66f4a9d5d6297296cdf896b0fb97beb0f959ae054be86d"
)
CURRENT_TAU_PATH_V3: Final = "docs/research/ZENODEX_CURRENT_TAU_COMPATIBILITY_V1.json"
CURRENT_TAU_SHA256_V3: Final = (
    "ee3646ea867a0b41ad2a6f6bd8b9c7c7848e0ebd72f83b56c2b074d58ccf0ae7"
)

MAX_ARTIFACT_BYTES_V3: Final = 524_288
MAX_SOURCE_BYTES_V3: Final = 2_097_152
MAX_DISCOVERY_PATHS_V3: Final = 4_096
MAX_DISCOVERY_TOTAL_BYTES_V3: Final = 67_108_864
BASELINE_DISCOVERY_PATH_COUNT_V3: Final = 1_406
BASELINE_DISCOVERY_PATH_SET_SHA256_V3: Final = (
    "eea0c245933a64075ccac30da37c6f98cf5e052a2f13bde1d03b4f820261a3a4"
)
DIRECT_CONSUMER_PATH_SET_SHA256_V3: Final = (
    "49572f3b42515f210244df22061a6be11d1b2249a40a7647c181b4a5676da5b1"
)
EXPECTED_BASELINE_EDGE_COUNT_V3: Final = 128
EXPECTED_CURRENT_EDGE_COUNT_V3: Final = 92
EXPECTED_UNCHANGED_EDGE_COUNT_V3: Final = 92
EXPECTED_REMOVED_EDGE_COUNT_V3: Final = 36
EXPECTED_CURRENT_ONLY_EDGE_COUNT_V3: Final = 0
EXPECTED_BASELINE_EDGE_ROOT_V3: Final = (
    "742105c34b3cad43fd830e7d81316afcef92a6371217563093436be4b56575c0"
)
EXPECTED_CURRENT_EDGE_ROOT_V3: Final = (
    "ee2bd25e8be61ac601d9d68c3a5d8f63462407b7dff01d5f119dbd2c8bd71f36"
)
EXPECTED_BASELINE_SOURCE_ROOT_V3: Final = (
    "37a179ef826ca9a3d4d6cd79ed194a1868e0e8783cbc6f279e0ec830b873cb91"
)
EXPECTED_CURRENT_SOURCE_ROOT_V3: Final = (
    "a30365fb098360556e5f2fb4bfcb79fce55bf3b55da93ec57f515e0bb4ea2eaf"
)
EXPECTED_CURRENT_ROUTE_SOURCE_ROOT_V3: Final = (
    "770a8b131a3c3d2000cb0dabee66e2c62d6af1100613ceafe8c667fdee046a70"
)

_SHA1_RE: Final = re.compile(r"^[0-9a-f]{40}$")
_SHA256_RE: Final = re.compile(r"^[0-9a-f]{64}$")
_CLASSIFICATIONS_V3: Final = ("QUARANTINED", "RESEARCH_ORACLE", "REMOVED")

DIRECT_CONSUMER_PATHS_V3: Final = (
    "src/agents/autotrader_client_policy_bundle.py",
    "src/agents/intent_signer.py",
    "src/agents/krr_bundle_artifacts.py",
    "src/agents/policy_artifacts.py",
    "src/agents/zenograph_fact_pack.py",
    "src/fire/registry/index_v1.py",
    "src/integration/api_server.py",
    "src/integration/autotrader_live.py",
    "src/integration/autotrader_live_api.py",
    "src/integration/autotrader_live_release_certificate.py",
    "src/integration/autotrader_stage_certificate.py",
    "src/integration/confidential_sealed_bid_api.py",
    "src/integration/perps_wallet_api.py",
    "src/integration/perps_wallet_encrypted_sss_backup.py",
    "src/integration/tau_testnet_dex_plugin.py",
    "src/integration/zenodex_local_signer.py",
    "src/integration/zusd_custody_registry.py",
    "src/integration/zusd_monetary_bridge.py",
    "src/integration/zusd_monetary_wallet_api.py",
    "src/integration/zusd_tau_token.py",
    "src/integration/zusd_tau_wallet_api.py",
    "src/kernels/python/strategy_submit_bundle_guard_v1_adapter.py",
    "tools/autotrader_live.py",
    "tools/build_app_root_jmt_evidence.py",
    "tools/chaos/run_chaos_experiments.py",
    "tools/dex_offline_swap_demo.py",
    "tools/tau_testnet_local_e2e.py",
    "tools/tau_testnet_local_smoke.py",
    "tools/zeno_ledger_make_public_testnet_bundle.py",
    "tools/zeno_ledger_multidocker_scenario.py",
    "tools/zeno_ledger_run_local.py",
    "tools/zenoctl_testnet_local/fixtures.py",
    "tools/zenoctl_testnet_local/lifecycle.py",
    "tools/zenodex_live_cross_stream_stateful.py",
    "tools/zenodex_perp_np_release_smoke.py",
    "tools/zusd_tau_wallet.py",
)

_BRIDGE_MODULES_V3: Final = frozenset(
    {
        "src.integration.autotrader_live",
        "src.integration.autotrader_live_api",
        "src.integration.perps_wallet_api",
        "src.integration.tau_net_client",
        "src.integration.tau_testnet_dex_plugin",
        "src.integration.zusd_monetary_bridge",
        "src.integration.zusd_monetary_wallet_api",
        "src.integration.zusd_tau_token",
        "src.integration.zusd_tau_wallet_api",
    }
)
CURRENT_PATH_OPERATIONS_V3: Final = (
    ("src/agents/autotrader_client_policy_bundle.py", ("AUTOTRADER_POLICY_BUNDLE_BUILD",)),
    ("src/agents/intent_signer.py", ("DEX_INTENT_SIGNING",)),
    ("src/agents/krr_bundle_artifacts.py", ("KRR_BUNDLE_ARTIFACT_BUILD",)),
    ("src/agents/policy_artifacts.py", ("POLICY_ARTIFACT_BUILD",)),
    ("src/agents/zenograph_fact_pack.py", ("ZENOGRAPH_FACT_PACK_BUILD",)),
    ("src/fire/registry/index_v1.py", ("FIRE_REGISTRY_INDEX_BUILD",)),
    ("src/integration/api_server.py", ("API_SERVER_STARTUP", "API_REQUEST_DISPATCH")),
    ("src/integration/confidential_sealed_bid_api.py", ("CONFIDENTIAL_SETTLEMENT",)),
    ("src/integration/perps_wallet_encrypted_sss_backup.py", ("PERPS_WALLET_BACKUP",)),
    ("src/integration/zenodex_local_signer.py", ("LOCAL_SIGNER",)),
    ("tools/build_app_root_jmt_evidence.py", ("APP_ROOT_JMT_EVIDENCE_BUILD",)),
    ("tools/zeno_ledger_make_public_testnet_bundle.py", ("PUBLIC_TESTNET_BUNDLE_BUILD",)),
    ("tools/zeno_ledger_multidocker_scenario.py", ("MULTIDOCKER_SCENARIO",)),
    ("tools/zeno_ledger_run_local.py", ("LOCAL_BLOCK_BUILD",)),
    ("tools/zenoctl_testnet_local/fixtures.py", ("LOCAL_FIXTURE_BUILD",)),
    ("tools/zenoctl_testnet_local/lifecycle.py", ("LOCAL_OPERATOR_LIFECYCLE",)),
    ("tools/zenodex_perp_np_release_smoke.py", ("PERP_NP_RELEASE_SMOKE",)),
)

RESEARCH_PATH_OPERATIONS_V3: Final = (
    ("src/integration/autotrader_live.py", ("RESEARCH_AUTOTRADER_LIVE",)),
    ("src/integration/autotrader_live_api.py", ("RESEARCH_AUTOTRADER_LIVE_API",)),
    ("src/integration/autotrader_live_release_certificate.py", ("RESEARCH_AUTOTRADER_RELEASE_CERTIFICATE",)),
    ("src/integration/autotrader_stage_certificate.py", ("RESEARCH_AUTOTRADER_STAGE_CERTIFICATE",)),
    ("src/integration/perps_wallet_api.py", ("RESEARCH_PERPS_WALLET_BRIDGE",)),
    ("src/integration/tau_testnet_dex_plugin.py", ("RESEARCH_TAU_APP_BRIDGE",)),
    ("src/integration/zusd_custody_registry.py", ("RESEARCH_ZUSD_CUSTODY_BRIDGE",)),
    ("src/integration/zusd_monetary_bridge.py", ("RESEARCH_ZUSD_MONETARY_BRIDGE",)),
    ("src/integration/zusd_monetary_wallet_api.py", ("RESEARCH_ZUSD_MONETARY_WALLET",)),
    ("src/integration/zusd_tau_token.py", ("RESEARCH_ZUSD_TAU_TOKEN",)),
    ("src/integration/zusd_tau_wallet_api.py", ("RESEARCH_ZUSD_TAU_WALLET",)),
    ("src/kernels/python/strategy_submit_bundle_guard_v1_adapter.py", ("RESEARCH_AUTOTRADER_SUBMIT_BUNDLE",)),
    ("tools/autotrader_live.py", ("RESEARCH_AUTOTRADER_CLI",)),
    ("tools/chaos/run_chaos_experiments.py", ("RESEARCH_TAU_RPC_CHAOS",)),
    ("tools/dex_offline_swap_demo.py", ("RESEARCH_TAU_DEX_OFFLINE_DEMO",)),
    ("tools/tau_testnet_local_e2e.py", ("RESEARCH_TAU_LOCAL_E2E",)),
    ("tools/tau_testnet_local_smoke.py", ("RESEARCH_TAU_LOCAL_SMOKE",)),
    ("tools/zenodex_live_cross_stream_stateful.py", ("RESEARCH_TAU_CROSS_STREAM_STATEFUL",)),
    ("tools/zusd_tau_wallet.py", ("RESEARCH_ZUSD_TAU_WALLET_CLI",)),
)

_EXTRA_CURRENT_OPERATION_IDS_V3: Final = (
    "APP_ROOT_JMT_PROMOTION_ADMISSION",
    "CORE_FEATURE_SUITE_BUILD",
    "FEATURE_LANE_BUILD",
    "LOCAL_MANIFEST_BUILD",
    "LOCAL_OPERATOR_PROFILE",
    "LOCAL_OPERATOR_STARTUP",
    "LOCAL_RUNTIME_CONFIG",
    "MANIFEST_EXECUTION",
    "NEUTRAL_ASSET_ID_CONSUMERS",
    "NEUTRAL_SIGNING_CONSUMERS",
    "NODE_PEER_PULL",
    "NODE_STARTUP",
    "NODE_STATE_WRITE",
    "OPERATOR_LOCAL_NODE_SELECTOR",
    "PRODUCTION_BOUNDARY_AUDIT",
)
_EXTRA_RESEARCH_OPERATION_IDS_V3: Final = (
    "RESEARCH_AUTOTRADER_TAU",
    "RESEARCH_HISTORICAL_TOOLING",
    "RESEARCH_LIFECYCLE_DONOR_SOURCE",
    "RESEARCH_PERPS_WALLET",
    "RESEARCH_TAU_APP_PLUGIN",
    "RESEARCH_TAU_RPC_CLIENT",
    "RESEARCH_ZUSD_MONETARY_WALLET_ORACLE",
    "RESEARCH_ZUSD_TAU_WALLET_ORACLE",
    "RESEARCH_ZUSD_TOKEN_BRIDGE",
)

CURRENT_OPERATION_IDS_V3: Final = tuple(
    sorted(
        {operation_id for _, operation_ids in CURRENT_PATH_OPERATIONS_V3 for operation_id in operation_ids}
        | set(_EXTRA_CURRENT_OPERATION_IDS_V3)
    )
)
RESEARCH_OPERATION_IDS_V3: Final = tuple(
    sorted(
        {operation_id for _, operation_ids in RESEARCH_PATH_OPERATIONS_V3 for operation_id in operation_ids}
        | set(_EXTRA_RESEARCH_OPERATION_IDS_V3)
    )
)

_ROUTE_PIN_PATHS_V3: Final = (
    "docker-compose.local-testnet.yml",
    "docker-compose.permissionless.yml",
    "docs/PRODUCTION_BOUNDARY_CLOSURE_AUDIT.md",
    CURRENT_TAU_PATH_V3,
    PLAN_PATH_V3,
    "src/integration/local_route_quarantine.py",
    "src/integration/production_promotion_evidence.py",
    "src/integration/tau_net_client.py",
    "src/integration/zeno_ledger_v0.py",
    "tests/integration/test_api_server_main.py",
    "tests/integration/test_app_root_jmt_promotion_lane.py",
    "tests/integration/test_zenoctl_compose_quiescence.py",
    "tests/integration/test_zenoctl_testnet_local.py",
    "tests/test_build_app_root_jmt_evidence.py",
    "tests/test_build_operator_release_bundle.py",
    "tests/test_check_production_boundary.py",
    "tests/test_check_production_promotion_evidence_manifest.py",
    "tools/check_container_hardening.py",
    "tools/check_production_boundary.py",
    "tools/check_production_promotion_evidence_manifest.py",
    "tools/generate_operator_systemd.py",
    "tools/permissionless_operator_preflight.py",
    "tools/zeno_ledger_make_core_feature_suite.py",
    "tools/zeno_ledger_make_feature_lane.py",
    "tools/zeno_ledger_node.py",
    "tools/zeno_ledger_run_manifest.py",
    "tools/zenoctl_testnet_local/manifest.py",
    "tools/zenoctl_testnet_local/nginx.py",
    "tools/zenodex_local_signer.py",
)
BASELINE_PIN_PATHS_V3: Final = tuple(sorted(set(DIRECT_CONSUMER_PATHS_V3) | set(_ROUTE_PIN_PATHS_V3)))
SUBJECT_PIN_PATHS_V3: Final = tuple(
    sorted(
        set(BASELINE_PIN_PATHS_V3)
        | {
            "src/integration/asset_ids.py",
            "src/integration/bls_intent_signing.py",
            "tests/integration/test_bls_intent_signing.py",
            "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py",
            "tests/integration/test_zusd_tau_token.py",
            "tests/test_check_retired_tau_bridge_closure_v3.py",
            "tools/__init__.py",
            "tools/build_m6_normative_requirements_v1.py",
            "tools/build_retired_tau_bridge_closure_v3.py",
            "tools/check_retired_tau_bridge_closure_v3.py",
            "tools/m6_normative_requirements_decisions_v1.py",
            "tools/m6_normative_requirements_v1.py",
            "tools/retired_tau_bridge_closure_v3.py",
        }
    )
)
PIN_PATHS_V3: Final = SUBJECT_PIN_PATHS_V3

_PRIMARY_ROUTE_ENV_V3: Final = (
    "PERPS_WALLET_API_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLED",
)
_ROUTE_ENV_ALIASES_V3: Final = (
    "PERPS_WALLET_API_ENABLE",
    "PERPS_WALLET_ENABLED",
    "PERPS_API_WALLET_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLE",
    "ZUSD_TAU_WALLET_ENABLED",
    "ZUSD_TAU_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLE",
    "ZUSD_MONETARY_WALLET_ENABLED",
    "ZUSD_MONETARY_API_ENABLED",
    "perps_wallet_api_enabled",
    "perps_wallet_api_enable",
    "perps_wallet_enabled",
    "perps_api_wallet_enabled",
    "zusd_tau_wallet_api_enabled",
    "zusd_tau_wallet_api_enable",
    "zusd_tau_wallet_enabled",
    "zusd_tau_api_enabled",
    "zusd_monetary_wallet_api_enabled",
    "zusd_monetary_wallet_api_enable",
    "zusd_monetary_wallet_enabled",
    "zusd_monetary_api_enabled",
)
_LIFECYCLE_DONOR_PAIRS_V3: Final = (
    ("_seed_api_state", "_seed_api_state_historical_donor"),
    ("_materialize_release_native_collateral", "_materialize_release_native_collateral_historical_donor"),
    ("_run_release_flow_smoke", "_run_release_flow_smoke_historical_donor"),
    ("_run_cloudflare_quick_tunnel", "_run_cloudflare_quick_tunnel_historical_donor"),
    ("_zusd_transfer_payload", "_zusd_transfer_payload_historical_donor"),
    ("_run_perps_wallet_cycle_smoke", "_run_perps_wallet_cycle_smoke_historical_donor"),
)


@dataclass(frozen=True)
class SourceFileV3:
    path: str
    git_blob_sha: str
    data: bytes


@dataclass(frozen=True)
class SourceSnapshotV3:
    commit: str
    tree: str
    files: tuple[SourceFileV3, ...]
    discovery: PythonImportDiscoveryV3 | None = None


@dataclass(frozen=True)
class SubjectSnapshotV3:
    captured_head: str
    rechecked_head: str
    baseline: SourceSnapshotV3
    subject: SourceSnapshotV3
    baseline_is_subject_ancestor: bool
    subject_is_current_ancestor: bool
    current_discovery: PythonImportDiscoveryV3 | None = None


@dataclass(frozen=True, order=True)
class ImportEdgeV3:
    source_path: str
    scope: str
    dependency_kind: str
    target_module: str
    imported_member: str
    bound_name: str

    def target(self) -> str:
        if self.imported_member == "*":
            return self.target_module
        return f"{self.target_module}::{self.imported_member}"

    def to_dict(self) -> dict[str, str]:
        return {
            "bound_name": self.bound_name,
            "dependency_kind": self.dependency_kind,
            "imported_member": self.imported_member,
            "scope": self.scope,
            "source_path": self.source_path,
            "target": self.target(),
            "target_module": self.target_module,
        }

    def to_hash_row(self) -> list[str]:
        return [
            self.source_path,
            self.scope,
            self.dependency_kind,
            self.target_module,
            self.imported_member,
            self.bound_name,
        ]


@dataclass(frozen=True)
class PythonImportDiscoveryV3:
    paths: tuple[str, ...]
    edges: tuple[ImportEdgeV3, ...]
    source_root_sha256: str


@dataclass
class ClosureRejectV3(ValueError):
    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise ClosureRejectV3(code, path, detail)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git_blob_sha(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()  # noqa: S324 - Git object identity


def canonical_json_bytes_v3(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n").encode("utf-8")


def _decode_json_object(raw: bytes, path: str) -> dict[str, object]:
    def reject_duplicates(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                _reject("DUPLICATE_JSON_KEY", path, key)
            result[key] = value
        return result

    try:
        value = json.loads(raw, object_pairs_hook=reject_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("JSON_SOURCE", path, type(exc).__name__)
    if type(value) is not dict:
        _reject("JSON_OBJECT", path, "root must be an exact object")
    return value


def _parse_python(source: Mapping[str, bytes], path: str) -> ast.Module:
    try:
        return ast.parse(source[path], filename=path)
    except (KeyError, MemoryError, RecursionError, SyntaxError, ValueError) as exc:
        _reject("PYTHON_SOURCE", path, type(exc).__name__)


def _path_set_sha256(paths: Sequence[str]) -> str:
    return _sha256(("\n".join(paths) + "\n").encode("utf-8"))


def is_python_discovery_path_v3(path: object) -> bool:
    if type(path) is not str or not path.endswith(".py"):
        return False
    if path.startswith(("tests/", "generated/", "/")) or any(
        character in path for character in ("\\", "\n", "\r", "\x00")
    ):
        return False
    parts = path.split("/")
    return bool(parts) and all(part not in {"", ".", ".."} for part in parts)


def _source_manifest(files: Mapping[str, SourceFileV3], paths: Sequence[str]) -> list[dict[str, object]]:
    return [{"path": path, "sha256": _sha256(files[path].data), "size": len(files[path].data)} for path in paths]


def _manifest_root(rows: object) -> str:
    return _sha256(canonical_json_bytes_v3(rows))


def _validate_source_snapshot(
    snapshot: SourceSnapshotV3,
    *,
    expected_paths: tuple[str, ...],
    role: str,
) -> dict[str, SourceFileV3]:
    if type(snapshot) is not SourceSnapshotV3:
        _reject("SNAPSHOT_TYPE", role, "requires exact SourceSnapshotV3")
    if _SHA1_RE.fullmatch(snapshot.commit) is None or _SHA1_RE.fullmatch(snapshot.tree) is None:
        _reject("GIT_ID", role, "commit and tree must be lowercase Git object ids")
    if type(snapshot.files) is not tuple or len(snapshot.files) != len(expected_paths):
        _reject("SOURCE_SCOPE", role, "pinned source cardinality drift")
    result: dict[str, SourceFileV3] = {}
    for expected_path, item in zip(expected_paths, snapshot.files, strict=True):
        if type(item) is not SourceFileV3 or item.path != expected_path:
            _reject("SOURCE_SCOPE", role, f"expected ordered path {expected_path}")
        if (
            type(item.git_blob_sha) is not str
            or _SHA1_RE.fullmatch(item.git_blob_sha) is None
            or type(item.data) is not bytes
            or len(item.data) > MAX_SOURCE_BYTES_V3
        ):
            _reject("SOURCE_SHAPE", expected_path, "invalid bounded source row")
        if _git_blob_sha(item.data) != item.git_blob_sha:
            _reject("SOURCE_BLOB", expected_path, "bytes do not match Git blob id")
        if item.path in result:
            _reject("SOURCE_SCOPE", role, f"duplicate path {item.path}")
        result[item.path] = item
    return result


def _snapshot_sources(snapshot: SubjectSnapshotV3) -> tuple[dict[str, SourceFileV3], dict[str, SourceFileV3]]:
    if type(snapshot) is not SubjectSnapshotV3:
        _reject("SNAPSHOT_TYPE", "snapshot", "requires exact SubjectSnapshotV3")
    if snapshot.captured_head != snapshot.rechecked_head:
        _reject("HEAD_CHANGED", "Git", "HEAD changed during bounded acquisition")
    if _SHA1_RE.fullmatch(snapshot.captured_head) is None:
        _reject("GIT_ID", "Git", "captured HEAD must be a lowercase Git object id")
    if snapshot.baseline.commit != BASELINE_COMMIT_V3:
        _reject("BASELINE_COMMIT", "Git", "O-002 baseline commit drift")
    if snapshot.baseline.tree != BASELINE_TREE_V3:
        _reject("BASELINE_TREE", "Git", "O-002 baseline tree drift")
    if type(snapshot.baseline_is_subject_ancestor) is not bool:
        _reject("ANCESTRY_TYPE", "Git", "ancestry result must be an exact bool")
    if not snapshot.baseline_is_subject_ancestor:
        _reject("BASELINE_ANCESTRY", "Git", "O-002 baseline is off subject lineage")
    if type(snapshot.subject_is_current_ancestor) is not bool:
        _reject("ANCESTRY_TYPE", "Git", "subject ancestry result must be an exact bool")
    if not snapshot.subject_is_current_ancestor:
        _reject("SUBJECT_ANCESTRY", "Git", "evidence subject is off current lineage")
    baseline = _validate_source_snapshot(snapshot.baseline, expected_paths=BASELINE_PIN_PATHS_V3, role="baseline")
    subject = _validate_source_snapshot(snapshot.subject, expected_paths=SUBJECT_PIN_PATHS_V3, role="subject")
    return baseline, subject


def require_terminal_snapshot_match_v3(
    initial: SubjectSnapshotV3,
    terminal: SubjectSnapshotV3,
    *,
    expected_head: str,
) -> None:
    """Reject observed source or discovery drift before checker acceptance."""

    if type(initial) is not SubjectSnapshotV3 or type(terminal) is not SubjectSnapshotV3:
        _reject("SNAPSHOT_TYPE", "terminal replay", "requires exact SubjectSnapshotV3")
    if (
        initial.captured_head != expected_head
        or initial.rechecked_head != expected_head
        or terminal.captured_head != expected_head
        or terminal.rechecked_head != expected_head
    ):
        _reject("HEAD_CHANGED", expected_head, "HEAD changed during terminal source replay")
    if terminal.baseline != initial.baseline or terminal.subject != initial.subject:
        _reject(
            "WORKTREE_SOURCE_CHANGED",
            "terminal replay",
            "pinned source snapshot changed before acceptance",
        )
    if terminal.current_discovery != initial.current_discovery:
        _reject(
            "CURRENT_DISCOVERY_CHANGED",
            "terminal replay",
            "Python discovery path or edge projection changed before acceptance",
        )
    if terminal != initial:
        _reject(
            "WORKTREE_INPUT_CHANGED",
            "terminal replay",
            "live snapshot metadata changed before acceptance",
        )


def _validate_discovery_snapshot(
    discovery: PythonImportDiscoveryV3 | None,
    *,
    role: str,
) -> PythonImportDiscoveryV3:
    if type(discovery) is not PythonImportDiscoveryV3:
        _reject("DISCOVERY_TYPE", role, "requires exact PythonImportDiscoveryV3")
    paths = discovery.paths
    edges = discovery.edges
    source_root_sha256 = discovery.source_root_sha256
    if (
        type(paths) is not tuple
        or not paths
        or len(paths) > MAX_DISCOVERY_PATHS_V3
        or any(type(path) is not str for path in paths)
        or tuple(sorted(paths)) != paths
        or len(set(paths)) != len(paths)
    ):
        _reject("DISCOVERY_PATH_SET", role, "requires a sorted unique bounded tuple")
    for path in paths:
        if not is_python_discovery_path_v3(path):
            _reject("DISCOVERY_PATH", str(path), "outside ordinary Python scope")
    if type(edges) is not tuple or any(
        type(edge) is not ImportEdgeV3 for edge in edges
    ):
        _reject("DISCOVERY_EDGE_TYPE", role, "requires exact ImportEdgeV3 rows")
    if type(source_root_sha256) is not str or _SHA256_RE.fullmatch(source_root_sha256) is None:
        _reject("DISCOVERY_SOURCE_ROOT", role, "requires one lowercase SHA-256 digest")
    if tuple(sorted(edges)) != edges:
        _reject("DISCOVERY_EDGE_SET", role, "requires a sorted exact tuple")
    path_set = set(paths)
    for edge in edges:
        if (
            edge.source_path not in path_set
            or edge.target_module not in _BRIDGE_MODULES_V3
            or edge.dependency_kind not in {"FROM", "FROM_MODULE", "IMPORT"}
            or any(
                type(value) is not str or not value
                for value in (
                    edge.scope,
                    edge.imported_member,
                    edge.bound_name,
                )
            )
        ):
            _reject("DISCOVERY_EDGE_SHAPE", edge.source_path, edge.target())
    return discovery


def _snapshot_discoveries(
    snapshot: SubjectSnapshotV3,
) -> tuple[PythonImportDiscoveryV3, PythonImportDiscoveryV3, PythonImportDiscoveryV3]:
    baseline = _validate_discovery_snapshot(
        snapshot.baseline.discovery,
        role="baseline discovery",
    )
    subject = _validate_discovery_snapshot(
        snapshot.subject.discovery,
        role="subject discovery",
    )
    current = _validate_discovery_snapshot(
        snapshot.current_discovery,
        role="current worktree discovery",
    )
    if (
        len(baseline.paths) != BASELINE_DISCOVERY_PATH_COUNT_V3
        or _path_set_sha256(baseline.paths)
        != BASELINE_DISCOVERY_PATH_SET_SHA256_V3
    ):
        _reject(
            "BASELINE_DISCOVERY_PATH_SET",
            "baseline discovery",
            f"count={len(baseline.paths)} root={_path_set_sha256(baseline.paths)}",
        )
    return baseline, subject, current


def _module_package(path: str) -> tuple[str, ...]:
    if not path.endswith(".py"):
        _reject("PYTHON_PATH", path, "import projection accepts Python files only")
    return tuple(path[:-3].split("/")[:-1])


def _resolve_from_module(path: str, node: ast.ImportFrom) -> str:
    if node.level == 0:
        return node.module or ""
    package = _module_package(path)
    keep = len(package) - (node.level - 1)
    if keep < 0:
        _reject("RELATIVE_IMPORT_SCOPE", path, f"relative level {node.level} escapes package")
    parts = list(package[:keep])
    if node.module:
        parts.extend(node.module.split("."))
    return ".".join(parts)


class _ImportVisitorV3(ast.NodeVisitor):
    def __init__(self, path: str) -> None:
        self._path = path
        self._scope: list[str] = []
        self.rows: list[ImportEdgeV3] = []

    def _visit_scoped(self, name: str, node: ast.AST) -> None:
        self._scope.append(name)
        self.generic_visit(node)
        self._scope.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._visit_scoped(node.name, node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._visit_scoped(node.name, node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._visit_scoped(node.name, node)

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            if alias.name in _BRIDGE_MODULES_V3:
                self.rows.append(
                    ImportEdgeV3(
                        self._path,
                        ".".join(self._scope) or "<module>",
                        "IMPORT",
                        alias.name,
                        "*",
                        alias.asname or alias.name.split(".")[0],
                    )
                )

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        module = _resolve_from_module(self._path, node)
        for alias in node.names:
            candidate_module = f"{module}.{alias.name}" if module else alias.name
            if module in _BRIDGE_MODULES_V3:
                dependency_kind = "FROM"
                target_module = module
                imported_member = alias.name
            elif candidate_module in _BRIDGE_MODULES_V3:
                dependency_kind = "FROM_MODULE"
                target_module = candidate_module
                imported_member = "*"
            else:
                continue
            self.rows.append(
                ImportEdgeV3(
                    self._path,
                    ".".join(self._scope) or "<module>",
                    dependency_kind,
                    target_module,
                    imported_member,
                    alias.asname or alias.name,
                )
            )


def scan_bridge_import_edges_v3(source: Mapping[str, bytes]) -> tuple[ImportEdgeV3, ...]:
    if set(source) != set(DIRECT_CONSUMER_PATHS_V3):
        _reject("SOURCE_SCOPE", "direct consumers", "exact 36-path projection required")
    rows: list[ImportEdgeV3] = []
    for path in DIRECT_CONSUMER_PATHS_V3:
        visitor = _ImportVisitorV3(path)
        visitor.visit(_parse_python(source, path))
        rows.extend(visitor.rows)
    return tuple(sorted(rows))


def discover_bridge_imports_v3(
    source: Mapping[str, bytes],
) -> PythonImportDiscoveryV3:
    raw_paths = tuple(source)
    if any(type(path) is not str for path in raw_paths):
        _reject("DISCOVERY_PATH", "Python discovery", "requires exact strings")
    paths = tuple(sorted(raw_paths))
    if not paths or len(paths) > MAX_DISCOVERY_PATHS_V3:
        _reject("DISCOVERY_PATH_COUNT", "Python discovery", str(len(paths)))
    if len(set(paths)) != len(paths):
        _reject("DISCOVERY_PATH_SET", "Python discovery", "duplicate path")
    total_bytes = 0
    rows: list[ImportEdgeV3] = []
    source_rows: list[dict[str, object]] = []
    for path in paths:
        if not is_python_discovery_path_v3(path):
            _reject("DISCOVERY_PATH", str(path), "outside ordinary Python scope")
        raw = source[path]
        if type(raw) is not bytes or len(raw) > MAX_SOURCE_BYTES_V3:
            _reject("DISCOVERY_SOURCE", path, "requires bounded exact bytes")
        total_bytes += len(raw)
        if total_bytes > MAX_DISCOVERY_TOTAL_BYTES_V3:
            _reject("DISCOVERY_TOTAL_BYTES", "Python discovery", str(total_bytes))
        source_rows.append(
            {"path": path, "sha256": _sha256(raw), "size": len(raw)}
        )
        visitor = _ImportVisitorV3(path)
        visitor.visit(_parse_python(source, path))
        rows.extend(visitor.rows)
    return PythonImportDiscoveryV3(
        paths=paths,
        edges=tuple(sorted(rows)),
        source_root_sha256=_manifest_root(source_rows),
    )


def _first_counter_extra(
    candidate: Counter[ImportEdgeV3],
    reference: Counter[ImportEdgeV3],
) -> ImportEdgeV3 | None:
    return next(
        (
            edge
            for edge in sorted(candidate)
            if candidate[edge] > reference[edge]
        ),
        None,
    )


def _edge_reject_detail(edge: ImportEdgeV3) -> str:
    return (
        f"{edge.scope}:{edge.dependency_kind}:"
        f"{edge.target()}:{edge.bound_name}"
    )


def _require_discovery_closure(
    *,
    baseline_direct: tuple[ImportEdgeV3, ...],
    subject_direct: tuple[ImportEdgeV3, ...],
    baseline_discovery: PythonImportDiscoveryV3,
    subject_discovery: PythonImportDiscoveryV3,
    current_discovery: PythonImportDiscoveryV3,
) -> dict[str, object]:
    baseline_direct_counts = Counter(baseline_direct)
    subject_direct_counts = Counter(subject_direct)
    baseline_discovered_counts = Counter(baseline_discovery.edges)
    subject_discovered_counts = Counter(subject_discovery.edges)
    current_discovered_counts = Counter(current_discovery.edges)

    baseline_extra = _first_counter_extra(
        baseline_discovered_counts,
        baseline_direct_counts,
    )
    baseline_missing = _first_counter_extra(
        baseline_direct_counts,
        baseline_discovered_counts,
    )
    if baseline_extra is not None or baseline_missing is not None:
        edge = baseline_extra or baseline_missing
        if edge is None:
            _reject("BASELINE_DISCOVERY_EDGE_SET", "baseline discovery", "unknown drift")
        _reject(
            "BASELINE_DISCOVERY_EDGE_SET",
            edge.source_path,
            _edge_reject_detail(edge),
        )
    baseline_consumers = tuple(
        sorted({edge.source_path for edge in baseline_discovery.edges})
    )
    if baseline_consumers != DIRECT_CONSUMER_PATHS_V3:
        _reject(
            "BASELINE_DISCOVERY_CONSUMER_SET",
            "baseline discovery",
            _path_set_sha256(baseline_consumers),
        )

    subject_extra = _first_counter_extra(
        subject_discovered_counts,
        subject_direct_counts,
    )
    if subject_extra is not None:
        _reject(
            "UNCLASSIFIED_RETIRED_TAU_BRIDGE_IMPORT",
            subject_extra.source_path,
            _edge_reject_detail(subject_extra),
        )
    subject_missing = _first_counter_extra(
        subject_direct_counts,
        subject_discovered_counts,
    )
    if subject_missing is not None:
        _reject(
            "DISCOVERY_INCOMPLETE",
            subject_missing.source_path,
            _edge_reject_detail(subject_missing),
        )

    current_extra = _first_counter_extra(
        current_discovered_counts,
        subject_discovered_counts,
    )
    if current_extra is not None:
        _reject(
            "UNCLASSIFIED_RETIRED_TAU_BRIDGE_IMPORT",
            current_extra.source_path,
            _edge_reject_detail(current_extra),
        )
    current_missing = _first_counter_extra(
        subject_discovered_counts,
        current_discovered_counts,
    )
    if current_missing is not None:
        _reject(
            "CURRENT_DISCOVERY_DRIFT",
            current_missing.source_path,
            _edge_reject_detail(current_missing),
        )

    return {
        "baseline_discovered_consumer_count": len(baseline_consumers),
        "baseline_discovered_edge_count": len(baseline_discovery.edges),
        "baseline_python_path_count": len(baseline_discovery.paths),
        "baseline_python_path_set_sha256": _path_set_sha256(
            baseline_discovery.paths
        ),
        "python_discovery_scope": (
            "GIT_TREE_BASELINE_AND_SUBJECT_PLUS_CURRENT_INDEX_OR_UNTRACKED_"
            "NONIGNORED_NONTEST_NONGENERATED_STATIC_PYTHON_IMPORTS"
        ),
        "subject_discovered_consumer_count": len(
            {edge.source_path for edge in subject_discovery.edges}
        ),
        "subject_discovered_edge_count": len(subject_discovery.edges),
        "subject_python_path_count": len(subject_discovery.paths),
        "subject_python_path_set_sha256": _path_set_sha256(
            subject_discovery.paths
        ),
    }


def _edge_manifest(edges: Sequence[ImportEdgeV3]) -> list[list[str]]:
    return [edge.to_hash_row() for edge in edges]


def _unique_top_level_function(
    tree: ast.Module,
    name: str,
) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
    matches = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == name
    ]
    return matches[0] if len(matches) == 1 else None


def _unique_top_level_class(tree: ast.Module, name: str) -> ast.ClassDef | None:
    matches = [
        node
        for node in tree.body
        if isinstance(node, ast.ClassDef) and node.name == name
    ]
    return matches[0] if len(matches) == 1 else None


def _unique_direct_method(
    class_node: ast.ClassDef,
    name: str,
) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
    matches = [
        node
        for node in class_node.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == name
    ]
    return matches[0] if len(matches) == 1 else None


def _binding_root_name(node: ast.AST) -> str | None:
    current = node
    while isinstance(current, ast.Attribute):
        current = current.value
    return current.id if isinstance(current, ast.Name) else None


def _target_rewrites_binding(target: ast.AST, protected: frozenset[str]) -> bool:
    if isinstance(target, ast.Name):
        return target.id in protected
    if isinstance(target, ast.Attribute):
        return _binding_root_name(target) in protected
    if isinstance(target, (ast.List, ast.Tuple)):
        return any(
            _target_rewrites_binding(item, protected) for item in target.elts
        )
    if isinstance(target, ast.Starred):
        return _target_rewrites_binding(target.value, protected)
    return False


def _require_no_binding_rewrites(
    tree: ast.Module,
    *,
    path: str,
    code: str,
    names: tuple[str, ...],
) -> None:
    protected = frozenset(names)
    for node in ast.walk(tree):
        targets: tuple[ast.AST, ...] = ()
        assigned_value: ast.AST | None = None
        if isinstance(node, ast.Assign):
            targets = tuple(node.targets)
            assigned_value = node.value
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
            targets = (node.target,)
            if isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
                assigned_value = node.value
        elif isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
            targets = (node.target,)
        elif isinstance(node, ast.withitem) and node.optional_vars is not None:
            targets = (node.optional_vars,)
        elif isinstance(node, ast.Delete):
            targets = tuple(node.targets)
        elif isinstance(node, ast.ExceptHandler) and node.name in protected:
            _reject(code, path, f"protected binding rewrite: {node.name}")
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            bound = {
                alias.asname or alias.name.split(".", maxsplit=1)[0]
                for alias in node.names
            }
            overlap = sorted(bound & protected)
            if overlap:
                _reject(code, path, f"protected import binding: {overlap[0]}")
        if any(_target_rewrites_binding(target, protected) for target in targets):
            _reject(code, path, "protected binding assignment or deletion")
        if (
            assigned_value is not None
            and _binding_root_name(assigned_value) in protected
        ):
            _reject(code, path, "protected binding alias")
        if not isinstance(node, ast.Call) or not node.args:
            continue
        mutator = None
        if isinstance(node.func, ast.Name):
            mutator = node.func.id
        elif isinstance(node.func, ast.Attribute):
            mutator = node.func.attr
        if mutator in {"exec", "eval"}:
            _reject(code, path, f"dynamic binding mutator: {mutator}")
        if mutator in {"setattr", "delattr", "__setattr__", "__delattr__"}:
            referenced_names = {
                child.id
                for child in ast.walk(node.args[0])
                if isinstance(child, ast.Name)
            }
            if referenced_names & protected:
                _reject(code, path, f"protected binding mutator: {mutator}")


def _literal_assignment(tree: ast.Module, name: str, path: str) -> object:
    values: list[ast.expr] = []
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name) and target.id == name for target in node.targets):
            values.append(node.value)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.target.id == name:
            if node.value is None:
                _reject("ASSIGNMENT_LITERAL", path, f"{name}:missing value")
            values.append(node.value)
    if len(values) != 1:
        _reject("ASSIGNMENT_CARDINALITY", path, name)
    try:
        value = values[0]
        if (
            isinstance(value, ast.Call)
            and isinstance(value.func, ast.Name)
            and value.func.id == "frozenset"
            and len(value.args) == 1
            and not value.keywords
        ):
            return frozenset(ast.literal_eval(value.args[0]))
        return ast.literal_eval(values[0])
    except (MemoryError, RecursionError, SyntaxError, ValueError) as exc:
        _reject("ASSIGNMENT_LITERAL", path, f"{name}:{type(exc).__name__}")


def _string_collection_assignment(
    tree: ast.Module,
    name: str,
    path: str,
) -> tuple[str, ...]:
    value = _literal_assignment(tree, name, path)
    if type(value) not in {list, tuple, frozenset}:
        _reject("ASSIGNMENT_LITERAL", path, f"{name}:requires string collection")
    collection = cast(Iterable[object], value)
    if any(type(item) is not str for item in collection):
        _reject("ASSIGNMENT_LITERAL", path, f"{name}:requires exact strings")
    return tuple(cast(Iterable[str], value))


def _require_markers(
    source: Mapping[str, bytes],
    path: str,
    code: str,
    *,
    present: tuple[bytes, ...] = (),
    absent: tuple[bytes, ...] = (),
) -> None:
    raw = source[path]
    for marker in present:
        if marker not in raw:
            _reject(code, path, f"missing {marker.decode('utf-8', 'replace')}")
    for marker in absent:
        if marker in raw:
            _reject(code, path, f"forbidden {marker.decode('utf-8', 'replace')}")


def _first_executable_statement(node: ast.FunctionDef | ast.AsyncFunctionDef) -> ast.stmt | None:
    body = list(node.body)
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and type(body[0].value.value) is str:
        body.pop(0)
    return body[0] if body else None


def _is_call_to(statement: ast.stmt | None, name: str) -> bool:
    call: ast.Call | None = None
    if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Call):
        call = statement.value
    elif isinstance(statement, ast.Return) and isinstance(statement.value, ast.Call):
        call = statement.value
    return call is not None and isinstance(call.func, ast.Name) and call.func.id == name


def _is_raise_call_to(statement: ast.stmt | None, name: str) -> bool:
    return (
        isinstance(statement, ast.Raise)
        and isinstance(statement.exc, ast.Call)
        and isinstance(statement.exc.func, ast.Name)
        and statement.exc.func.id == name
    )


def _ast_shape(node: ast.AST | None) -> str:
    return "" if node is None else ast.dump(node, include_attributes=False)


def _expected_if_test(source: str) -> ast.expr:
    parsed = ast.parse(f"if {source}:\n    pass\n")
    statement = parsed.body[0]
    if not isinstance(statement, ast.If):
        _reject("CHECKER_INTERNAL_SHAPE", "AST", "expected if statement")
    return statement.test


def _is_exact_call_statement(
    statement: ast.stmt | None,
    *,
    name: str,
    argument: str,
) -> bool:
    return bool(
        isinstance(statement, ast.Expr)
        and isinstance(statement.value, ast.Call)
        and isinstance(statement.value.func, ast.Name)
        and statement.value.func.id == name
        and len(statement.value.args) == 1
        and isinstance(statement.value.args[0], ast.Constant)
        and statement.value.args[0].value == argument
        and not statement.value.keywords
    )


def _operation_maps() -> tuple[dict[str, tuple[str, ...]], dict[str, tuple[str, ...]]]:
    current: dict[str, tuple[str, ...]] = dict(CURRENT_PATH_OPERATIONS_V3)
    research: dict[str, tuple[str, ...]] = dict(RESEARCH_PATH_OPERATIONS_V3)
    if len(current) != len(CURRENT_PATH_OPERATIONS_V3) or len(research) != len(RESEARCH_PATH_OPERATIONS_V3):
        _reject("OPERATION_REGISTRY_DUPLICATE", "operation registry", "duplicate path")
    if set(current) & set(research):
        _reject("ORACLE_AUTHORITY", "operation registry", "path appears in both lanes")
    if set(current) | set(research) != set(DIRECT_CONSUMER_PATHS_V3):
        _reject("OPERATION_REGISTRY_SCOPE", "operation registry", "36-path coverage drift")
    if tuple(sorted(set(CURRENT_OPERATION_IDS_V3))) != CURRENT_OPERATION_IDS_V3:
        _reject("OPERATION_REGISTRY_ORDER", "current", "operation ids are not exact")
    if tuple(sorted(set(RESEARCH_OPERATION_IDS_V3))) != RESEARCH_OPERATION_IDS_V3:
        _reject("OPERATION_REGISTRY_ORDER", "research", "operation ids are not exact")
    if set(CURRENT_OPERATION_IDS_V3) & set(RESEARCH_OPERATION_IDS_V3):
        _reject("ORACLE_AUTHORITY", "operation registry", "operation id lane overlap")
    return current, research


def _require_plan_and_current_tau(source: Mapping[str, bytes]) -> None:
    if _sha256(source[PLAN_PATH_V3]) != PLAN_SHA256_V3:
        _reject("PLAN_SHA256", PLAN_PATH_V3, "admitted plan bytes drift")
    plan = _decode_json_object(source[PLAN_PATH_V3], PLAN_PATH_V3)
    obligations = plan.get("next_obligations")
    gaps = plan.get("gap_registry")
    gates = plan.get("value_movement_gates")
    if type(obligations) is not list or type(gaps) is not list or type(gates) is not list:
        _reject("PLAN_SHAPE", PLAN_PATH_V3, "required registries missing")
    rows = [
        row
        for row in obligations
        if type(row) is dict and row.get("obligation_id") == "O-003B"
    ]
    expected_evidence = [
        "operation-derived dependency rows",
        "QUARANTINED or RESEARCH_ORACLE or REMOVED classification",
        "new bridge import mutation killer",
        "startup refusal for retired bridge modes",
    ]
    if len(rows) != 1 or rows[0].get("required_evidence") != expected_evidence:
        _reject("PLAN_O003B", PLAN_PATH_V3, "O-003B contract drift")
    expected_gaps = {
        ("stale_tau_assurance", "O-003B", "OPEN"),
        ("retired_bridge_dependency_inventory_gap", "O-003B", "OPEN"),
    }
    observed_gaps = {
        (row.get("gap_id"), row.get("owner_obligation"), row.get("status"))
        for row in gaps
        if type(row) is dict and row.get("owner_obligation") == "O-003B"
    }
    if observed_gaps != expected_gaps:
        _reject("PLAN_GAPS", PLAN_PATH_V3, "O-003B baseline gap set drift")
    if len(gates) != 12:
        _reject("PLAN_VM_GATES", PLAN_PATH_V3, "expected 12 unpromoted gates")

    if _sha256(source[CURRENT_TAU_PATH_V3]) != CURRENT_TAU_SHA256_V3:
        _reject("CURRENT_TAU_SHA256", CURRENT_TAU_PATH_V3, "O-003A oracle drift")
    current_tau = _decode_json_object(source[CURRENT_TAU_PATH_V3], CURRENT_TAU_PATH_V3)
    disposition = current_tau.get("route_disposition")
    authority = current_tau.get("authority")
    vm_ledger = current_tau.get("vm_ledger_contribution")
    if (
        current_tau.get("status") != "BLOCKED_EXTERNAL_REPLAY_TRUST_ROOT"
        or type(disposition) is not dict
        or disposition.get("current_tau_compatible") is not False
        or type(authority) is not dict
        or set(authority.values()) != {"NONE"}
        or type(vm_ledger) is not dict
        or vm_ledger.get("vm_gates_closed") != []
    ):
        _reject("CURRENT_TAU_WITNESS", CURRENT_TAU_PATH_V3, "research oracle posture drift")


def _require_removed_marker(
    baseline: Mapping[str, SourceFileV3],
    subject: Mapping[str, SourceFileV3],
    *,
    path: str,
    marker: bytes,
    code: str,
) -> None:
    if marker not in baseline[path].data or marker in subject[path].data:
        _reject(code, path, marker.decode("utf-8", "replace"))


def _require_function_guard(
    source: Mapping[str, bytes],
    *,
    path: str,
    function_name: str,
    guard_name: str,
    code: str,
) -> None:
    tree = _parse_python(source, path)
    _require_no_binding_rewrites(
        tree,
        path=path,
        code=code,
        names=(function_name,),
    )
    node = _unique_top_level_function(tree, function_name)
    if (
        type(node) is not ast.FunctionDef
        or node.decorator_list
        or not _is_call_to(_first_executable_statement(node), guard_name)
    ):
        _reject(code, path, function_name)


def _require_route_witnesses(
    baseline: Mapping[str, SourceFileV3],
    subject: Mapping[str, SourceFileV3],
) -> None:
    current = {path: item.data for path, item in subject.items()}
    quarantine_path = "src/integration/local_route_quarantine.py"
    quarantine_tree = _parse_python(current, quarantine_path)
    if _string_collection_assignment(quarantine_tree, "QUARANTINED_ROUTE_ENVIRONMENT_V1", quarantine_path) != _PRIMARY_ROUTE_ENV_V3:
        _reject("ROUTE_ENVIRONMENT", quarantine_path, "primary route registry drift")
    if _string_collection_assignment(quarantine_tree, "QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1", quarantine_path) != _ROUTE_ENV_ALIASES_V3:
        _reject("ROUTE_ALIASES", quarantine_path, "alias registry drift")
    if frozenset(_string_collection_assignment(quarantine_tree, "QUARANTINED_ROUTE_ALLOWED_VALUES_V1", quarantine_path)) != frozenset({"false", "0"}):
        _reject("ROUTE_ALLOWED_VALUES", quarantine_path, "exact disabled encodings drift")

    _require_markers(
        current,
        "src/integration/api_server.py",
        "API_AUTOTRADER_STARTUP_REFUSAL",
        present=(
            b"if config.autotrader_live_enabled:",
            b"AUTOTRADER_LIVE_API_ENABLED is unavailable",
            b"httpd.autotrader_live_api_enabled = False",
        ),
        absent=(
            b"from src.integration.perps_wallet_api import handle_perps_wallet_request",
            b"from src.integration.zusd_tau_wallet_api import handle_zusd_tau_wallet_request",
            b"from src.integration.zusd_monetary_wallet_api import handle_zusd_monetary_wallet_request",
            b"from src.integration.autotrader_live_api import handle_autotrader_live_request",
        ),
    )
    api_tree = _parse_python(current, "src/integration/api_server.py")
    _require_no_binding_rewrites(
        api_tree,
        path="src/integration/api_server.py",
        code="API_AUTOTRADER_ATTACHMENT_GUARD",
        names=("_attach_api_server_state", "_api_startup_refusal_lines"),
    )
    attach = _unique_top_level_function(api_tree, "_attach_api_server_state")
    first_attach_statement = (
        None if attach is None else _first_executable_statement(attach)
    )
    expected_attach_test = _expected_if_test(
        "type(config) is not ApiServerConfig or any("
        "value is not False for value in ("
        "config.perps_wallet_enabled, config.zusd_tau_wallet_enabled, "
        "config.zusd_monetary_wallet_enabled, config.autotrader_live_enabled, "
        "config.confidential_sealed_bid_asset_settlement_enabled))"
    )
    exact_attach_condition = bool(
        isinstance(first_attach_statement, ast.If)
        and _ast_shape(first_attach_statement.test)
        == _ast_shape(expected_attach_test)
    )
    exact_attach_refusal = bool(
        isinstance(first_attach_statement, ast.If)
        and len(first_attach_statement.body) == 1
        and _is_exact_call_statement(
            first_attach_statement.body[0],
            name="refuse_current_local_operator_operation_v1",
            argument="api_server_state_attachment",
        )
    )
    if not (
        type(attach) is ast.FunctionDef
        and not attach.decorator_list
        and exact_attach_condition
        and exact_attach_refusal
    ):
        _reject(
            "API_AUTOTRADER_ATTACHMENT_GUARD",
            "src/integration/api_server.py",
            "direct state attachment must refuse before mutation",
        )
    startup_refusal = _unique_top_level_function(
        api_tree,
        "_api_startup_refusal_lines",
    )
    startup_body = [] if startup_refusal is None else list(startup_refusal.body)
    expected_startup_branches = (
        (1, "autotrader_live_enabled", "AUTOTRADER_LIVE_API_ENABLED"),
        (2, "zusd_tau_wallet_enabled", "ZUSD_TAU_WALLET_API_ENABLED"),
        (3, "perps_wallet_enabled", "PERPS_WALLET_API_ENABLED"),
        (
            4,
            "zusd_monetary_wallet_enabled",
            "ZUSD_MONETARY_WALLET_API_ENABLED",
        ),
    )
    if type(startup_refusal) is not ast.FunctionDef or startup_refusal.decorator_list:
        _reject(
            "API_AUTOTRADER_STARTUP_REFUSAL",
            "src/integration/api_server.py",
            "startup refusal must be one plain top-level function",
        )
    for index, attribute, message_marker in expected_startup_branches:
        branch = startup_body[index] if len(startup_body) > index else None
        expected_test = _expected_if_test(f"config.{attribute}")
        returned = (
            branch.body[0]
            if isinstance(branch, ast.If) and len(branch.body) == 1
            else None
        )
        return_value = returned.value if isinstance(returned, ast.Return) else None
        returned_strings = (
            tuple(
                item.value
                for item in return_value.elts
                if isinstance(item, ast.Constant) and type(item.value) is str
            )
            if isinstance(return_value, ast.List)
            else ()
        )
        if (
            not isinstance(branch, ast.If)
            or _ast_shape(branch.test) != _ast_shape(expected_test)
            or not returned_strings
            or not any(message_marker in value for value in returned_strings)
        ):
            _reject(
                "API_AUTOTRADER_STARTUP_REFUSAL",
                "src/integration/api_server.py",
                f"exact startup refusal branch drift: {attribute}",
            )
    startup_test = "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py"
    _require_markers(
        current,
        startup_test,
        "STARTUP_REFUSAL_EVIDENCE",
        present=(
            b"test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect",
            b"test_given_retired_route_alias_when_starting_then_exact_reject_precedes_config",
            b"test_given_allowed_retired_route_encoding_when_starting_then_reaches_server_path",
            b"test_given_direct_retired_tau_signing_call_then_typed_reject_precedes_vault_access",
            b"test_given_retired_stream_when_follower_http_ingress_receives_it_then_reject_precedes_forwarding",
        ),
    )

    for path in ("docker-compose.local-testnet.yml", "docker-compose.permissionless.yml"):
        _require_removed_marker(
            baseline,
            subject,
            path=path,
            marker=b"tau-local:",
            code="COMPOSE_TAU_SERVICE_REMOVAL",
        )
        _require_markers(
            current,
            path,
            "COMPOSE_TAU_SERVICE_REMOVAL",
            absent=(b"run_local_tau_node_container.sh",),
        )

    _require_removed_marker(
        baseline,
        subject,
        path="src/integration/confidential_sealed_bid_api.py",
        marker=b"def submit_confidential_sealed_bid_local_ledger_settlement(",
        code="CONFIDENTIAL_TAU_CALLBACK_REMOVAL",
    )
    _require_removed_marker(
        baseline,
        subject,
        path="tools/zeno_ledger_make_core_feature_suite.py",
        marker=b"tau_app_bridge_spot",
        code="CORE_FEATURE_TAU_LANE_REMOVAL",
    )
    _require_removed_marker(
        baseline,
        subject,
        path="tools/zenoctl_testnet_local/nginx.py",
        marker=b"sign-tau-transaction-payload",
        code="NGINX_SIGNER_ROUTE_REMOVAL",
    )
    _require_removed_marker(
        baseline,
        subject,
        path="tools/build_app_root_jmt_evidence.py",
        marker=b"tau_app_state_wrapper_live_root",
        code="APP_ROOT_HISTORICAL_MODE_REMOVAL",
    )

    _require_markers(
        current,
        "tools/zeno_ledger_run_local.py",
        "LOCAL_BLOCK_SELECTOR_GUARD",
        present=(
            b"raise ValueError(RETIRED_TAU_APP_STATE_SELECTOR_ERROR)",
            b"raise ValueError(RETIRED_TAU_BRIDGE_COMPANION_SELECTOR_ERROR)",
        ),
        absent=(b"def _execute_tau_app_body_v0(",),
    )
    _require_markers(
        current,
        "tools/zeno_ledger_make_feature_lane.py",
        "FEATURE_LANE_SELECTOR_GUARD",
        present=(
            b"raise ValueError(RETIRED_TAU_APP_STATE_SELECTOR_ERROR)",
            b"raise ValueError(RETIRED_TAU_BRIDGE_COMPANION_SELECTOR_ERROR)",
        ),
        absent=(b'"execution_mode": "tau_app"',),
    )
    _require_markers(
        current,
        "tools/zeno_ledger_run_manifest.py",
        "MANIFEST_SELECTOR_GUARD",
        present=(b"RETIRED_TAU_BRIDGE_EXECUTABLES", b"RETIRED_TAU_BRIDGE_SELECTORS"),
        absent=(b'"--tau-" in item', b'"--clock-policy" in item'),
    )
    _require_markers(
        current,
        "tools/zeno_ledger_node.py",
        "NODE_RETIRED_STATE_GUARD",
        present=(
            b"_require_current_node_state_obj_v0",
            b"_require_no_retired_tau_operations_v0(tx)",
            b"_require_no_retired_tau_body_operations_v0(peer_body)",
        ),
    )
    _require_markers(
        current,
        "tools/generate_operator_systemd.py",
        "OPERATOR_LOCAL_NODE_GUARD",
        present=(b"RETIRED_LOCAL_NODE_REFUSAL", b"if local_node:"),
    )
    _require_markers(
        current,
        "tools/permissionless_operator_preflight.py",
        "OPERATOR_LOCAL_NODE_GUARD",
        present=(b'"id": "retired_tau_local_node"', b'"ok": False'),
    )
    _require_markers(
        current,
        "tools/check_container_hardening.py",
        "OPERATOR_LOCAL_NODE_GUARD",
        present=(b"retired Tau local-node service must remain absent",),
    )

    signer_path = "src/integration/zenodex_local_signer.py"
    signer_tree = _parse_python(current, signer_path)
    _require_no_binding_rewrites(
        signer_tree,
        path=signer_path,
        code="LOCAL_SIGNER_RETIREMENT_GUARD",
        names=("LocalSignerVault",),
    )
    signer_class = _unique_top_level_class(signer_tree, "LocalSignerVault")
    signer_method = None
    if signer_class is not None:
        signer_method = _unique_direct_method(
            signer_class,
            "sign_tau_transaction_payload",
        )
    if (
        type(signer_method) is not ast.FunctionDef
        or signer_method.decorator_list
        or not _is_raise_call_to(
            _first_executable_statement(signer_method),
            "RetiredTauTransactionSigningRouteError",
        )
    ):
        _reject("LOCAL_SIGNER_RETIREMENT_GUARD", signer_path, "direct vault method")
    _require_markers(
        current,
        "tools/zenodex_local_signer.py",
        "LOCAL_SIGNER_RETIREMENT_GUARD",
        present=(
            b"raise ValueError(RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR)",
            b'if urlsplit(self.path).path == "/sign-tau-transaction-payload":',
        ),
    )
    http_signer_path = "tools/zenodex_local_signer.py"
    http_signer_tree = _parse_python(current, http_signer_path)
    _require_no_binding_rewrites(
        http_signer_tree,
        path=http_signer_path,
        code="LOCAL_SIGNER_RETIREMENT_GUARD",
        names=("_LocalSignerHttpHandler", "cmd_sign_tau_transaction_payload"),
    )
    cli_method = _unique_top_level_function(
        http_signer_tree,
        "cmd_sign_tau_transaction_payload",
    )
    expected_cli_method = cast(
        ast.FunctionDef,
        ast.parse(
            "def cmd_sign_tau_transaction_payload(args: argparse.Namespace) -> int:\n    pass\n"
        ).body[0],
    )
    cli_first = (
        None if cli_method is None else _first_executable_statement(cli_method)
    )
    cli_raise = cli_first.exc if isinstance(cli_first, ast.Raise) else None
    cli_callable_ok = bool(
        type(cli_method) is ast.FunctionDef
        and not cli_method.decorator_list
        and ast.dump(cli_method.args, include_attributes=False)
        == ast.dump(expected_cli_method.args, include_attributes=False)
        and isinstance(cli_method.returns, ast.expr)
        and isinstance(expected_cli_method.returns, ast.expr)
        and ast.dump(cli_method.returns, include_attributes=False)
        == ast.dump(expected_cli_method.returns, include_attributes=False)
    )
    cli_guard_ok = bool(
        cli_callable_ok
        and isinstance(cli_raise, ast.Call)
        and isinstance(cli_raise.func, ast.Name)
        and cli_raise.func.id == "ValueError"
        and len(cli_raise.args) == 1
        and isinstance(cli_raise.args[0], ast.Name)
        and cli_raise.args[0].id == "RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR"
        and not cli_raise.keywords
    )
    if not cli_guard_ok:
        _reject(
            "LOCAL_SIGNER_RETIREMENT_GUARD",
            http_signer_path,
            "CLI route must reject before argument or vault access",
        )
    handler_class = _unique_top_level_class(
        http_signer_tree,
        "_LocalSignerHttpHandler",
    )
    handler_class_ok = bool(
        type(handler_class) is ast.ClassDef
        and not handler_class.decorator_list
        and not handler_class.keywords
        and len(handler_class.bases) == 1
        and isinstance(handler_class.bases[0], ast.Name)
        and handler_class.bases[0].id == "BaseHTTPRequestHandler"
    )
    post_method = (
        None
        if handler_class is None
        else _unique_direct_method(handler_class, "do_POST")
    )
    expected_post_method = cast(
        ast.FunctionDef,
        ast.parse("def do_POST(self) -> None:\n    pass\n").body[0],
    )
    post_callable_ok = bool(
        type(post_method) is ast.FunctionDef
        and not post_method.decorator_list
        and ast.dump(post_method.args, include_attributes=False)
        == ast.dump(expected_post_method.args, include_attributes=False)
        and isinstance(post_method.returns, ast.expr)
        and isinstance(expected_post_method.returns, ast.expr)
        and ast.dump(post_method.returns, include_attributes=False)
        == ast.dump(expected_post_method.returns, include_attributes=False)
    )
    post_body = [] if post_method is None else list(post_method.body)
    if (
        post_body
        and isinstance(post_body[0], ast.Expr)
        and isinstance(post_body[0].value, ast.Constant)
        and type(post_body[0].value.value) is str
    ):
        post_body.pop(0)
    origin_guard = post_body[0] if len(post_body) >= 1 else None
    retired_guard = post_body[1] if len(post_body) >= 2 else None
    origin_test = origin_guard.test if isinstance(origin_guard, ast.If) else None
    expected_origin_test = ast.parse(
        "self._reject_disallowed_origin(require_origin=True)",
        mode="eval",
    ).body
    origin_ok = bool(
        isinstance(origin_guard, ast.If)
        and isinstance(origin_test, ast.Call)
        and ast.dump(origin_test, include_attributes=False)
        == ast.dump(expected_origin_test, include_attributes=False)
        and len(origin_guard.body) == 1
        and isinstance(origin_guard.body[0], ast.Return)
        and origin_guard.body[0].value is None
        and not origin_guard.orelse
    )
    retired_test = retired_guard.test if isinstance(retired_guard, ast.If) else None
    expected_retired_test = ast.parse(
        'urlsplit(self.path).path == "/sign-tau-transaction-payload"',
        mode="eval",
    ).body
    retired_path_ok = bool(
        isinstance(retired_test, ast.Compare)
        and ast.dump(retired_test, include_attributes=False)
        == ast.dump(expected_retired_test, include_attributes=False)
    )
    retired_body = list(retired_guard.body) if isinstance(retired_guard, ast.If) else []
    write_statement = retired_body[0] if retired_body else None
    write_call = (
        write_statement.value
        if isinstance(write_statement, ast.Expr)
        and isinstance(write_statement.value, ast.Call)
        else None
    )
    expected_payload = ast.parse(
        '{"ok": False, "error": RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR}',
        mode="eval",
    ).body
    write_410_ok = bool(
        isinstance(write_call, ast.Call)
        and isinstance(write_call.func, ast.Attribute)
        and isinstance(write_call.func.value, ast.Name)
        and write_call.func.value.id == "self"
        and write_call.func.attr == "_write_json"
        and len(write_call.args) == 2
        and not write_call.keywords
        and isinstance(write_call.args[0], ast.Constant)
        and write_call.args[0].value == 410
        and ast.dump(write_call.args[1], include_attributes=False)
        == ast.dump(expected_payload, include_attributes=False)
    )
    return_ok = bool(
        isinstance(retired_guard, ast.If)
        and len(retired_body) == 2
        and isinstance(retired_body[1], ast.Return)
        and retired_body[1].value is None
        and not retired_guard.orelse
    )
    if not (
        handler_class_ok
        and post_callable_ok
        and origin_ok
        and retired_path_ok
        and write_410_ok
        and return_ok
    ):
        _reject(
            "LOCAL_SIGNER_RETIREMENT_GUARD",
            http_signer_path,
            "HTTP route must return exact 410 before body or signer access",
        )

    lifecycle_path = "tools/zenoctl_testnet_local/lifecycle.py"
    for current_name, donor_name in _LIFECYCLE_DONOR_PAIRS_V3:
        _require_function_guard(
            current,
            path=lifecycle_path,
            function_name=current_name,
            guard_name="refuse_current_local_operator_operation_v1",
            code="LIFECYCLE_DONOR_GUARD",
        )
        _require_function_guard(
            current,
            path=lifecycle_path,
            function_name=donor_name,
            guard_name="refuse_current_local_operator_operation_v1",
            code="LIFECYCLE_DONOR_GUARD",
        )

    _require_markers(
        current,
        "src/integration/production_promotion_evidence.py",
        "APP_ROOT_PROMOTION_GUARD",
        present=(b"unsupported app-root live-root mode",),
    )
    _require_markers(
        current,
        "tests/integration/test_app_root_jmt_promotion_lane.py",
        "APP_ROOT_PROMOTION_GUARD",
        present=(b"test_lane_evaluator_rejects_self_consistent_historical_tau_wrapper_mode",),
    )
    _require_removed_marker(
        baseline,
        subject,
        path="tools/check_production_boundary.py",
        marker=b"tau_testnet_dex_plugin_enters_through_dex_engine",
        code="PRODUCTION_BOUNDARY_NONAUTHORITY",
    )
    _require_markers(
        current,
        "tools/check_production_boundary.py",
        "PRODUCTION_BOUNDARY_NONAUTHORITY",
        present=(b"retired_tau_bridge_classified_without_production_authority",),
    )


def _source_pin(item: SourceFileV3) -> dict[str, object]:
    return {
        "git_blob_sha": item.git_blob_sha,
        "sha256": _sha256(item.data),
        "size": len(item.data),
    }


def _dependency_row(
    *,
    dependency_id: str,
    classification: str,
    source_path: str,
    scope: str,
    symbol: str,
    dependency_kind: str,
    target: str,
    bound_name: str,
    baseline_occurrences: int,
    current_occurrences: int,
    baseline_operation_ids: tuple[str, ...],
    current_operation_ids: tuple[str, ...],
    research_operation_ids: tuple[str, ...],
    quarantine_evidence_ids: tuple[str, ...],
    reason: str,
    baseline: Mapping[str, SourceFileV3],
    subject: Mapping[str, SourceFileV3],
) -> dict[str, object]:
    return {
        "baseline_occurrences": baseline_occurrences,
        "baseline_operation_ids": sorted(baseline_operation_ids),
        "baseline_source": _source_pin(baseline[source_path]),
        "bound_name": bound_name,
        "classification": classification,
        "current_occurrences": current_occurrences,
        "current_operation_ids": sorted(current_operation_ids),
        "current_source": _source_pin(subject[source_path]),
        "dependency_id": dependency_id,
        "dependency_kind": dependency_kind,
        "quarantine_evidence_ids": sorted(quarantine_evidence_ids),
        "reason": reason,
        "research_operation_ids": sorted(research_operation_ids),
        "scope": scope,
        "source_path": source_path,
        "symbol": symbol,
        "target": target,
    }


_GENERIC_SIGNING_MEMBERS_V3: Final = frozenset(
    {
        "_parse_privkey_to_int",
        "bls_pubkey_hex_from_privkey",
        "encode_tau_operations_for_wire",
        "sign_dex_intent_for_engine",
        "sign_perp_op_for_engine",
        "sign_tau_transaction_payload",
        "verify_tau_transaction_payload_signature",
    }
)


def _current_operations_for_edge(
    edge: ImportEdgeV3,
    current_by_path: Mapping[str, tuple[str, ...]],
) -> tuple[str, ...]:
    operation_ids = set(current_by_path[edge.source_path])
    if (
        edge.target_module == "src.integration.tau_net_client"
        and edge.imported_member in _GENERIC_SIGNING_MEMBERS_V3
    ):
        operation_ids.add("NEUTRAL_SIGNING_CONSUMERS")
    if (
        edge.target_module == "src.integration.zusd_tau_token"
        and edge.imported_member == "derive_zusd_tau_asset_id"
    ):
        operation_ids.add("NEUTRAL_ASSET_ID_CONSUMERS")
    return tuple(sorted(operation_ids))


def _import_dependency_rows(
    baseline: Mapping[str, SourceFileV3],
    subject: Mapping[str, SourceFileV3],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    baseline_source = {path: baseline[path].data for path in DIRECT_CONSUMER_PATHS_V3}
    current_source = {path: subject[path].data for path in DIRECT_CONSUMER_PATHS_V3}
    baseline_edges = scan_bridge_import_edges_v3(baseline_source)
    current_edges = scan_bridge_import_edges_v3(current_source)
    baseline_counts = Counter(baseline_edges)
    current_counts = Counter(current_edges)
    current_only = sorted(set(current_counts) - set(baseline_counts))
    if current_only:
        edge = current_only[0]
        _reject(
            "UNCLASSIFIED_RETIRED_TAU_BRIDGE_IMPORT",
            edge.source_path,
            f"{edge.scope}:{edge.dependency_kind}:{edge.target()}:{edge.bound_name}",
        )
    baseline_root = _manifest_root(_edge_manifest(baseline_edges))
    current_root = _manifest_root(_edge_manifest(current_edges))
    if len(baseline_edges) != EXPECTED_BASELINE_EDGE_COUNT_V3 or baseline_root != EXPECTED_BASELINE_EDGE_ROOT_V3:
        _reject("BASELINE_EDGE_SET", "import projection", f"count={len(baseline_edges)} root={baseline_root}")
    if len(current_edges) != EXPECTED_CURRENT_EDGE_COUNT_V3 or current_root != EXPECTED_CURRENT_EDGE_ROOT_V3:
        _reject("CURRENT_EDGE_SET", "import projection", f"count={len(current_edges)} root={current_root}")
    unchanged = set(baseline_counts) & set(current_counts)
    removed = set(baseline_counts) - set(current_counts)
    if (
        len(unchanged) != EXPECTED_UNCHANGED_EDGE_COUNT_V3
        or len(removed) != EXPECTED_REMOVED_EDGE_COUNT_V3
        or len(current_only) != EXPECTED_CURRENT_ONLY_EDGE_COUNT_V3
    ):
        _reject("EDGE_PARTITION", "import projection", "128-to-92 partition drift")

    current_by_path, research_by_path = _operation_maps()
    rows: list[dict[str, object]] = []
    for edge in sorted(set(baseline_counts)):
        baseline_occurrences = baseline_counts[edge]
        current_occurrences = current_counts[edge]
        if current_occurrences:
            if edge.source_path in research_by_path:
                classification = "RESEARCH_ORACLE"
                baseline_operation_ids: tuple[str, ...] = ()
                current_operation_ids: tuple[str, ...] = ()
                research_operation_ids = research_by_path[edge.source_path]
                evidence_ids: tuple[str, ...] = ()
                reason = "retained only inside the declared historical research-oracle source"
            else:
                _reject(
                    "UNCLASSIFIED_RETIRED_TAU_BRIDGE_IMPORT",
                    edge.source_path,
                    f"{edge.scope}:{edge.dependency_kind}:{edge.target()}:{edge.bound_name}",
                )
        else:
            if edge.source_path not in current_by_path:
                _reject("REMOVED_RESEARCH_EDGE", edge.source_path, edge.target())
            classification = "REMOVED"
            baseline_operation_ids = current_by_path[edge.source_path]
            current_operation_ids = _current_operations_for_edge(edge, current_by_path)
            research_operation_ids = ()
            evidence_ids = ()
            reason = "baseline import edge is absent from the exact current source projection"
        edge_id = _sha256(canonical_json_bytes_v3(edge.to_hash_row()))[:32]
        rows.append(
            _dependency_row(
                dependency_id=f"python-import:{edge_id}",
                classification=classification,
                source_path=edge.source_path,
                scope=edge.scope,
                symbol=f"{edge.target()} as {edge.bound_name}",
                dependency_kind=edge.dependency_kind,
                target=edge.target(),
                bound_name=edge.bound_name,
                baseline_occurrences=baseline_occurrences,
                current_occurrences=current_occurrences,
                baseline_operation_ids=baseline_operation_ids,
                current_operation_ids=current_operation_ids,
                research_operation_ids=research_operation_ids,
                quarantine_evidence_ids=evidence_ids,
                reason=reason,
                baseline=baseline,
                subject=subject,
            )
        )
    projection = {
        "baseline_edge_count": len(baseline_edges),
        "baseline_edge_root_sha256": baseline_root,
        "current_edge_count": len(current_edges),
        "current_edge_root_sha256": current_root,
        "current_only_edge_count": len(current_only),
        "removed_edge_count": len(removed),
        "unchanged_edge_count": len(unchanged),
    }
    return rows, projection


def _manual_dependency_rows(
    baseline: Mapping[str, SourceFileV3],
    subject: Mapping[str, SourceFileV3],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []

    def add(
        dependency_id: str,
        classification: str,
        path: str,
        symbol: str,
        dependency_kind: str,
        *,
        marker: bytes,
        current_operation_ids: tuple[str, ...] = (),
        research_operation_ids: tuple[str, ...] = (),
        evidence_ids: tuple[str, ...] = (),
        reason: str,
    ) -> None:
        rows.append(
            _dependency_row(
                dependency_id=dependency_id,
                classification=classification,
                source_path=path,
                scope="<module>",
                symbol=symbol,
                dependency_kind=dependency_kind,
                target=symbol,
                bound_name=symbol,
                baseline_occurrences=baseline[path].data.count(marker),
                current_occurrences=subject[path].data.count(marker),
                baseline_operation_ids=current_operation_ids,
                current_operation_ids=current_operation_ids,
                research_operation_ids=research_operation_ids,
                quarantine_evidence_ids=evidence_ids,
                reason=reason,
                baseline=baseline,
                subject=subject,
            )
        )

    primary_evidence = (
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect",
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_allowed_retired_route_encoding_when_starting_then_reaches_server_path",
    )
    for variable in _PRIMARY_ROUTE_ENV_V3:
        add(
            f"route-env:{variable}",
            "QUARANTINED",
            "src/integration/local_route_quarantine.py",
            variable,
            "STARTUP_ENVIRONMENT_SELECTOR",
            marker=variable.encode("ascii"),
            current_operation_ids=(
                "API_SERVER_STARTUP",
                "LOCAL_OPERATOR_PROFILE",
                "LOCAL_RUNTIME_CONFIG",
            ),
            evidence_ids=primary_evidence,
            reason="only absent, exact false, or exact 0 reaches server construction",
        )
    alias_evidence = (
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_retired_route_alias_when_starting_then_exact_reject_precedes_config",
    )
    for alias in _ROUTE_ENV_ALIASES_V3:
        add(
            f"route-env-alias:{alias}",
            "QUARANTINED",
            "src/integration/local_route_quarantine.py",
            alias,
            "STARTUP_ENVIRONMENT_ALIAS",
            marker=alias.encode("ascii"),
            current_operation_ids=("API_SERVER_STARTUP", "LOCAL_RUNTIME_CONFIG"),
            evidence_ids=alias_evidence,
            reason="every historical spelling is rejected before configuration or effects",
        )
    add(
        "route-profile:current-local-operator",
        "QUARANTINED",
        "src/integration/local_route_quarantine.py",
        "CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1",
        "LOCAL_OPERATOR_PROFILE",
        marker=b"local-testnet-retired-bridge-quarantine-v2",
        current_operation_ids=("LOCAL_OPERATOR_PROFILE", "LOCAL_RUNTIME_CONFIG"),
        evidence_ids=primary_evidence,
        reason="current local profile carries no release authority and keeps retired routes disabled",
    )

    for path in ("docker-compose.local-testnet.yml", "docker-compose.permissionless.yml"):
        add(
            f"compose-service-removed:{path}:tau-local",
            "REMOVED",
            path,
            "tau-local",
            "COMPOSE_SERVICE",
            marker=b"tau-local:",
            current_operation_ids=("LOCAL_OPERATOR_STARTUP",),
            reason="historical Tau local-node service is absent from the current Compose profile",
        )
    add(
        "manifest-v4-retired-tau-keys",
        "QUARANTINED",
        "tools/zenoctl_testnet_local/manifest.py",
        "LEGACY_RETIRED_TAU_SERVICE_KEYS/LEGACY_RETIRED_TAU_IMAGE_KEYS",
        "LOCAL_MANIFEST_SELECTOR",
        marker=b"LEGACY_RETIRED_TAU_SERVICE_KEYS",
        current_operation_ids=("LOCAL_MANIFEST_BUILD", "LOCAL_OPERATOR_STARTUP"),
        evidence_ids=(
            "tests/integration/test_zenoctl_testnet_local.py::test_manifest_mountable_lane_registry_excludes_retired_tau_routes",
        ),
        reason="V4 manifests reject reintroduced Tau service and image keys",
    )
    for path, symbol in (
        ("tools/generate_operator_systemd.py", "--local-node"),
        ("tools/permissionless_operator_preflight.py", "retired_tau_local_node"),
        ("tools/check_container_hardening.py", "retired Tau local-node service must remain absent"),
    ):
        add(
            f"operator-local-node:{path}",
            "QUARANTINED",
            path,
            symbol,
            "OPERATOR_LOCAL_NODE_SELECTOR",
            marker=symbol.encode("utf-8"),
            current_operation_ids=("LOCAL_OPERATOR_STARTUP", "OPERATOR_LOCAL_NODE_SELECTOR"),
            evidence_ids=("tools/check_container_hardening.py::run_checks",),
            reason="operator tooling refuses or detects the historical local-node selector",
        )

    add(
        "api-autotrader-live-selector",
        "QUARANTINED",
        "src/integration/api_server.py",
        "AUTOTRADER_LIVE_API_ENABLED",
        "HTTP_HANDLER_SELECTOR",
        marker=b"AUTOTRADER_LIVE_API_ENABLED",
        current_operation_ids=("API_REQUEST_DISPATCH", "API_SERVER_STARTUP"),
        evidence_ids=(
            "tests/integration/test_api_server_main.py::test_api_server_refuses_autotrader_live_mount_until_external_intent_signing_exists",
            "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_direct_autotrader_attachment_when_called_then_rejects_before_state_effects",
            "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_retired_http_paths_when_requested_then_modules_stay_unloaded_and_routes_are_absent",
        ),
        reason="startup and direct attachment reject the selector, and request dispatch leaves the historical handler unmounted",
    )
    add(
        "api-retired-wallet-handlers",
        "REMOVED",
        "src/integration/api_server.py",
        "perps/zUSD historical wallet handler imports",
        "HTTP_HANDLER_MOUNT",
        marker=b"from src.integration.perps_wallet_api import handle_perps_wallet_request",
        current_operation_ids=("API_REQUEST_DISPATCH",),
        reason="all three historical wallet handler imports are absent from current dispatch",
    )
    add(
        "confidential-local-tau-callback",
        "REMOVED",
        "src/integration/confidential_sealed_bid_api.py",
        "submit_confidential_sealed_bid_local_ledger_settlement",
        "CALLBACK_AND_SIGNER_ROUTE",
        marker=b"def submit_confidential_sealed_bid_local_ledger_settlement(",
        current_operation_ids=("CONFIDENTIAL_SETTLEMENT",),
        reason="historical local Tau settlement callback is absent",
    )
    add(
        "core-feature-tau-app-lane",
        "REMOVED",
        "tools/zeno_ledger_make_core_feature_suite.py",
        "tau_app_bridge_spot",
        "GENERATED_FEATURE_LANE",
        marker=b"tau_app_bridge_spot",
        current_operation_ids=("CORE_FEATURE_SUITE_BUILD",),
        reason="core feature suite no longer constructs the historical Tau bridge lane",
    )
    add(
        "nginx-tau-signing-route",
        "REMOVED",
        "tools/zenoctl_testnet_local/nginx.py",
        "sign-tau-transaction-payload",
        "NGINX_SIGNER_ROUTE",
        marker=b"sign-tau-transaction-payload",
        current_operation_ids=("LOCAL_OPERATOR_STARTUP", "LOCAL_SIGNER"),
        reason="browser reverse-proxy material no longer publishes the Tau signing endpoint",
    )

    selector_evidence = (
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_retired_tau_state_selector_when_called_then_rejects_before_file_effects",
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_feature_lane_tau_companion_selector_then_rejects_before_paths",
    )
    add(
        "local-block-retired-tau-selectors",
        "QUARANTINED",
        "tools/zeno_ledger_run_local.py",
        "tau-app-state and Tau companion selectors",
        "RUNTIME_SELECTOR",
        marker=b"RETIRED_TAU_APP_STATE_SELECTOR_ERROR",
        current_operation_ids=("LOCAL_BLOCK_BUILD",),
        evidence_ids=selector_evidence,
        reason="selectors reject before reads, writes, subprocesses, or report construction",
    )
    add(
        "feature-lane-retired-tau-selectors",
        "QUARANTINED",
        "tools/zeno_ledger_make_feature_lane.py",
        "tau-app-state and Tau companion selectors",
        "RUNTIME_SELECTOR",
        marker=b"RETIRED_TAU_APP_STATE_SELECTOR_ERROR",
        current_operation_ids=("FEATURE_LANE_BUILD",),
        evidence_ids=selector_evidence,
        reason="feature-lane selectors reject before filesystem effects",
    )
    add(
        "manifest-retired-tau-executable-selectors",
        "QUARANTINED",
        "tools/zeno_ledger_run_manifest.py",
        "RETIRED_TAU_BRIDGE_EXECUTABLES/SELECTORS",
        "MANIFEST_COMMAND_SELECTOR",
        marker=b"RETIRED_TAU_BRIDGE_EXECUTABLES",
        current_operation_ids=("MANIFEST_EXECUTION",),
        evidence_ids=(
            "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_manifest_embeds_retired_tau_state_selector_then_no_command_or_report_runs",
        ),
        reason="exact executable and option pairs reject before command execution",
    )

    node_evidence = (
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_persisted_tau_wrapper_when_any_public_node_writer_runs_then_exact_reject_has_no_authoritative_effect",
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_retired_stream_when_follower_http_ingress_receives_it_then_reject_precedes_forwarding",
    )
    for suffix, symbol, marker in (
        ("tau-wrapper", "zenodex/tau_app_state/v1", b"zenodex/tau_app_state/v1"),
        ("stream-7", "operation stream 7", b'"7" in operations'),
        ("stream-10", "operation stream 10", b'"10" in operations'),
    ):
        add(
            f"node-retired:{suffix}",
            "QUARANTINED",
            "tools/zeno_ledger_node.py",
            symbol,
            "NODE_STATE_OR_OPERATION_SELECTOR",
            marker=marker,
            current_operation_ids=("NODE_STARTUP", "NODE_STATE_WRITE", "NODE_PEER_PULL"),
            evidence_ids=node_evidence,
            reason="startup, public writers, HTTP forwarding, batch append, and peer pull reject before authoritative ledger, report, root, or forwarding effects; writer-lock coordination is permitted",
        )

    signer_evidence = (
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_retired_tau_signing_command_then_exact_reject_precedes_vault_read",
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_direct_retired_tau_signing_call_then_typed_reject_precedes_vault_access",
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_retired_tau_http_signing_route_then_http_410_precedes_signer_access",
    )
    add(
        "signer-direct-tau-transaction-method",
        "QUARANTINED",
        "src/integration/zenodex_local_signer.py",
        "LocalSignerVault.sign_tau_transaction_payload",
        "DIRECT_SIGNER_METHOD",
        marker=b"def sign_tau_transaction_payload(",
        current_operation_ids=("LOCAL_SIGNER",),
        evidence_ids=signer_evidence,
        reason="typed refusal precedes passphrase, payload, key, and vault access",
    )
    for suffix, symbol in (
        ("cli", "cmd_sign_tau_transaction_payload"),
        ("http", "/sign-tau-transaction-payload"),
    ):
        add(
            f"signer-tau-transaction-{suffix}",
            "QUARANTINED",
            "tools/zenodex_local_signer.py",
            symbol,
            "SIGNER_CLI_OR_HTTP_ROUTE",
            marker=symbol.encode("ascii"),
            current_operation_ids=("LOCAL_SIGNER",),
            evidence_ids=signer_evidence,
            reason="historical signing route returns an exact refusal before vault access",
        )

    lifecycle_evidence = (
        "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py::test_given_all_lifecycle_historical_donors_when_called_then_refuse_before_effects",
    )
    for current_name, donor_name in _LIFECYCLE_DONOR_PAIRS_V3:
        add(
            f"lifecycle-entrypoint:{current_name}",
            "QUARANTINED",
            "tools/zenoctl_testnet_local/lifecycle.py",
            f"{current_name}/{donor_name}",
            "CURRENT_WRAPPER_AND_HISTORICAL_DONOR",
            marker=f"def {donor_name}(".encode("ascii"),
            current_operation_ids=("LOCAL_OPERATOR_LIFECYCLE",),
            evidence_ids=lifecycle_evidence,
            reason="both current wrapper and retained donor refuse as their first executable action",
        )

    add(
        "app-root-historical-wrapper-build-mode",
        "REMOVED",
        "tools/build_app_root_jmt_evidence.py",
        "tau_app_state_wrapper_live_root",
        "APP_ROOT_EVIDENCE_MODE",
        marker=b"tau_app_state_wrapper_live_root",
        current_operation_ids=("APP_ROOT_JMT_EVIDENCE_BUILD",),
        reason="evidence builder emits only current plain-snapshot and local-block modes",
    )
    add(
        "app-root-historical-wrapper-admission",
        "QUARANTINED",
        "src/integration/production_promotion_evidence.py",
        "tau_app_state_wrapper_live_root",
        "APP_ROOT_PROMOTION_MODE",
        marker=b"unsupported app-root live-root mode",
        current_operation_ids=("APP_ROOT_JMT_PROMOTION_ADMISSION",),
        evidence_ids=(
            "tests/integration/test_app_root_jmt_promotion_lane.py::test_lane_evaluator_rejects_self_consistent_historical_tau_wrapper_mode",
        ),
        reason="promotion evaluator rejects a self-consistent injected historical wrapper mode",
    )
    add(
        "production-credit-historical-plugin",
        "REMOVED",
        "tools/check_production_boundary.py",
        "tau_testnet_dex_plugin_enters_through_dex_engine",
        "PRODUCTION_REQUIREMENT_CREDIT",
        marker=b"tau_testnet_dex_plugin_enters_through_dex_engine",
        current_operation_ids=("PRODUCTION_BOUNDARY_AUDIT",),
        reason="historical plugin behavior no longer contributes positive production evidence",
    )

    oracle_specs = (
        ("src/integration/tau_net_client.py", "TauNetTcpClient", "HISTORICAL_RPC_CLIENT", ("RESEARCH_TAU_RPC_CLIENT",)),
        ("src/integration/tau_net_client.py", "build_signed_tau_transaction", "HISTORICAL_TRANSACTION_BUILDER", ("RESEARCH_HISTORICAL_TOOLING",)),
        ("src/integration/tau_testnet_dex_plugin.py", "propose_app_tx_v1", "HISTORICAL_APP_BRIDGE", ("RESEARCH_TAU_APP_PLUGIN",)),
        ("src/integration/tau_testnet_dex_plugin.py", "apply_app_tx", "HISTORICAL_APP_BRIDGE", ("RESEARCH_TAU_APP_PLUGIN",)),
        ("src/integration/autotrader_live.py", "prepare_autotrader_live_quote_receipt", "HISTORICAL_AUTOTRADER", ("RESEARCH_AUTOTRADER_TAU",)),
        ("src/integration/perps_wallet_api.py", "handle_perps_wallet_request", "HISTORICAL_WALLET_HANDLER", ("RESEARCH_PERPS_WALLET",)),
        ("src/integration/zusd_tau_wallet_api.py", "handle_zusd_tau_wallet_request", "HISTORICAL_WALLET_HANDLER", ("RESEARCH_ZUSD_TAU_WALLET_ORACLE",)),
        ("src/integration/zusd_monetary_wallet_api.py", "handle_zusd_monetary_wallet_request", "HISTORICAL_WALLET_HANDLER", ("RESEARCH_ZUSD_MONETARY_WALLET_ORACLE",)),
        ("src/integration/zusd_tau_token.py", "prepare_zusd_tau_token_operation", "HISTORICAL_TOKEN_BRIDGE", ("RESEARCH_ZUSD_TOKEN_BRIDGE",)),
        ("src/integration/zusd_tau_token.py", "derive_zusd_tau_asset_id", "HISTORICAL_TOKEN_BRIDGE", ("RESEARCH_ZUSD_TOKEN_BRIDGE",)),
        ("src/integration/zusd_monetary_bridge.py", "init_monetary_state", "HISTORICAL_MONETARY_BRIDGE", ("RESEARCH_ZUSD_MONETARY_BRIDGE",)),
        ("src/integration/zusd_monetary_bridge.py", "apply_zusd_monetary_ops", "HISTORICAL_MONETARY_BRIDGE", ("RESEARCH_ZUSD_MONETARY_BRIDGE",)),
    )
    current_source = {path: item.data for path, item in subject.items()}
    for path, symbol, kind, research_ids in oracle_specs:
        tree = _parse_python(current_source, path)
        function = _unique_top_level_function(tree, symbol)
        class_node = _unique_top_level_class(tree, symbol)
        if (function is None) == (class_node is None):
            _reject("HISTORICAL_ORACLE_SYMBOL", path, symbol)
        add(
            f"research-oracle:{path}:{symbol}",
            "RESEARCH_ORACLE",
            path,
            symbol,
            kind,
            marker=f"{symbol}".encode("ascii"),
            research_operation_ids=research_ids,
            reason="retained as source-pinned historical research material with no current operation authority",
        )
    for _, donor_name in _LIFECYCLE_DONOR_PAIRS_V3:
        add(
            f"research-oracle:tools/zenoctl_testnet_local/lifecycle.py:{donor_name}",
            "RESEARCH_ORACLE",
            "tools/zenoctl_testnet_local/lifecycle.py",
            donor_name,
            "HISTORICAL_LIFECYCLE_DONOR_SOURCE",
            marker=f"def {donor_name}(".encode("ascii"),
            research_operation_ids=("RESEARCH_LIFECYCLE_DONOR_SOURCE",),
            reason="guarded donor body is retained for future versioned refinement and grants no authority",
        )
    return rows


def _validate_dependency_rows(rows: list[dict[str, object]]) -> None:
    dependency_ids: list[str] = []
    identities: list[tuple[object, ...]] = []
    used_current: set[str] = set()
    used_research: set[str] = set()
    current_registry = set(CURRENT_OPERATION_IDS_V3)
    research_registry = set(RESEARCH_OPERATION_IDS_V3)
    for index, row in enumerate(rows):
        path = f"dependency_rows[{index}]"
        dependency_id = row.get("dependency_id")
        classification = row.get("classification")
        current_ids = row.get("current_operation_ids")
        baseline_ids = row.get("baseline_operation_ids")
        research_ids = row.get("research_operation_ids")
        evidence_ids = row.get("quarantine_evidence_ids")
        if type(dependency_id) is not str or not dependency_id:
            _reject("DEPENDENCY_ID", path, "requires nonempty exact string")
        if classification not in _CLASSIFICATIONS_V3:
            _reject("CLASSIFICATION", path, str(classification))
        for field, value in (
            ("baseline_operation_ids", baseline_ids),
            ("current_operation_ids", current_ids),
            ("research_operation_ids", research_ids),
            ("quarantine_evidence_ids", evidence_ids),
        ):
            if type(value) is not list or any(type(item) is not str for item in value):
                _reject("DEPENDENCY_ROW_SHAPE", path, field)
            if value != sorted(set(value)):
                _reject("DEPENDENCY_ROW_ORDER", path, field)
        current_ids = cast(list[str], current_ids)
        baseline_ids = cast(list[str], baseline_ids)
        research_ids = cast(list[str], research_ids)
        evidence_ids = cast(list[str], evidence_ids)
        foreign_current = (set(current_ids) | set(baseline_ids)) - current_registry
        foreign_research = set(research_ids) - research_registry
        if foreign_current or foreign_research:
            _reject(
                "FOREIGN_OPERATION_ID",
                path,
                ",".join(sorted(foreign_current | foreign_research)),
            )
        if classification == "RESEARCH_ORACLE":
            if current_ids or baseline_ids:
                _reject(
                    "RESEARCH_ORACLE_REACHABLE_FROM_CURRENT_OPERATION",
                    path,
                    dependency_id,
                )
            if not research_ids:
                _reject("ORACLE_OPERATION_MISSING", path, dependency_id)
        elif research_ids:
            _reject("RESEARCH_OPERATION_ON_CURRENT_DEPENDENCY", path, dependency_id)
        if classification == "QUARANTINED" and (not current_ids or not evidence_ids):
            _reject("QUARANTINE_WITNESS_MISSING", path, dependency_id)
        baseline_occurrences = row.get("baseline_occurrences")
        current_occurrences = row.get("current_occurrences")
        if (
            type(baseline_occurrences) is not int
            or baseline_occurrences < 0
            or type(current_occurrences) is not int
            or current_occurrences < 0
        ):
            _reject("OCCURRENCE_COUNT", path, dependency_id)
        dependency_ids.append(dependency_id)
        identities.append(
            (
                row.get("source_path"),
                row.get("scope"),
                row.get("symbol"),
                row.get("dependency_kind"),
                row.get("target"),
            )
        )
        used_current.update(current_ids)
        used_research.update(research_ids)
    if len(dependency_ids) != len(set(dependency_ids)) or len(identities) != len(set(identities)):
        _reject("DUPLICATE_DEPENDENCY", "dependency_rows", "dependency identity collision")
    missing_current = current_registry - used_current
    missing_research = research_registry - used_research
    if missing_current or missing_research:
        _reject(
            "OPERATION_REGISTRY_COVERAGE",
            "dependency_rows",
            ",".join(sorted(missing_current | missing_research)),
        )


def _row_string_list(row: Mapping[str, object], field: str) -> list[str]:
    value = row.get(field)
    if type(value) is not list or any(type(item) is not str for item in value):
        _reject("DEPENDENCY_ROW_SHAPE", "dependency_rows", field)
    return cast(list[str], value)


def _operation_registry(rows: Sequence[dict[str, object]]) -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    for lane, operation_ids, field in (
        ("CURRENT_OPERATION", CURRENT_OPERATION_IDS_V3, "current_operation_ids"),
        ("RESEARCH_ORACLE", RESEARCH_OPERATION_IDS_V3, "research_operation_ids"),
    ):
        for operation_id in operation_ids:
            dependencies = sorted(
                str(row["dependency_id"])
                for row in rows
                if operation_id in _row_string_list(row, field)
            )
            evidence = sorted(
                {
                    str(evidence_id)
                    for row in rows
                    if operation_id in _row_string_list(row, field)
                    for evidence_id in _row_string_list(
                        row, "quarantine_evidence_ids"
                    )
                }
            )
            result.append(
                {
                    "dependency_ids": dependencies,
                    "evidence_ids": evidence,
                    "lane": lane,
                    "operation_id": operation_id,
                }
            )
    return sorted(result, key=lambda row: str(row["operation_id"]))


def derive_closure_v3(
    snapshot: SubjectSnapshotV3,
) -> tuple[
    dict[str, SourceFileV3],
    dict[str, SourceFileV3],
    list[dict[str, object]],
    dict[str, object],
]:
    baseline, subject = _snapshot_sources(snapshot)
    baseline_discovery, subject_discovery, current_discovery = (
        _snapshot_discoveries(snapshot)
    )
    if _path_set_sha256(DIRECT_CONSUMER_PATHS_V3) != DIRECT_CONSUMER_PATH_SET_SHA256_V3:
        _reject("SOURCE_SCOPE", "direct consumers", "fixed path-set digest drift")
    current_source = {path: item.data for path, item in subject.items()}
    _require_plan_and_current_tau(current_source)
    _require_route_witnesses(baseline, subject)
    current_route_source_root = _manifest_root(
        _source_manifest(subject, _ROUTE_PIN_PATHS_V3)
    )
    if current_route_source_root != EXPECTED_CURRENT_ROUTE_SOURCE_ROOT_V3:
        _reject(
            "CURRENT_ROUTE_SOURCE_SET",
            "route witnesses",
            current_route_source_root,
        )

    import_rows, projection = _import_dependency_rows(baseline, subject)
    discovery_projection = _require_discovery_closure(
        baseline_direct=scan_bridge_import_edges_v3(
            {
                path: baseline[path].data
                for path in DIRECT_CONSUMER_PATHS_V3
            }
        ),
        subject_direct=scan_bridge_import_edges_v3(
            {
                path: subject[path].data
                for path in DIRECT_CONSUMER_PATHS_V3
            }
        ),
        baseline_discovery=baseline_discovery,
        subject_discovery=subject_discovery,
        current_discovery=current_discovery,
    )
    baseline_direct_manifest = _source_manifest(baseline, DIRECT_CONSUMER_PATHS_V3)
    current_direct_manifest = _source_manifest(subject, DIRECT_CONSUMER_PATHS_V3)
    baseline_source_root = _manifest_root(baseline_direct_manifest)
    current_source_root = _manifest_root(current_direct_manifest)
    if baseline_source_root != EXPECTED_BASELINE_SOURCE_ROOT_V3:
        _reject("BASELINE_SOURCE_SET", "direct consumers", baseline_source_root)
    if current_source_root != EXPECTED_CURRENT_SOURCE_ROOT_V3:
        _reject("CURRENT_SOURCE_SET", "direct consumers", current_source_root)
    rows = import_rows + _manual_dependency_rows(baseline, subject)
    rows.sort(key=lambda row: str(row["dependency_id"]))
    _validate_dependency_rows(rows)
    import_counts = {
        classification: sum(
            row["classification"] == classification for row in import_rows
        )
        for classification in _CLASSIFICATIONS_V3
    }
    if import_counts != {"QUARANTINED": 0, "RESEARCH_ORACLE": 92, "REMOVED": 36}:
        _reject("IMPORT_CLASSIFICATION_COUNTS", "import projection", str(import_counts))
    projection.update(
        {
            "baseline_source_bytes": sum(
                cast(int, row["size"]) for row in baseline_direct_manifest
            ),
            "baseline_source_root_sha256": baseline_source_root,
            "current_source_bytes": sum(
                cast(int, row["size"]) for row in current_direct_manifest
            ),
            "current_source_root_sha256": current_source_root,
            "current_route_source_root_sha256": current_route_source_root,
            "direct_consumer_path_count": len(DIRECT_CONSUMER_PATHS_V3),
            "direct_consumer_path_set_sha256": DIRECT_CONSUMER_PATH_SET_SHA256_V3,
            "import_classification_counts": import_counts,
            **discovery_projection,
        }
    )
    return baseline, subject, rows, projection


def build_artifact_v3(snapshot: SubjectSnapshotV3) -> bytes:
    baseline, subject, rows, projection = derive_closure_v3(snapshot)
    classification_counts = {
        classification: sum(row["classification"] == classification for row in rows)
        for classification in _CLASSIFICATIONS_V3
    }
    operation_registry = _operation_registry(rows)
    unsigned: dict[str, object] = {
        "active_plan_binding": {
            "admission_receipt_payload_sha256": PLAN_ADMISSION_PAYLOAD_SHA256_V3,
            "admission_receipt_sha256": PLAN_ADMISSION_RECEIPT_SHA256_V3,
            "admitted_commit": PLAN_ADMITTED_COMMIT_V3,
            "admitted_tree": PLAN_ADMITTED_TREE_V3,
            "plan_path": PLAN_PATH_V3,
            "plan_sha256": PLAN_SHA256_V3,
            "registry_sha256": PLAN_REGISTRY_SHA256_V3,
        },
        "baseline_subject": {
            "commit": snapshot.baseline.commit,
            "tree": snapshot.baseline.tree,
        },
        "claim_ceiling": {
            "closed_value_movement_gates": 0,
            "production_authority": "NONE",
            "release_authority": "NONE",
            "settlement_authority": "NONE",
            "value_movement_authority": "NONE",
            "value_movement_claim_allowed": False,
        },
        "dependency_projection": {
            "classification_counts": classification_counts,
            "dependency_count": len(rows),
            "dependency_rows": rows,
        },
        "evidence_subject": {
            "commit": snapshot.subject.commit,
            "tree": snapshot.subject.tree,
        },
        "generator_command": GENERATOR_COMMAND_V3,
        "nonclaims": [
            "No top-level tests/ or renamed-copy completeness is claimed.",
            "No computed dynamic-loading completeness is claimed.",
            "No generated-code, frontend, Docker-transitive, shell-transitive, Rust, Tau, or other cross-language closure is claimed.",
            "No O-006 command-to-lane closure is claimed.",
            "No O-007B/C recovery, migration, callback, worker, subprocess, administrative, deployed, or cross-language closure is claimed.",
            "Research-oracle source may remain in shipped bytes and has no current operation authority.",
            "The pinned Python checker modules, interpreter, operating system, and Git executable remain trusted replay premises.",
            "Terminal replays require a quiescent single-writer worktree; sequential no-follow reads detect observed drift but do not create an atomic filesystem snapshot.",
            "A successful replay on a descendant HEAD does not certify that descendant tree; completion remains bound to evidence_subject.",
            "No production, release, settlement, migration, or value-moving authority is granted.",
        ],
        "o003b_completion": {
            "closes_only": [
                "retired_bridge_dependency_inventory_gap",
                "stale_tau_assurance",
            ],
            "obligation_id": "O-003B",
            "scope": "ORDINARY_STATIC_PYTHON_IMPORT_CLOSURE_AND_FINITE_ROUTE_WITNESSES",
            "status": "COMPLETE_ON_STAGE_A_EVIDENCE_SUBJECT",
        },
        "operation_registry": {
            "current_operation_ids": list(CURRENT_OPERATION_IDS_V3),
            "operation_rows": operation_registry,
            "research_operation_ids": list(RESEARCH_OPERATION_IDS_V3),
        },
        "schema": ARTIFACT_SCHEMA_V3,
        "source_projection": projection,
        "source_snapshot_pins": {
            "baseline": [
                {"path": path, **_source_pin(baseline[path])}
                for path in BASELINE_PIN_PATHS_V3
            ],
            "subject": [
                {"path": path, **_source_pin(subject[path])}
                for path in SUBJECT_PIN_PATHS_V3
            ],
        },
        "startup_refusal_evidence": {
            "path": "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py",
            "replay_command": "python3 -m pytest -q tests/integration/test_retired_tau_bridge_startup_refusal_v2.py",
        },
        "status": "RESEARCH_ONLY_O003B_COMPLETE_ON_STAGE_A_EVIDENCE_SUBJECT",
    }
    unsigned_bytes = canonical_json_bytes_v3(unsigned)
    artifact = {**unsigned, "certificate_root": _sha256(unsigned_bytes)}
    raw = canonical_json_bytes_v3(artifact)
    if len(raw) > MAX_ARTIFACT_BYTES_V3:
        _reject("ARTIFACT_SIZE", "artifact", f"{len(raw)} bytes")
    return raw


_ARTIFACT_TOP_LEVEL_FIELDS_V3: Final = frozenset(
    {
        "active_plan_binding",
        "baseline_subject",
        "certificate_root",
        "claim_ceiling",
        "dependency_projection",
        "evidence_subject",
        "generator_command",
        "nonclaims",
        "o003b_completion",
        "operation_registry",
        "schema",
        "source_projection",
        "source_snapshot_pins",
        "startup_refusal_evidence",
        "status",
    }
)


def _validate_artifact_semantics(artifact: dict[str, object]) -> None:
    if set(artifact) != _ARTIFACT_TOP_LEVEL_FIELDS_V3:
        _reject("ARTIFACT_FIELDS", "artifact", "closed top-level field set drift")
    if artifact.get("schema") != ARTIFACT_SCHEMA_V3:
        _reject("ARTIFACT_SCHEMA", "artifact", str(artifact.get("schema")))
    claim = artifact.get("claim_ceiling")
    expected_claim = {
        "closed_value_movement_gates": 0,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "value_movement_claim_allowed": False,
    }
    if type(claim) is not dict:
        _reject("AUTHORITY_PROMOTION", "claim_ceiling", "missing exact object")
    if claim.get("closed_value_movement_gates") != 0:
        _reject("VM_GATE_PROMOTION", "claim_ceiling", "O-003B closes zero VM gates")
    if claim != expected_claim:
        _reject("AUTHORITY_PROMOTION", "claim_ceiling", "authority must remain NONE")

    registry = artifact.get("operation_registry")
    if type(registry) is not dict:
        _reject("OPERATION_REGISTRY_SHAPE", "operation_registry", "missing exact object")
    if registry.get("current_operation_ids") != list(CURRENT_OPERATION_IDS_V3) or registry.get("research_operation_ids") != list(RESEARCH_OPERATION_IDS_V3):
        _reject("OPERATION_REGISTRY_DRIFT", "operation_registry", "closed operation ids drift")
    projection = artifact.get("dependency_projection")
    if type(projection) is not dict or type(projection.get("dependency_rows")) is not list:
        _reject("DEPENDENCY_ROW_SHAPE", "dependency_projection", "rows missing")
    rows = projection["dependency_rows"]
    if any(type(row) is not dict for row in rows):
        _reject("DEPENDENCY_ROW_SHAPE", "dependency_projection", "row must be an object")
    typed_rows = list(rows)
    _validate_dependency_rows(typed_rows)
    counts = {
        classification: sum(row.get("classification") == classification for row in typed_rows)
        for classification in _CLASSIFICATIONS_V3
    }
    if projection.get("classification_counts") != counts or projection.get("dependency_count") != len(typed_rows):
        _reject("CLASSIFICATION_COUNT", "dependency_projection", "count replay drift")
    expected_registry = _operation_registry(typed_rows)
    if registry.get("operation_rows") != expected_registry:
        _reject("OPERATION_REGISTRY_DRIFT", "operation_registry", "operation edge replay drift")

    certificate_root = artifact.get("certificate_root")
    if type(certificate_root) is not str:
        _reject("CERTIFICATE_ROOT", "artifact", "missing root")
    unsigned = dict(artifact)
    del unsigned["certificate_root"]
    if certificate_root != _sha256(canonical_json_bytes_v3(unsigned)):
        _reject("CERTIFICATE_ROOT", "artifact", "self-binding root mismatch")


def check_artifact_v3(raw: bytes, snapshot: SubjectSnapshotV3) -> dict[str, object]:
    if type(raw) is not bytes or len(raw) > MAX_ARTIFACT_BYTES_V3:
        _reject("ARTIFACT_SIZE", "artifact", "requires bounded exact bytes")
    artifact = _decode_json_object(raw, "artifact")
    if canonical_json_bytes_v3(artifact) != raw:
        _reject("NONCANONICAL_ARTIFACT", "artifact", "bytes are not canonical JSON")
    _validate_artifact_semantics(artifact)
    expected = build_artifact_v3(snapshot)
    if raw != expected:
        _reject("ARTIFACT_REPLAY_MISMATCH", "artifact", "bytes differ from derivation")
    projection = cast(dict[str, object], artifact["dependency_projection"])
    source_projection = cast(dict[str, object], artifact["source_projection"])
    return {
        "artifact_sha256": _sha256(raw),
        "classification_counts": projection["classification_counts"],
        "closed_value_movement_gates": 0,
        "current_only_import_edge_count": source_projection["current_only_edge_count"],
        "dependency_count": projection["dependency_count"],
        "findings": [],
        "o003b_status": "COMPLETE_ON_STAGE_A_EVIDENCE_SUBJECT",
        "ok": True,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": CHECK_SCHEMA_V3,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def failure_report_v3(exc: ClosureRejectV3) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "classification_counts": {},
        "closed_value_movement_gates": 0,
        "current_only_import_edge_count": None,
        "dependency_count": 0,
        "findings": [{"code": exc.code, "detail": exc.detail, "path": exc.path}],
        "o003b_status": "OPEN",
        "ok": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": CHECK_SCHEMA_V3,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }
