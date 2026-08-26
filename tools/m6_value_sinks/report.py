"""Compare observations against the manifest and assemble the inventory report.

Field names deliberately say ``static_source`` rather than ``deployed``.  The
scan reaches statically resolvable edges from decoded launchers; it does not
establish runtime reachability or complete deployment coverage.
"""

from __future__ import annotations

import ast
import hashlib
from pathlib import Path
from typing import Any, TypedDict, cast

from tools.m6_value_sinks.deployment import (
    MAX_AST_NODES,
    MAX_SOURCE_BYTES,
    DeploymentClosureV2,
    derive_python_deployment_closure,
)
from tools.m6_value_sinks.launchers import (
    DEFAULT_SCAN_RESOURCE_LIMITS_V2,
    ClosureFindingV2,
    RepositorySnapshotChanged,
    RepositorySnapshotV2,
    ResourceBudgetExceeded,
    ScanResourceLimitsV2,
    read_bounded_text,
)
from tools.m6_value_sinks.manifest import (
    MAX_MANIFEST_BYTES,
    SCHEMA_V2,
    UNADJUDICATED,
    ClosureGapV2,
    ValueSinkSpecV2,
    decode_value_sink_document_text_v2,
)
from tools.m6_value_sinks.operations import (
    LiteralPathResolverV2,
    combine_fingerprints,
)
from tools.m6_value_sinks.scanner import ValueSinkObservationV2, scan_module

MANIFEST_NAME = "m6_value_sink_manifest_v2.json"

NONCLAIMS: tuple[str, ...] = (
    "this is a static-source inventory aid; it is never proof of sole-publisher closure",
    "scanner-relative manifest agreement means only that the manifest matches operations recognized by this bounded scanner; it is not closure completeness",
    "ephemeral tempfile and temporary-directory kinds record API cleanup intent; they do not prove crash cleanup or terminal deletion",
    "the scan follows statically resolvable Python import and dispatch edges from decoded launchers only",
    "recognized unresolved executable mechanisms are reported as closure gaps; unrecognized dynamic, plugin, native, generated, and cross-language dispatch may remain outside this inventory",
    "Rust, Tau, shell bodies, generated code, native extensions, and container wiring beyond entrypoint dispatch require separate cross-language inventories",
    "an observed operation may be unreachable at runtime, and an unobserved path may still write through an unmodelled mechanism",
    "classification and consumer tracing record research judgement; the manifest carries no release-backed authority",
    "schema v2 has no reviewed transitive control-dependency certificate, so mediated-by-publisher judgements reset on every regeneration",
    "a source-bound reader record proves only an exact static instruction; runtime execution and artifact consumption remain unproved",
    "a passing result does not establish complete mediation, durability, finality, or safe value movement",
    "VM-01 remains open; no gate here contributes production authority",
)


class ValueSinkReportV2(TypedDict):
    """Typed shape of the inventory report consumed by the CLI and tests."""

    adjudicated_identity_count: int
    declared_closure_gaps: list[dict[str, str]]
    decoded_launchers: list[dict[str, str]]
    findings: list[dict[str, str]]
    scanner_relative_manifest_agreement: bool
    closure_complete: bool
    manifest_identity_count: int
    nonclaims: list[str]
    observed_occurrence_count: int
    production_authority: bool
    p2_t01_status: str
    p2_t02_status: str
    release_gaps: list[str]
    release_ready: bool
    schema: str
    sinks: list[dict[str, object]]
    static_reachable_unscanned_modules: list[str]
    static_scanned_module_count: int
    static_scanned_module_digests: list[dict[str, str]]
    unadjudicated_sinks: list[str]
    unmediated_static_writers: list[str]
    vm01_status: str


REPORT_FIELDS_V2 = frozenset(ValueSinkReportV2.__annotations__)
REPORT_ROW_FIELDS_V2: dict[str, frozenset[str]] = {
    "declared_closure_gaps": frozenset({"mechanism", "path", "rationale"}),
    "decoded_launchers": frozenset({"discovery", "entrypoint_id", "target"}),
    "findings": frozenset({"evidence", "path", "rule_id"}),
    "static_scanned_module_digests": frozenset({"path", "sha256"}),
}
SINK_REPORT_FIELDS_V2 = frozenset(
    {
        "classification",
        "consumers",
        "deployed_reachable",
        "identity_fingerprint",
        "mediation_status",
        "occurrence_count",
        "path",
        "rationale",
        "release_binding",
        "sink_id",
        "sink_kind",
        "symbol",
    }
)
CONSUMER_REPORT_FIELDS_V2 = frozenset(
    {
        "artifact",
        "kind",
        "reader_fingerprint",
        "reference",
        "source_path",
        "source_sha256",
    }
)
MAX_REPORT_VALUE_NODES_V2 = 500_000
MAX_REPORT_LIST_ITEMS_V2 = 100_000


def _observation_groups(
    observations: tuple[ValueSinkObservationV2, ...],
) -> dict[tuple[str, str, str], list[ValueSinkObservationV2]]:
    groups: dict[tuple[str, str, str], list[ValueSinkObservationV2]] = {}
    for observation in observations:
        groups.setdefault(observation.identity(), []).append(observation)
    return groups


def compare_inventory(
    specs: tuple[ValueSinkSpecV2, ...],
    observations: tuple[ValueSinkObservationV2, ...],
    scanned_modules: frozenset[str] = frozenset(),
) -> tuple[ClosureFindingV2, ...]:
    """Require one exact classification per observed durable-write identity."""

    findings: list[ClosureFindingV2] = []
    groups = _observation_groups(observations)
    specs_by_identity = {spec.identity(): spec for spec in specs}
    for identity, group in sorted(groups.items()):
        spec = specs_by_identity.get(identity)
        count = len(group)
        evidence = f"{identity[1]}:{identity[2]}:{count}"
        if spec is None:
            findings.append(ClosureFindingV2(identity[0], "unclassified_value_sink", evidence))
            continue
        if spec.occurrence_count != count:
            findings.append(
                ClosureFindingV2(
                    identity[0], "value_sink_occurrence_mismatch", f"{evidence}:expected={spec.occurrence_count}"
                )
            )
        fingerprint = combine_fingerprints(tuple(item.fingerprint for item in group))
        if spec.identity_fingerprint != fingerprint:
            findings.append(
                ClosureFindingV2(
                    identity[0], "operation_fingerprint_mismatch", f"{spec.sink_id}:observed={fingerprint}"
                )
            )
        if spec.deployed_reachable != (identity[0] in scanned_modules):
            findings.append(
                ClosureFindingV2(
                    identity[0], "reachability_claim_mismatch", f"{spec.sink_id}:declared={spec.deployed_reachable}"
                )
            )
    for identity, spec in sorted(specs_by_identity.items()):
        if identity not in groups:
            findings.append(
                ClosureFindingV2(spec.path, "classified_value_sink_missing", f"{spec.symbol}:{spec.sink_kind}")
            )
    return tuple(sorted(findings))


def reconcile_closure_gaps(
    observed: tuple[tuple[str, str], ...], declared: tuple[ClosureGapV2, ...]
) -> tuple[ClosureFindingV2, ...]:
    """Require the declared incompleteness set to equal the observed one."""

    declared_identities = {gap.identity() for gap in declared}
    observed_identities = set(observed)
    findings = [
        ClosureFindingV2(path, "undeclared_closure_gap", mechanism)
        for path, mechanism in sorted(observed_identities - declared_identities)
    ]
    findings.extend(
        ClosureFindingV2(path, "stale_closure_gap", mechanism)
        for path, mechanism in sorted(declared_identities - observed_identities)
    )
    return tuple(sorted(findings))


def _reader_fingerprint(source_path: str, artifact: str, call: ast.Call) -> str:
    rendered = ast.dump(call, annotate_fields=True, include_attributes=False)
    payload = (
        b"zenodex-m6-reader-v2\0"
        + source_path.encode("utf-8")
        + b"\0"
        + artifact.encode("utf-8")
        + b"\0"
        + rendered.encode("utf-8")
    )
    return hashlib.sha256(payload).hexdigest()


def _reader_fingerprints(
    source_path: str, artifact: str, text: str
) -> tuple[frozenset[str], frozenset[str]]:
    """Return direct-module and nested typed pathlib read instructions."""

    try:
        tree = ast.parse(text, filename=source_path)
    except (SyntaxError, ValueError, RecursionError):
        return frozenset(), frozenset()
    if sum(1 for _ in ast.walk(tree)) > MAX_AST_NODES:
        return frozenset(), frozenset()
    resolver = LiteralPathResolverV2(tree)
    parents = {
        child: parent for parent in ast.walk(tree) for child in ast.iter_child_nodes(parent)
    }
    direct_module: set[str] = set()
    unreachable: set[str] = set()
    for node in ast.walk(tree):
        if (
            not isinstance(node, ast.Call)
            or not isinstance(node.func, ast.Attribute)
            or node.func.attr not in {"read_bytes", "read_text"}
            or node.args
            or node.keywords
        ):
            continue
        literal = resolver.pathlib_receiver_literal_at(node.func.value, node)
        if literal != artifact:
            continue
        fingerprint = _reader_fingerprint(source_path, artifact, node)
        parent = parents.get(node)
        if (
            isinstance(parent, ast.Expr)
            and parent.value is node
            and parents.get(parent) is tree
        ) or (
            isinstance(parent, (ast.Assign, ast.AnnAssign))
            and parent.value is node
            and parents.get(parent) is tree
        ):
            direct_module.add(fingerprint)
        else:
            unreachable.add(fingerprint)
    return frozenset(direct_module), frozenset(unreachable)


def consumer_binding_findings(
    root: Path | RepositorySnapshotV2,
    closure: DeploymentClosureV2,
    specs: tuple[ValueSinkSpecV2, ...],
    observations: tuple[ValueSinkObservationV2, ...],
) -> tuple[ClosureFindingV2, ...]:
    """Bind writer, source bytes, and one exact static read instruction.

    Launcher identity proves dispatch only.  It cannot prove that any code reads
    an artifact, so launcher-only records remain non-adjudicable. Even a direct
    module instruction may be preceded by failure, so static evidence always
    retains ``runtime_read_unproved`` until a separate replay lane exists.
    """

    findings: list[ClosureFindingV2] = []
    scanned = frozenset(closure.modules)
    module_digests = dict(closure.module_digests)
    entrypoint_targets = frozenset(item.target for item in closure.entrypoints)
    groups = _observation_groups(observations)
    source_cache: dict[str, tuple[str | None, str | None]] = {}
    for spec in specs:
        group = groups.get(spec.identity(), [])
        for consumer in spec.consumers:
            evidence = f"{spec.sink_id}:{consumer.kind}:{consumer.reference}"
            if consumer.kind != "REPO_PATH":
                findings.append(
                    ClosureFindingV2(spec.path, "consumer_read_unverifiable", evidence)
                )
                continue
            if consumer.source_path not in scanned:
                findings.append(
                    ClosureFindingV2(spec.path, "unresolved_consumer_reference", evidence)
                )
                continue
            if consumer.source_path not in entrypoint_targets:
                findings.append(
                    ClosureFindingV2(
                        spec.path,
                        "consumer_source_not_entrypoint",
                        evidence,
                    )
                )
                continue
            if not any(
                observation.destination_resolved
                and observation.destination == f"LITERAL:{consumer.artifact}"
                for observation in group
            ):
                findings.append(
                    ClosureFindingV2(spec.path, "consumer_artifact_unbound", evidence)
                )
                continue
            if consumer.source_path not in source_cache:
                source_cache[consumer.source_path] = read_bounded_text(
                    Path(root) / consumer.source_path, MAX_SOURCE_BYTES, root=root
                )
            source, error = source_cache[consumer.source_path]
            if source is None:
                findings.append(
                    ClosureFindingV2(
                        spec.path,
                        "consumer_source_unreadable",
                        f"{evidence}:{error}",
                    )
                )
                continue
            actual_digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
            closure_digest = module_digests.get(consumer.source_path)
            if actual_digest != consumer.source_sha256 or closure_digest != consumer.source_sha256:
                findings.append(
                    ClosureFindingV2(
                        spec.path,
                        "consumer_source_digest_mismatch",
                        f"{evidence}:observed={actual_digest}",
                    )
                )
                continue
            fingerprints, unreachable_fingerprints = _reader_fingerprints(
                consumer.source_path, consumer.artifact, source
            )
            if consumer.reader_fingerprint in unreachable_fingerprints:
                findings.append(
                    ClosureFindingV2(
                        spec.path,
                        "consumer_read_unreachable",
                        evidence,
                    )
                )
            elif consumer.reader_fingerprint not in fingerprints:
                findings.append(
                    ClosureFindingV2(
                        spec.path,
                        "consumer_reader_fingerprint_mismatch",
                        evidence,
                    )
                )
            else:
                findings.append(
                    ClosureFindingV2(
                        spec.path,
                        "runtime_read_unproved",
                        evidence,
                    )
                )
    return tuple(sorted(findings))


def dynamic_destination_gaps(
    observations: tuple[ValueSinkObservationV2, ...],
) -> tuple[tuple[str, str], ...]:
    """Report modules whose writers take a destination this scan cannot resolve.

    A shared helper writing to a caller-supplied path may write an evidence file
    or a balance file, so no classification of that row is verifiable from the
    helper body alone.
    """

    return tuple(
        sorted({(item.path, "dynamic_destination") for item in observations if not item.destination_resolved})
    )


def unresolved_destination_adjudication_findings(
    specs: tuple[ValueSinkSpecV2, ...], observations: tuple[ValueSinkObservationV2, ...]
) -> tuple[ClosureFindingV2, ...]:
    """Reject an economic judgement whose written artifact is not source-bound."""

    unresolved = {item.identity() for item in observations if not item.destination_resolved}
    return tuple(
        ClosureFindingV2(
            spec.path,
            "unresolved_destination_adjudication",
            f"{spec.sink_id}:{spec.symbol}:{spec.sink_kind}",
        )
        for spec in specs
        if spec.identity() in unresolved and spec.classification != UNADJUDICATED
    )


def uncertified_mediation_findings(
    specs: tuple[ValueSinkSpecV2, ...],
) -> tuple[ClosureFindingV2, ...]:
    """Reject mediated judgements while V2 has no control certificate field."""

    return tuple(
        ClosureFindingV2(
            spec.path,
            "mediation_control_dependency_unbound",
            f"{spec.sink_id}:{spec.symbol}:{spec.sink_kind}",
        )
        for spec in specs
        if spec.mediation_status == "MEDIATED_BY_VERIFIED_PUBLISHER"
    )


def scan_closure(
    root: Path | RepositorySnapshotV2, closure: DeploymentClosureV2
) -> tuple[ValueSinkObservationV2, ...]:
    """Observe operations across the statically scanned module set.

    The observation phase re-reads under the same bounds as the closure phase
    and requires the exact digest the closure recorded.  A file swapped,
    truncated, or grown between the phases therefore rejects instead of
    producing observations that describe different bytes than the closure.
    """

    if not isinstance(root, RepositorySnapshotV2):
        with RepositorySnapshotV2(root) as snapshot:
            snapshot_observations = scan_closure(snapshot, closure)
            snapshot.verify_stable()
            return snapshot_observations
    root.assert_path_identity()
    digests = dict(closure.module_digests)
    observations: list[ValueSinkObservationV2] = []
    for relative in closure.modules:
        text, error = read_bounded_text(root.root_path / relative, MAX_SOURCE_BYTES, root=root)
        if text is None:
            raise ValueError(f"cannot scan {relative}: {error}")
        root.resource_meter.claim_source_bytes(len(text.encode("utf-8")))
        digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
        expected = digests.get(relative)
        if expected is None or digest != expected:
            raise ValueError(f"cannot scan {relative}: source changed between closure and scan")
        try:
            tree = ast.parse(text, filename=relative)
        except (SyntaxError, ValueError, RecursionError) as exc:
            raise ValueError(f"cannot scan {relative}: {exc}") from exc
        ast_nodes = sum(1 for _ in ast.walk(tree))
        if ast_nodes > MAX_AST_NODES:
            raise ValueError(f"cannot scan {relative}: exceeds {MAX_AST_NODES} AST nodes")
        root.resource_meter.claim_ast_nodes(ast_nodes)
        module_observations = scan_module(
            relative,
            tree,
            source_sha256=digest,
            resource_meter=root.resource_meter,
        )
        observations.extend(module_observations)
    root.assert_path_identity()
    return tuple(sorted(observations))


def _load_manifest_parts(
    root: RepositorySnapshotV2,
) -> tuple[tuple[ValueSinkSpecV2, ...], tuple[ClosureGapV2, ...], list[ClosureFindingV2]]:
    relative_name = f"tools/{MANIFEST_NAME}"
    text, error = root.read_bounded_text(relative_name, MAX_MANIFEST_BYTES)
    if text is None:
        return (), (), [
            ClosureFindingV2(relative_name, "manifest_invalid", error or "unreadable")
        ]
    try:
        document = decode_value_sink_document_text_v2(text)
    except ValueError as exc:
        return (), (), [ClosureFindingV2(relative_name, "manifest_invalid", str(exc))]
    return document.entries, document.closure_gaps, []


def _build_report_from_snapshot(root: RepositorySnapshotV2) -> ValueSinkReportV2:
    specs, declared_gaps, findings = _load_manifest_parts(root)
    manifest_load_failed = bool(findings)
    closure = derive_python_deployment_closure(root)
    findings.extend(closure.findings)
    try:
        observations = scan_closure(root, closure)
    except ValueError as exc:
        observations = ()
        findings.append(ClosureFindingV2("bin", "sink_scan_failed", str(exc)))
    observed_gaps = tuple(sorted(set(closure.observed_gaps) | set(dynamic_destination_gaps(observations))))
    findings.extend(reconcile_closure_gaps(observed_gaps, declared_gaps))
    inventory_findings = compare_inventory(
        specs, observations, frozenset(closure.modules)
    )
    findings.extend(inventory_findings)
    findings.extend(unresolved_destination_adjudication_findings(specs, observations))
    findings.extend(uncertified_mediation_findings(specs))
    findings.extend(consumer_binding_findings(root, closure, specs, observations))
    findings.sort()
    unmediated = sorted(
        spec.sink_id for spec in specs if spec.mediation_status == "UNMEDIATED_DEPLOYED_WRITER"
    )
    unadjudicated = sorted(
        spec.sink_id for spec in specs if spec.classification == UNADJUDICATED
    )
    # Every research row is release-unbound by construction, so the gap list
    # covers all of them and no classification can shrink it to nothing.
    release_gaps = sorted(spec.sink_id for spec in specs if spec.release_binding is None)
    closure_complete = not (
        findings
        or observed_gaps
        or declared_gaps
        or closure.unscanned_modules
        or unadjudicated
        or unmediated
        or release_gaps
    )
    return {
        "adjudicated_identity_count": len(specs) - len(unadjudicated),
        "declared_closure_gaps": [gap.to_dict() for gap in declared_gaps],
        "manifest_identity_count": len(specs),
        "decoded_launchers": [entrypoint.to_dict() for entrypoint in closure.entrypoints],
        "findings": [finding.to_dict() for finding in findings],
        "scanner_relative_manifest_agreement": not manifest_load_failed
        and not inventory_findings,
        "closure_complete": closure_complete,
        "nonclaims": list(NONCLAIMS),
        "observed_occurrence_count": len(observations),
        # Schema v2 is a research inventory. No manifest content can promote it,
        # so these are constants rather than computed verdicts.
        "production_authority": False,
        "p2_t01_status": "OPEN",
        "p2_t02_status": "OPEN",
        "release_gaps": release_gaps,
        "release_ready": False,
        "schema": SCHEMA_V2,
        "sinks": [spec.to_dict() for spec in specs],
        "static_reachable_unscanned_modules": list(closure.unscanned_modules),
        "static_scanned_module_count": len(closure.modules),
        "static_scanned_module_digests": [
            {"path": path, "sha256": digest} for path, digest in closure.module_digests
        ],
        "unadjudicated_sinks": unadjudicated,
        "unmediated_static_writers": unmediated,
        "vm01_status": "OPEN",
    }


def _red_failure_report(rule_id: str, evidence: str) -> ValueSinkReportV2:
    finding = ClosureFindingV2(".", rule_id, evidence)
    return {
        "adjudicated_identity_count": 0,
        "declared_closure_gaps": [],
        "decoded_launchers": [],
        "findings": [finding.to_dict()],
        "scanner_relative_manifest_agreement": False,
        "closure_complete": False,
        "manifest_identity_count": 0,
        "nonclaims": list(NONCLAIMS),
        "observed_occurrence_count": 0,
        "production_authority": False,
        "p2_t01_status": "OPEN",
        "p2_t02_status": "OPEN",
        "release_gaps": [],
        "release_ready": False,
        "schema": SCHEMA_V2,
        "sinks": [],
        "static_reachable_unscanned_modules": [],
        "static_scanned_module_count": 0,
        "static_scanned_module_digests": [],
        "unadjudicated_sinks": [],
        "unmediated_static_writers": [],
        "vm01_status": "OPEN",
    }


def _root_failure_report(detail: str) -> ValueSinkReportV2:
    return _red_failure_report("repository_snapshot_changed", detail)


def build_report(
    root: Path,
    *,
    resource_limits: ScanResourceLimitsV2 = DEFAULT_SCAN_RESOURCE_LIMITS_V2,
) -> ValueSinkReportV2:
    """Assemble one report from a single descriptor-backed subject snapshot."""

    try:
        with RepositorySnapshotV2(root, resource_limits=resource_limits) as snapshot:
            try:
                report = _build_report_from_snapshot(snapshot)
                snapshot.verify_stable()
            except RepositorySnapshotChanged as exc:
                return _root_failure_report(str(exc))
            return report
    except ResourceBudgetExceeded as exc:
        return _red_failure_report("resource_budget_exceeded", str(exc))
    except (MemoryError, OSError) as exc:
        return _red_failure_report("scanner_resource_failure", type(exc).__name__)
    except SystemError as exc:
        return _red_failure_report("scanner_internal_failure", type(exc).__name__)
    except ValueError as exc:
        return _root_failure_report(str(exc))


def _owned_value_shell_v2(
    value: object, seen_containers: set[int]
) -> tuple[object, tuple[object, object] | None] | None:
    """Copy a scalar or allocate one exact container shell without callbacks."""

    if type(value) is dict:
        identity = id(value)
        if identity in seen_containers:
            return None
        seen_containers.add(identity)
        owned: object = {}
        return owned, (value, owned)
    if type(value) is list:
        identity = id(value)
        if identity in seen_containers:
            return None
        seen_containers.add(identity)
        owned = []
        return owned, (value, owned)
    if type(value) in {str, int, bool, type(None)}:
        return value, None
    return None


def _snapshot_exact_builtin_report_v2(report: object) -> dict[str, object] | None:
    """Take a bounded callback-free copy of one exact built-in report tree."""

    if type(report) is not dict:
        return None
    owned_root: dict[str, object] = {}
    stack: list[tuple[object, object]] = [(report, owned_root)]
    seen_containers: set[int] = {id(report)}
    nodes = 1
    try:
        while stack:
            source, target = stack.pop()
            if type(source) is dict and type(target) is dict:
                source_dict = cast(dict[object, object], source)
                target_dict = cast(dict[str, object], target)
                dict_items = list(dict.items(source_dict))
                if len(dict_items) > MAX_REPORT_LIST_ITEMS_V2 or len(
                    dict_items
                ) > MAX_REPORT_VALUE_NODES_V2 - nodes:
                    return None
                nodes += len(dict_items)
                for key, child in dict_items:
                    if type(key) is not str:
                        return None
                    shell = _owned_value_shell_v2(child, seen_containers)
                    if shell is None:
                        return None
                    owned_child, pending = shell
                    target_dict[key] = owned_child
                    if pending is not None:
                        stack.append(pending)
            elif type(source) is list and type(target) is list:
                source_list = cast(list[object], source)
                target_list = cast(list[object], target)
                list_items = list(source_list)
                if len(list_items) > MAX_REPORT_LIST_ITEMS_V2 or len(
                    list_items
                ) > MAX_REPORT_VALUE_NODES_V2 - nodes:
                    return None
                nodes += len(list_items)
                for child in list_items:
                    shell = _owned_value_shell_v2(child, seen_containers)
                    if shell is None:
                        return None
                    owned_child, pending = shell
                    target_list.append(owned_child)
                    if pending is not None:
                        stack.append(pending)
            else:
                return None
    except (MemoryError, RuntimeError, SystemError):
        return None
    return owned_root


def _exact_owned_report_v2(report: object) -> dict[str, object] | None:
    """Accept only the closed, bounded, ordinary-data report shape."""

    owned_root = _snapshot_exact_builtin_report_v2(report)
    if owned_root is None or frozenset(owned_root) != REPORT_FIELDS_V2:
        return None
    owned = cast(dict[str, Any], owned_root)
    integer_fields = (
        "adjudicated_identity_count",
        "manifest_identity_count",
        "observed_occurrence_count",
        "static_scanned_module_count",
    )
    if any(type(owned[field]) is not int or owned[field] < 0 for field in integer_fields):
        return None
    boolean_fields = (
        "scanner_relative_manifest_agreement",
        "closure_complete",
        "production_authority",
        "release_ready",
    )
    if any(type(owned[field]) is not bool for field in boolean_fields):
        return None
    if (
        owned["schema"] != SCHEMA_V2
        or owned["production_authority"] is not False
        or owned["release_ready"] is not False
        or owned["vm01_status"] != "OPEN"
        or owned["p2_t01_status"] != "OPEN"
        or owned["p2_t02_status"] != "OPEN"
    ):
        return None
    list_fields = REPORT_FIELDS_V2 - frozenset(integer_fields) - frozenset(boolean_fields) - {
        "schema",
        "vm01_status",
        "p2_t01_status",
        "p2_t02_status",
    }
    if any(type(owned[field]) is not list for field in list_fields):
        return None
    for field, expected in REPORT_ROW_FIELDS_V2.items():
        for row in owned[field]:
            if type(row) is not dict or frozenset(row) != expected or any(
                type(value) is not str for value in row.values()
            ):
                return None
    for field in (
        "nonclaims",
        "release_gaps",
        "static_reachable_unscanned_modules",
        "unadjudicated_sinks",
        "unmediated_static_writers",
    ):
        if any(type(value) is not str for value in owned[field]):
            return None
    for sink in owned["sinks"]:
        if type(sink) is not dict or frozenset(sink) != SINK_REPORT_FIELDS_V2:
            return None
        if (
            type(sink["consumers"]) is not list
            or type(sink["deployed_reachable"]) is not bool
            or type(sink["occurrence_count"]) is not int
            or sink["occurrence_count"] < 0
            or sink["release_binding"] is not None
            or any(
                type(sink[field]) is not str
                for field in SINK_REPORT_FIELDS_V2
                - {"consumers", "deployed_reachable", "occurrence_count", "release_binding"}
            )
        ):
            return None
        for consumer in sink["consumers"]:
            if (
                type(consumer) is not dict
                or frozenset(consumer) != CONSUMER_REPORT_FIELDS_V2
                or any(type(value) is not str for value in consumer.values())
            ):
                return None
    if (
        owned["manifest_identity_count"] != len(owned["sinks"])
        or owned["static_scanned_module_count"]
        != len(owned["static_scanned_module_digests"])
        or owned["adjudicated_identity_count"]
        != owned["manifest_identity_count"] - len(owned["unadjudicated_sinks"])
    ):
        return None
    return owned_root


def gate_blockers(report: object) -> tuple[str, ...]:
    """List every reason the default gate must exit nonzero.

    The inventory is complete only when nothing is unclassified, nothing is
    unscanned, no incompleteness is declared, and every value-affecting writer
    is both mediated and release-bound. None of those hold today.
    """

    owned = _exact_owned_report_v2(report)
    if owned is None:
        return ("report_invalid",)
    blockers = [
        name
        for name in (
            "findings",
            "declared_closure_gaps",
            "static_reachable_unscanned_modules",
            "unadjudicated_sinks",
            "unmediated_static_writers",
            "release_gaps",
        )
        if owned[name]
    ]
    blockers.extend(
        name
        for name, blocked in (
            ("scanner_relative_manifest_disagreement", not owned["scanner_relative_manifest_agreement"]),
            ("closure_incomplete", not owned["closure_complete"]),
            ("production_authority_none", not owned["production_authority"]),
            ("release_not_ready", not owned["release_ready"]),
            ("vm01_open", owned["vm01_status"] == "OPEN"),
            ("p2_t01_open", owned["p2_t01_status"] == "OPEN"),
            ("p2_t02_open", owned["p2_t02_status"] == "OPEN"),
        )
        if blocked
    )
    return tuple(blockers)
