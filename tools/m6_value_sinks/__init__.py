"""Operation-derived value-sink inventory for the deployed ZenoDEX Python surface.

Scope is derived from decoded launchers rather than a declared source root, and
discovery keys on the operation performed rather than on writer names.  The
package is an inventory aid; it is never proof of sole-publisher closure.
"""

from __future__ import annotations

from tools.m6_value_sinks.deployment import (
    DeploymentClosureV2,
    derive_python_deployment_closure,
    resolve_module,
    resolve_module_candidate,
)
from tools.m6_value_sinks.launchers import (
    DEFAULT_SCAN_RESOURCE_LIMITS_V2,
    ClosureFindingV2,
    DeployedEntrypointV2,
    RepositorySnapshotChanged,
    RepositorySnapshotV2,
    ResourceBudgetExceeded,
    ScanResourceLimitsV2,
    ScanResourceMeterV2,
    canonical_relative_path,
    classify_unscannable_candidate,
    derive_deployed_entrypoints,
)
from tools.m6_value_sinks.manifest import (
    SCHEMA_V2,
    UNADJUDICATED,
    ClosureGapV2,
    ValueSinkDocumentV2,
    ValueSinkSpecV2,
    decode_value_sink_document_text_v2,
    identity_sink_id_v2,
    load_closure_gaps,
    load_value_sink_document,
    load_value_sink_manifest,
)
from tools.m6_value_sinks.operations import SINK_KINDS, combine_fingerprints
from tools.m6_value_sinks.report import (
    MANIFEST_NAME,
    NONCLAIMS,
    ValueSinkReportV2,
    build_report,
    compare_inventory,
    consumer_binding_findings,
    dynamic_destination_gaps,
    gate_blockers,
    reconcile_closure_gaps,
    scan_closure,
)
from tools.m6_value_sinks.scanner import ValueSinkObservationV2, scan_module

__all__ = [
    "ClosureFindingV2",
    "ClosureGapV2",
    "DeployedEntrypointV2",
    "DeploymentClosureV2",
    "DEFAULT_SCAN_RESOURCE_LIMITS_V2",
    "MANIFEST_NAME",
    "NONCLAIMS",
    "SCHEMA_V2",
    "SINK_KINDS",
    "UNADJUDICATED",
    "RepositorySnapshotChanged",
    "RepositorySnapshotV2",
    "ResourceBudgetExceeded",
    "ScanResourceLimitsV2",
    "ScanResourceMeterV2",
    "ValueSinkDocumentV2",
    "ValueSinkObservationV2",
    "ValueSinkReportV2",
    "ValueSinkSpecV2",
    "build_report",
    "canonical_relative_path",
    "classify_unscannable_candidate",
    "combine_fingerprints",
    "compare_inventory",
    "consumer_binding_findings",
    "decode_value_sink_document_text_v2",
    "derive_deployed_entrypoints",
    "dynamic_destination_gaps",
    "gate_blockers",
    "identity_sink_id_v2",
    "derive_python_deployment_closure",
    "load_closure_gaps",
    "load_value_sink_document",
    "load_value_sink_manifest",
    "reconcile_closure_gaps",
    "resolve_module",
    "resolve_module_candidate",
    "scan_closure",
    "scan_module",
]
