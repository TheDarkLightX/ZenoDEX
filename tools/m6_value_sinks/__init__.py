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
    ClosureFindingV2,
    DeployedEntrypointV2,
    canonical_relative_path,
    classify_unscannable_candidate,
    derive_deployed_entrypoints,
)
from tools.m6_value_sinks.manifest import (
    SCHEMA_V2,
    UNADJUDICATED,
    ClosureGapV2,
    ValueSinkSpecV2,
    load_closure_gaps,
    load_value_sink_manifest,
)
from tools.m6_value_sinks.operations import SINK_KINDS, combine_fingerprints
from tools.m6_value_sinks.report import (
    MANIFEST_NAME,
    NONCLAIMS,
    build_report,
    compare_inventory,
    reconcile_closure_gaps,
    scan_closure,
)
from tools.m6_value_sinks.scanner import ValueSinkObservationV2, scan_module

__all__ = [
    "ClosureFindingV2",
    "ClosureGapV2",
    "DeployedEntrypointV2",
    "DeploymentClosureV2",
    "MANIFEST_NAME",
    "NONCLAIMS",
    "SCHEMA_V2",
    "SINK_KINDS",
    "UNADJUDICATED",
    "ValueSinkObservationV2",
    "ValueSinkSpecV2",
    "build_report",
    "canonical_relative_path",
    "classify_unscannable_candidate",
    "combine_fingerprints",
    "compare_inventory",
    "derive_deployed_entrypoints",
    "derive_python_deployment_closure",
    "load_closure_gaps",
    "load_value_sink_manifest",
    "reconcile_closure_gaps",
    "resolve_module",
    "resolve_module_candidate",
    "scan_closure",
    "scan_module",
]
