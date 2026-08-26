#!/usr/bin/env python3
"""Inventory durable-write operations in the statically reachable deployed surface.

Schema v1 fixed its scan root to ``src``.  Every launcher installed by
``scripts/install_zenodex.sh`` and ``bin``, and the container entrypoint, execute
modules outside that root, so the v1 observation set and the deployed writer
surface were disjoint.

V2 derives scope from the operations that install or launch commands, closes it
over static import and dispatch edges, and requires one exact manifest
classification, source-derived operation fingerprint, and consumer trace for
every durable-write operation observed inside that scan.  Edges it cannot
resolve become typed closure gaps.

This is an inventory aid. It does not establish runtime reachability,
cross-language coverage, mediation, sole-publisher closure, or production
authority. VM-01 remains open.

Regenerate the manifest with::

    python3 tools/check_m6_value_sinks_v2.py --emit-manifest --research-emission \\
        > tools/m6_value_sink_manifest_v2.json

The research emitter intentionally exits nonzero. Decode the resulting bytes
with ``load_value_sink_document`` before accepting the generated artifact.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Iterable, Mapping, TypedDict

REPO_ROOT = Path(__file__).resolve().parents[1]
# Direct execution as a script leaves the repository root off sys.path.
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.m6_value_sinks import (  # noqa: E402
    MANIFEST_NAME,
    SCHEMA_V2,
    UNADJUDICATED,
    ClosureGapV2,
    RepositorySnapshotV2,
    ValueSinkReportV2,
    ValueSinkSpecV2,
    build_report,
    combine_fingerprints,
    consumer_binding_findings,
    decode_value_sink_document_text_v2,
    derive_python_deployment_closure,
    dynamic_destination_gaps,
    gate_blockers,
    identity_sink_id_v2,
    scan_closure,
)


class RenderedSinkEntryV2(TypedDict):
    classification: str
    consumers: list[dict[str, str]]
    deployed_reachable: bool
    identity_fingerprint: str
    mediation_status: str
    occurrence_count: int
    path: str
    rationale: str
    release_binding: None
    sink_id: str
    sink_kind: str
    symbol: str


class RenderedClosureGapV2(TypedDict):
    mechanism: str
    path: str
    rationale: str


class RenderedManifestV2(TypedDict):
    closure_gaps: list[RenderedClosureGapV2]
    entries: list[RenderedSinkEntryV2]
    schema: str
    scope: str


def check_m6_value_sinks_v2(root: Path = REPO_ROOT) -> ValueSinkReportV2:
    return build_report(root)


def render_manifest_v2(root: Path = REPO_ROOT) -> RenderedManifestV2:
    """Render the manifest for the current observation set.

    A non-mediated row keeps its recorded judgement only when its fingerprint
    and occurrence count both match exactly. V2 defines no reviewed transitive
    control-dependency certificate, so a prior
    ``MEDIATED_BY_VERIFIED_PUBLISHER`` judgement always resets fail closed.
    Every new, changed, or uncertified mediated row is emitted as
    ``UNADJUDICATED``, an explicit research state that loads and reports rather
    than a guess.  Unadjudicated rows are listed as gate blockers, so the
    generator can never promote a writer it has not had reviewed.
    """

    with RepositorySnapshotV2(root) as snapshot:
        rendered = _render_manifest_from_snapshot(snapshot)
        snapshot.verify_stable()
        return rendered


def _render_manifest_from_snapshot(root: RepositorySnapshotV2) -> RenderedManifestV2:
    closure = derive_python_deployment_closure(root)
    observations = scan_closure(root, closure)
    manifest_text, _ = root.read_bounded_text(f"tools/{MANIFEST_NAME}", 4 * 1024 * 1024)
    try:
        document = (
            decode_value_sink_document_text_v2(manifest_text)
            if manifest_text is not None
            else None
        )
    except ValueError:
        document = None
    existing = {spec.identity(): spec for spec in (document.entries if document else ())}
    scanned = frozenset(closure.modules)
    grouped: dict[tuple[str, str, str], list[str]] = {}
    for observation in observations:
        grouped.setdefault(observation.identity(), []).append(observation.fingerprint)
    unresolved_identities = {
        observation.identity() for observation in observations if not observation.destination_resolved
    }
    invalid_consumer_identities = {
        spec.identity()
        for spec in existing.values()
        if spec.consumers
        and consumer_binding_findings(root, closure, (spec,), observations)
    }
    entries = [
        _render_entry(
            identity,
            tuple(fingerprints),
            existing.get(identity),
            scanned,
            adjudicable=(
                identity not in unresolved_identities
                and identity not in invalid_consumer_identities
            ),
        )
        for identity, fingerprints in sorted(grouped.items())
    ]
    prior_gaps = {gap.identity(): gap for gap in (document.closure_gaps if document else ())}
    observed_gaps = tuple(sorted(set(closure.observed_gaps) | set(dynamic_destination_gaps(observations))))
    return {
        "closure_gaps": _render_gaps(observed_gaps, prior_gaps),
        "entries": entries,
        "schema": SCHEMA_V2,
        "scope": (
            "Durable-write operations observed in the statically reachable Python closure of the "
            "decoded launcher set. Research classification only; no release-backed authority."
        ),
    }


def _render_entry(
    identity: tuple[str, str, str],
    fingerprints: tuple[str, ...],
    prior: ValueSinkSpecV2 | None,
    scanned: frozenset[str],
    *,
    adjudicable: bool,
) -> RenderedSinkEntryV2:
    path, symbol, kind = identity
    fingerprint = combine_fingerprints(fingerprints)
    # A changed fingerprint or count means the writer source moved. Carrying the
    # prior judgement across that change would re-adjudicate it automatically,
    # so the judgement fields reset and a reviewer must classify it again.
    # The writer-local fingerprint cannot bind authorization in a caller,
    # adapter, dispatcher, policy gate, or route. Schema V2 has no reviewed
    # control-dependency certificate field, so preserving a mediated judgement
    # would silently assert transitive authority that this tool did not prove.
    has_preservable_control_basis = (
        prior is not None
        and prior.mediation_status != "MEDIATED_BY_VERIFIED_PUBLISHER"
    )
    unchanged = (
        prior is not None
        and has_preservable_control_basis
        and adjudicable
        and prior.identity_fingerprint == fingerprint
        and prior.occurrence_count == len(fingerprints)
    )
    return {
        "classification": prior.classification if unchanged and prior is not None else UNADJUDICATED,
        # Records must serialize as JSON objects, not dataclass instances.
        "consumers": [record.to_dict() for record in prior.consumers]
        if unchanged and prior is not None
        else [],
        "deployed_reachable": path in scanned,
        "identity_fingerprint": fingerprint,
        "mediation_status": prior.mediation_status if unchanged and prior is not None else UNADJUDICATED,
        "occurrence_count": len(fingerprints),
        "path": path,
        "rationale": prior.rationale if unchanged and prior is not None else UNADJUDICATED,
        "release_binding": None,
        "sink_id": _identity_sink_id(identity),
        "sink_kind": kind,
        "symbol": symbol,
    }


def _identity_sink_id(identity: tuple[str, str, str]) -> str:
    """Derive a collision-resistant identifier bound to the full identity."""

    return identity_sink_id_v2(identity)


# A gap rationale states what this scanner cannot resolve. That is a fact about
# the scanner, not an economic judgement, so regeneration may supply it.
_GAP_RATIONALES: Mapping[str, str] = {
    "__import__": "The module resolves an import target at runtime through __import__, so modules it reaches are outside the static closure and their durable writers are unscanned.",
    "asyncio_subprocess_dispatch": "The module launches a process through asyncio subprocess machinery, so code and durable writers reached by that process are outside this static closure.",
    "ast_node_ceiling_exceeded": "The reachable source exceeds the scanner AST node ceiling, so its durable writers are unscanned.",
    "dispatch_module_absent": "A decoded Python module entrypoint has no contained local implementation, so code selected by the runtime environment is unscanned.",
    "dynamic_destination": "A writer in this module takes its path operand from a caller, and no closed call graph proves the caller set, so the artifact it writes is not fixed by this module.",
    "dynamic_eval": "The module evaluates runtime-selected Python code, so executed durable writers are outside the static closure.",
    "dynamic_exec": "The module executes runtime-selected Python code, so executed durable writers are outside the static closure.",
    "dynamic_import_alias": "The module calls dynamic import machinery through a rebound name, so modules it reaches are outside the static closure.",
    "exec_module": "The module loads code through an explicit loader, so modules it reaches are outside the static closure and their durable writers are unscanned.",
    "import_module": "The module resolves an import target at runtime through importlib.import_module, so modules it reaches are outside the static closure and their durable writers are unscanned.",
    "os_process_dispatch": "The module launches or replaces a process through os process-dispatch machinery, so reached durable writers are unscanned.",
    "runpy_run_module": "The module executes a module through runpy, so its runtime-selected code is outside the static closure.",
    "runpy_run_path": "The module executes a path through runpy, so its runtime-selected code is outside the static closure.",
    "source_unparsable": "The reachable source does not parse under the scanner, so its durable writers are unscanned.",
    "source_unscannable": "The reachable source exceeds the scanner byte ceiling, so its durable writers are unscanned.",
    "unmodelled_container_dispatch": "A container ENTRYPOINT or CMD names an interpreter rather than a script this decoder models, so the code it runs is unscanned.",
    "unmodelled_container_shell_body": "The container script runs commands outside the recognized whole-line Python invocation grammar, so their reach is unscanned.",
    "unmodelled_installer_shell": "The installer is shell code outside this decoder's exact install_wrapper-call grammar; its complete executable semantics remain unmodelled.",
    "unresolved_executable_provenance": "An executable-code callable leaves the scanner's closed direct-call grammar, so code reached through it is unresolved.",
    "unresolved_receiver_writer_provenance": "A proved pathlib writer method escapes the scanner's direct-call grammar, so its operation and destination are unresolved.",
    "unresolved_star_import": "A star import may bind executable or writer names not closed by this scanner, so the imported execution surface is unresolved.",
    "unresolved_subprocess_dispatch": "The module launches a subprocess whose argv the decoder cannot resolve statically, so any durable writer it reaches is unscanned.",
    "unresolved_writer_provenance": "A tracked durable writer escapes the scanner's closed direct-call and simple-alias grammar, so the operation and destination reached through it are unresolved.",
    "unsupported_subprocess_dispatch": "The module launches a fully literal subprocess that is not a recognized Python module or contained script dispatch, so the code it runs is unscanned.",
}


def _render_gaps(
    observed: tuple[tuple[str, str], ...], prior: Mapping[tuple[str, str], ClosureGapV2]
) -> list[RenderedClosureGapV2]:
    rendered: list[RenderedClosureGapV2] = []
    for identity in sorted(observed):
        if identity in prior:
            gap = prior[identity]
            rendered.append(
                RenderedClosureGapV2(
                    mechanism=gap.mechanism,
                    path=gap.path,
                    rationale=gap.rationale,
                )
            )
            continue
        rationale = _GAP_RATIONALES.get(identity[1])
        if identity[1].startswith("installer_source_sha256_"):
            rationale = (
                "The complete installer bytes are bound by this SHA-256 marker; "
                "its shell semantics remain a declared blocking gap."
            )
        if rationale is None and identity[1].startswith(("import_target_", "dispatch_target_", "package_initializer_")):
            rationale = (
                "A lexically local import or dispatch candidate could not be resolved to a regular file "
                "inside the repository root, so the code it reaches is unscanned."
            )
        rendered.append(
            RenderedClosureGapV2(
                mechanism=identity[1],
                path=identity[0],
                rationale=rationale or UNADJUDICATED,
            )
        )
    return rendered


def _string_list(report: Mapping[str, object], key: str) -> tuple[str, ...]:
    value = report[key]
    if not isinstance(value, list):
        return ()
    return tuple(item for item in value if isinstance(item, str))


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--emit-manifest", action="store_true")
    parser.add_argument(
        "--research-emission",
        action="store_true",
        help="emit a manifest despite closure findings or gaps; still exits nonzero",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.emit_manifest:
        return _emit_manifest(args.root, research_emission=args.research_emission)
    report = check_m6_value_sinks_v2(args.root)
    blockers = gate_blockers(report)
    print(json.dumps(report, indent=2, sort_keys=True)) if args.json else print(
        "M6 static-source value sink inventory: "
        "scanner_relative_manifest_agreement="
        f"{report['scanner_relative_manifest_agreement']}, "
        f"closure_complete={report['closure_complete']}, "
        f"{report['static_scanned_module_count']} scanned modules, "
        f"{len(_string_list(report, 'unmediated_static_writers'))} unmediated writers, "
        f"{len(report['declared_closure_gaps'])} declared closure gaps; "
        f"blockers={list(blockers)}; VM-01 remains OPEN"
    )
    # Fail closed by default: anything unclassified, unscanned, declared
    # incomplete, unmediated, or release-unbound keeps the gate red.
    return 0 if not blockers else 1


def _emit_manifest(root: Path, *, research_emission: bool) -> int:
    try:
        rendered = render_manifest_v2(root)
        rendered_text = json.dumps(rendered, indent=2, sort_keys=True)
        decoded = decode_value_sink_document_text_v2(rendered_text)
    except (OSError, ValueError) as exc:
        print(
            json.dumps(
                {
                    "error": "rendered manifest failed production decoding",
                    "detail": str(exc),
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 1
    if decoded.closure_gaps and not research_emission:
        print(
            json.dumps(
                {
                    "error": "closure findings or gaps present; rerun with --research-emission",
                    "observed_gap_count": len(decoded.closure_gaps),
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 1
    print(rendered_text)
    # Every V2 row is release-unbound and the emitter is research-only.  A
    # syntactically valid emission therefore remains a red production gate.
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
