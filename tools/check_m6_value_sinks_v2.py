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

Regenerate the manifest atomically with::

    python3 tools/check_m6_value_sinks_v2.py --write-manifest

``--emit-manifest`` remains a read-only preview. Redirecting that preview onto
the source manifest is unsafe because the shell truncates the file before this
process can retain its reviewed classifications.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
# Direct execution as a script leaves the repository root off sys.path.
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.m6_value_sinks import (  # noqa: E402
    MANIFEST_NAME,
    SCHEMA_V2,
    UNADJUDICATED,
    ClosureGapV2,
    build_report,
    combine_fingerprints,
    derive_python_deployment_closure,
    load_closure_gaps,
    load_value_sink_manifest,
    scan_closure,
)


def check_m6_value_sinks_v2(root: Path = REPO_ROOT) -> dict[str, object]:
    return build_report(root)


def write_manifest_v2(
    root: Path = REPO_ROOT,
    *,
    prior_manifest: Path | None = None,
    prior_manifest_sha256: str | None = None,
) -> dict[str, object]:
    """Render first, then atomically replace the reviewed manifest.

    Newly observed identities remain ``UNADJUDICATED`` and keep the gate closed
    until a reviewer supplies an exact classification.  The existing reviewed
    manifest must decode completely before regeneration begins; malformed prior
    evidence is never replaced by a newly rendered candidate.
    """

    root = root.resolve()
    manifest_path = root / "tools" / MANIFEST_NAME
    prior_path = manifest_path if prior_manifest is None else prior_manifest.resolve()
    if prior_manifest is None and prior_manifest_sha256 is not None:
        raise ValueError("prior_manifest_sha256 requires an explicit prior_manifest")
    if prior_manifest is not None:
        if prior_manifest_sha256 is None:
            raise ValueError("an external prior manifest requires its exact SHA-256")
        try:
            prior_bytes = prior_path.read_bytes()
        except OSError as exc:
            raise ValueError(f"cannot read prior manifest: {exc}") from exc
        actual_digest = hashlib.sha256(prior_bytes).hexdigest()
        if actual_digest != prior_manifest_sha256:
            raise ValueError(
                f"prior manifest SHA-256 mismatch: expected={prior_manifest_sha256}, "
                f"actual={actual_digest}"
            )
    load_value_sink_manifest(prior_path)
    load_closure_gaps(prior_path)
    rendered = render_manifest_v2(root, prior_manifest=prior_path)
    candidate_path = manifest_path.with_name(f".{manifest_path.name}.candidate")
    payload = (json.dumps(rendered, indent=2, sort_keys=True) + "\n").encode("utf-8")
    descriptor = -1
    candidate_created = False
    try:
        descriptor = os.open(
            candidate_path,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0),
            0o600,
        )
        candidate_created = True
        with os.fdopen(descriptor, "wb") as candidate:
            descriptor = -1
            candidate.write(payload)
            candidate.flush()
            os.fchmod(candidate.fileno(), 0o644)
            os.fsync(candidate.fileno())
        os.replace(candidate_path, manifest_path)
        candidate_created = False
        directory_fd = os.open(
            manifest_path.parent,
            os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
        )
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        if candidate_created:
            try:
                candidate_path.unlink()
            except FileNotFoundError:
                pass
    return rendered


def render_manifest_v2(
    root: Path = REPO_ROOT, *, prior_manifest: Path | None = None
) -> dict[str, object]:
    """Render the manifest for the current observation set.

    An identity already adjudicated keeps its recorded judgement and receives the
    freshly observed fingerprint only when the reviewer confirms it.  A new
    identity is emitted as ``UNADJUDICATED``, which no enum accepts, so the
    manifest fails to load until a reviewer classifies the sink by hand.
    """

    root = root.resolve()
    manifest_path = root / "tools" / MANIFEST_NAME
    prior_path = manifest_path if prior_manifest is None else prior_manifest.resolve()
    closure = derive_python_deployment_closure(root)
    observations = scan_closure(root, closure)
    try:
        existing = {spec.identity(): spec for spec in load_value_sink_manifest(prior_path)}
    except ValueError:
        existing = {}
    scanned = frozenset(closure.modules)
    grouped: dict[tuple[str, str, str], list[str]] = {}
    for observation in observations:
        grouped.setdefault(observation.identity(), []).append(observation.fingerprint)
    entries = [
        _render_entry(identity, tuple(fingerprints), existing.get(identity), scanned)
        for identity, fingerprints in sorted(grouped.items())
    ]
    return {
        "closure_gaps": _render_gaps(closure.observed_gaps, prior_path),
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
    prior: object,
    scanned: frozenset[str],
) -> dict[str, object]:
    path, symbol, kind = identity
    known = prior is not None
    return {
        "classification": getattr(prior, "classification", UNADJUDICATED),
        "consumers": list(getattr(prior, "consumers", ())),
        "deployed_reachable": path in scanned,
        "identity_fingerprint": combine_fingerprints(fingerprints),
        "mediation_status": getattr(prior, "mediation_status", UNADJUDICATED),
        "occurrence_count": len(fingerprints),
        "path": path,
        "rationale": getattr(prior, "rationale", UNADJUDICATED),
        "release_binding": None,
        "sink_id": getattr(prior, "sink_id", f"{UNADJUDICATED}:{path}:{symbol}:{kind}")
        if known
        else f"{UNADJUDICATED}:{path}:{symbol}:{kind}",
        "sink_kind": kind,
        "symbol": symbol,
    }


def _render_gaps(
    observed: tuple[tuple[str, str], ...], manifest_path: Path
) -> list[dict[str, str]]:
    try:
        prior = {gap.identity(): gap for gap in load_closure_gaps(manifest_path)}
    except ValueError:
        prior = {}
    return [
        (
            prior[identity]
            if identity in prior
            else ClosureGapV2(identity[0], identity[1], UNADJUDICATED)
        ).to_dict()
        for identity in sorted(observed)
    ]


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
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--prior-manifest", type=Path)
    parser.add_argument("--prior-manifest-sha256")
    parser.add_argument("--require-release-ready", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.emit_manifest and args.write_manifest:
        parser.error("--emit-manifest and --write-manifest are mutually exclusive")
    if (
        args.prior_manifest is not None or args.prior_manifest_sha256 is not None
    ) and not args.write_manifest:
        parser.error("--prior-manifest options require --write-manifest")
    if args.emit_manifest:
        print(json.dumps(render_manifest_v2(args.root), indent=2, sort_keys=True))
        return 0
    if args.write_manifest:
        write_manifest_v2(
            args.root,
            prior_manifest=args.prior_manifest,
            prior_manifest_sha256=args.prior_manifest_sha256,
        )
        return 0
    report = check_m6_value_sinks_v2(args.root)
    gate_ok = report["ok"] is True and (
        not args.require_release_ready or report["release_ready"] is True
    )
    if args.json or not gate_ok:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            "M6 static-source value sink inventory ok; "
            f"{report['static_scanned_module_count']} scanned modules, "
            f"{len(_string_list(report, 'unmediated_static_writers'))} unmediated writers, "
            f"{len(report['declared_closure_gaps'])} declared closure gaps; VM-01 remains OPEN"  # type: ignore[arg-type]
        )
    return 0 if gate_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
