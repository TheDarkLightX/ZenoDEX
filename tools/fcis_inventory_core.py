"""Pure value-movement inventory parsing and classification.

Filesystem discovery belongs to the command-line shell.  This module accepts
owned immutable values and returns deterministically sorted diagnostics.
"""

from __future__ import annotations

import fnmatch
import hashlib
import json
import re
from dataclasses import dataclass
from typing import Mapping, Sequence

SCHEMA = "zenodex/value_movement_inventory/v1"
AUTHORITY_MODES = frozenset(
    {
        "python_authority",
        "rust_shadow",
        "rust_authority_with_python_shadow",
        "rust_authority",
        "unmounted",
    }
)
CBC_GRADES = frozenset({"none", "partial", "full"})
EVIDENCE_STATUSES = frozenset({"absent", "partial", "pass", "blocked"})
ATOMIC_STATUSES = frozenset({"absent", "partial", "complete", "blocked"})

SURFACE_KEYS = frozenset(
    {
        "surface_id",
        "rust_entrypoints",
        "python_shadow_entrypoints",
        "formal_transition_artifacts",
        "state_schema",
        "command_schema",
        "execution_context_schema",
        "effect_schema",
        "receipt_schema",
        "rejection_registry",
        "authority_profiles",
        "invariants",
        "proof_status",
        "differential_status",
        "test_status",
        "atomic_commit_status",
        "audit_cases",
        "direct_callers",
        "commit_path",
        "external_delivery_path",
        "source_patterns",
        "binding_patterns",
        "binding_sha256",
        "cbc_grade",
        "remaining_blockers",
    }
)

MUTATION_PATTERNS = tuple(
    re.compile(pattern, re.IGNORECASE | re.MULTILINE)
    for pattern in (
        r"\b(?:balance|reserve|debt|collateral|position|fee|reward|treasury|"
        r"premium|payout|shares?|supply|funding|pnl)[a-zA-Z0-9_]*\s*(?:\+=|-=|=(?!=))",
        r"\bdef\s+(?:credit|debit|transfer|mint|burn|deposit|withdraw|redeem|"
        r"liquidat[a-zA-Z0-9_]*|claim|payout|settle[a-zA-Z0-9_]*)\b",
        r"\bpub\s+fn\s+(?:credit|debit|transfer|mint|burn|deposit|withdraw|redeem|"
        r"liquidat[a-zA-Z0-9_]*|claim|payout|settle[a-zA-Z0-9_]*)\b",
        r"\b(?:INSERT|UPDATE)\b[^;\n]*(?:balance|reserve|debt|collateral|effect|outbox)",
    )
)


@dataclass(frozen=True, order=True)
class SourceFile:
    path: str
    text: str


@dataclass(frozen=True)
class SurfaceRecord:
    surface_id: str
    rust_entrypoints: tuple[str, ...]
    python_shadow_entrypoints: tuple[str, ...]
    formal_transition_artifacts: tuple[str, ...]
    state_schema: tuple[str, ...]
    command_schema: tuple[str, ...]
    execution_context_schema: tuple[str, ...]
    effect_schema: tuple[str, ...]
    receipt_schema: tuple[str, ...]
    rejection_registry: tuple[str, ...]
    authority_profiles: tuple[tuple[str, str], ...]
    invariants: tuple[str, ...]
    proof_status: str
    differential_status: str
    test_status: str
    atomic_commit_status: str
    audit_cases: tuple[str, ...]
    direct_callers: tuple[str, ...]
    commit_path: tuple[str, ...]
    external_delivery_path: tuple[str, ...]
    source_patterns: tuple[str, ...]
    binding_patterns: tuple[str, ...]
    binding_sha256: str
    cbc_grade: str
    remaining_blockers: tuple[str, ...]

    def authority_for(self, profile_id: str) -> str:
        return dict(self.authority_profiles).get(profile_id, "unmounted")


@dataclass(frozen=True)
class Inventory:
    scan_roots: tuple[str, ...]
    surfaces: tuple[SurfaceRecord, ...]


@dataclass(frozen=True, order=True)
class Diagnostic:
    code: str
    path: str
    detail: str


def _string(value: object, *, field: str) -> str:
    if not isinstance(value, str) or not value or value != value.strip():
        raise ValueError(f"{field} must be a non-empty trimmed string")
    return value


def _strings(value: object, *, field: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise TypeError(f"{field} must be a list")
    items = tuple(_string(item, field=field) for item in value)
    if len(items) != len(set(items)):
        raise ValueError(f"{field} must not contain duplicates")
    return items


def parse_inventory(raw: object) -> Inventory:
    if not isinstance(raw, Mapping):
        raise TypeError("inventory must be an object")
    if frozenset(raw) != frozenset({"schema", "scan_roots", "surfaces"}):
        raise ValueError("inventory top-level fields are not the exact v1 field set")
    if raw["schema"] != SCHEMA:
        raise ValueError(f"inventory schema must be {SCHEMA!r}")
    scan_roots = _strings(raw["scan_roots"], field="scan_roots")
    raw_surfaces = raw["surfaces"]
    if not isinstance(raw_surfaces, list):
        raise TypeError("surfaces must be a list")
    surfaces = tuple(
        sorted(
            (_parse_surface(item) for item in raw_surfaces),
            key=lambda surface: surface.surface_id,
        )
    )
    ids = tuple(surface.surface_id for surface in surfaces)
    if len(ids) != len(set(ids)):
        raise ValueError("surface_id values must be unique")
    return Inventory(scan_roots=scan_roots, surfaces=surfaces)


def _parse_authority_profiles(raw: object) -> tuple[tuple[str, str], ...]:
    if not isinstance(raw, Mapping):
        raise TypeError("authority_profiles must be an object")
    profiles = tuple(
        sorted(
            (
                _string(key, field="authority_profiles key"),
                _string(value, field="authority_profiles value"),
            )
            for key, value in raw.items()
        )
    )
    invalid_modes = sorted(value for _, value in profiles if value not in AUTHORITY_MODES)
    if invalid_modes:
        raise ValueError(f"unknown authority mode(s): {invalid_modes}")
    return profiles


def _validate_surface_status(record: SurfaceRecord) -> None:
    if record.cbc_grade not in CBC_GRADES:
        raise ValueError(f"unknown cbc_grade {record.cbc_grade!r}")
    for field, value in (
        ("proof_status", record.proof_status),
        ("differential_status", record.differential_status),
        ("test_status", record.test_status),
    ):
        if value not in EVIDENCE_STATUSES:
            raise ValueError(f"unknown {field} {value!r}")
    if record.atomic_commit_status not in ATOMIC_STATUSES:
        raise ValueError(f"unknown atomic_commit_status {record.atomic_commit_status!r}")


def _parse_surface(raw: object) -> SurfaceRecord:
    if not isinstance(raw, Mapping):
        raise TypeError("surface must be an object")
    if frozenset(raw) != SURFACE_KEYS:
        missing = sorted(SURFACE_KEYS - frozenset(raw))
        extra = sorted(frozenset(raw) - SURFACE_KEYS)
        raise ValueError(f"surface fields mismatch: missing={missing}, extra={extra}")
    record = SurfaceRecord(
        surface_id=_string(raw["surface_id"], field="surface_id"),
        rust_entrypoints=_strings(raw["rust_entrypoints"], field="rust_entrypoints"),
        python_shadow_entrypoints=_strings(
            raw["python_shadow_entrypoints"], field="python_shadow_entrypoints"
        ),
        formal_transition_artifacts=_strings(
            raw["formal_transition_artifacts"], field="formal_transition_artifacts"
        ),
        state_schema=_strings(raw["state_schema"], field="state_schema"),
        command_schema=_strings(raw["command_schema"], field="command_schema"),
        execution_context_schema=_strings(
            raw["execution_context_schema"], field="execution_context_schema"
        ),
        effect_schema=_strings(raw["effect_schema"], field="effect_schema"),
        receipt_schema=_strings(raw["receipt_schema"], field="receipt_schema"),
        rejection_registry=_strings(raw["rejection_registry"], field="rejection_registry"),
        authority_profiles=_parse_authority_profiles(raw["authority_profiles"]),
        invariants=_strings(raw["invariants"], field="invariants"),
        proof_status=_string(raw["proof_status"], field="proof_status"),
        differential_status=_string(raw["differential_status"], field="differential_status"),
        test_status=_string(raw["test_status"], field="test_status"),
        atomic_commit_status=_string(raw["atomic_commit_status"], field="atomic_commit_status"),
        audit_cases=_strings(raw["audit_cases"], field="audit_cases"),
        direct_callers=_strings(raw["direct_callers"], field="direct_callers"),
        commit_path=_strings(raw["commit_path"], field="commit_path"),
        external_delivery_path=_strings(
            raw["external_delivery_path"], field="external_delivery_path"
        ),
        source_patterns=_strings(raw["source_patterns"], field="source_patterns"),
        binding_patterns=_strings(raw["binding_patterns"], field="binding_patterns"),
        binding_sha256=_string(raw["binding_sha256"], field="binding_sha256"),
        cbc_grade=_string(raw["cbc_grade"], field="cbc_grade"),
        remaining_blockers=_strings(raw["remaining_blockers"], field="remaining_blockers"),
    )
    _validate_surface_status(record)
    return record


def is_value_movement_candidate(source: SourceFile) -> bool:
    return any(pattern.search(source.text) for pattern in MUTATION_PATTERNS)


def pattern_matches(path: str, patterns: Sequence[str]) -> bool:
    return any(fnmatch.fnmatchcase(path, pattern) for pattern in patterns)


def binding_digest(surface: SurfaceRecord, sources: Sequence[SourceFile]) -> str:
    bound = tuple(
        sorted(
            source for source in sources if pattern_matches(source.path, surface.binding_patterns)
        )
    )
    digest = hashlib.sha256()
    digest.update(b"zenodex/fcis/source-binding/v1\x00")
    for source in bound:
        digest.update(source.path.encode("utf-8"))
        digest.update(b"\x00")
        digest.update(source.text.encode("utf-8"))
        digest.update(b"\x00")
    return digest.hexdigest()


def _classify_candidates(
    inventory: Inventory, candidates: Sequence[SourceFile]
) -> tuple[Diagnostic, ...]:
    diagnostics: list[Diagnostic] = []
    for source in candidates:
        owners = tuple(
            surface.surface_id
            for surface in inventory.surfaces
            if pattern_matches(source.path, surface.source_patterns)
        )
        if not owners:
            diagnostics.append(
                Diagnostic("UNCLASSIFIED_VALUE_PATH", source.path, "no inventory owner")
            )
        elif len(owners) != 1:
            diagnostics.append(
                Diagnostic("AMBIGUOUS_VALUE_PATH", source.path, ",".join(sorted(owners)))
            )
    return tuple(diagnostics)


def _promotion_diagnostics(surface: SurfaceRecord) -> tuple[Diagnostic, ...]:
    diagnostics: list[Diagnostic] = []
    for profile_id, mode in surface.authority_profiles:
        if mode == "rust_authority":
            diagnostics.append(
                Diagnostic("UNSHADOWED_RUST_AUTHORITY", surface.surface_id, profile_id)
            )
        evidence_complete = (
            surface.cbc_grade == "full"
            and surface.proof_status == "pass"
            and surface.differential_status == "pass"
            and surface.test_status == "pass"
        )
        if mode == "rust_authority_with_python_shadow" and not evidence_complete:
            diagnostics.append(
                Diagnostic(
                    "PROMOTED_WITH_INCOMPLETE_EVIDENCE",
                    surface.surface_id,
                    profile_id,
                )
            )
    return tuple(diagnostics)


def _release_complete(surface: SurfaceRecord) -> bool:
    return all(
        (
            surface.cbc_grade == "full",
            surface.proof_status == "pass",
            surface.differential_status == "pass",
            surface.test_status == "pass",
            surface.atomic_commit_status == "complete",
            not surface.remaining_blockers,
            bool(surface.rust_entrypoints),
            bool(surface.formal_transition_artifacts),
            bool(surface.effect_schema),
            bool(surface.receipt_schema),
            bool(surface.external_delivery_path),
        )
    )


def _surface_diagnostics(
    surface: SurfaceRecord,
    source_paths: frozenset[str],
    sources: Sequence[SourceFile],
    *,
    require_release: bool,
) -> tuple[Diagnostic, ...]:
    diagnostics = list(_promotion_diagnostics(surface))
    matched = any(pattern_matches(path, surface.source_patterns) for path in source_paths)
    if not matched and surface.source_patterns:
        diagnostics.append(
            Diagnostic(
                "EMPTY_SOURCE_PATTERN",
                surface.surface_id,
                "source_patterns matched no scanned file",
            )
        )
    actual_digest = binding_digest(surface, sources)
    if surface.binding_sha256 != actual_digest:
        diagnostics.append(
            Diagnostic(
                "STALE_SOURCE_BINDING",
                surface.surface_id,
                f"expected={surface.binding_sha256},actual={actual_digest}",
            )
        )
    if require_release and not _release_complete(surface):
        diagnostics.append(
            Diagnostic(
                "RELEASE_SURFACE_INCOMPLETE",
                surface.surface_id,
                "full Rust/formal/differential/atomic closure absent",
            )
        )
    return tuple(diagnostics)


def validate_inventory(
    inventory: Inventory,
    sources: Sequence[SourceFile],
    *,
    require_release: bool,
) -> tuple[Diagnostic, ...]:
    candidates = tuple(source for source in sources if is_value_movement_candidate(source))
    diagnostics = list(_classify_candidates(inventory, candidates))
    source_paths = frozenset(source.path for source in sources)
    for surface in inventory.surfaces:
        diagnostics.extend(
            _surface_diagnostics(
                surface,
                source_paths,
                sources,
                require_release=require_release,
            )
        )
    return tuple(sorted(diagnostics))


def canonical_report(
    inventory: Inventory,
    sources: Sequence[SourceFile],
    diagnostics: Sequence[Diagnostic],
    *,
    require_release: bool,
) -> str:
    candidates = sorted(source.path for source in sources if is_value_movement_candidate(source))
    payload = {
        "schema": "zenodex/value_movement_inventory_report/v1",
        "claim_status": "released" if require_release and not diagnostics else "blocked",
        "release_check": require_release,
        "surface_count": len(inventory.surfaces),
        "candidate_path_count": len(candidates),
        "candidate_paths": candidates,
        "diagnostics": [
            {"code": item.code, "path": item.path, "detail": item.detail} for item in diagnostics
        ],
        "surface_bindings": {
            surface.surface_id: binding_digest(surface, sources) for surface in inventory.surfaces
        },
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
