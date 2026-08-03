"""Build the source-bound K07 deployment-boundary audit vector."""

from __future__ import annotations

import ast
import json
import sys
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.fcis_m6_k07_deployment_audit import (  # noqa: E402
    K07AuditStatusV1,
    K07DeploymentAuditV1,
    K07FindingKindV1,
    K07FindingV1,
    K07LaunchBindingV1,
    _mint_deployment_audit_v1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.build_fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    build_payload as build_k01_payload,
)
from tools.build_fcis_m6_k04_topology_anchor import (  # noqa: E402
    build_payload as build_k04_payload,
)
from tools.build_fcis_m6_k06_legacy_seal import (  # noqa: E402
    build_payload as build_k06_payload,
)

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_k07_deployment_audit_v1.json")
DEFAULT_OUTPUT_PATH = Path("docs/research/m6_tasks/TASK_K07_DEPLOYMENT_AUDIT_V1.json")
K01_CONFIG_PATH = Path("config/deploy/fcis_m6_k01_entrypoint_inventory_v1.json")


class K07BuildError(ValueError):
    """Raised when K07 inputs or expected findings are malformed."""


class _DuplicateKey(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateKey(key)
        result[key] = value
    return result


def _read_json(path: Path) -> dict[str, object]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object)
    except (OSError, UnicodeError, json.JSONDecodeError, _DuplicateKey) as exc:
        raise K07BuildError(f"strict JSON load failed for {path}") from exc
    if type(value) is not dict:
        raise K07BuildError(f"JSON root is not an object: {path}")
    return cast(dict[str, object], value)


def _text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise K07BuildError(f"{name} must be a nonempty string")
    return value


def _path(value: object, name: str) -> str:
    checked = _text(value, name)
    if "\\" in checked or checked.startswith("/") or ".." in checked.split("/"):
        raise K07BuildError(f"{name} is not a safe repository-relative path")
    if any(part in {"", "."} for part in checked.split("/")):
        raise K07BuildError(f"{name} is not canonical")
    return checked


def _digest(value: object, name: str) -> str:
    checked = _text(value, name)
    if (
        len(checked) != 64
        or checked != checked.lower()
        or any(character not in "0123456789abcdef" for character in checked)
    ):
        raise K07BuildError(f"{name} must be a lowercase digest")
    return checked


def _sorted_strings(value: object, name: str) -> tuple[str, ...]:
    if type(value) is not list or not value:
        raise K07BuildError(f"{name} must be a nonempty JSON array")
    checked = tuple(_text(item, f"{name}[{index}]") for index, item in enumerate(value))
    if len(set(checked)) != len(checked):
        raise K07BuildError(f"{name} contains duplicates")
    if checked != tuple(sorted(checked, key=lambda item: item.encode("utf-8"))):
        raise K07BuildError(f"{name} is not canonically ordered")
    return checked


def _load_config(path: Path) -> dict[str, object]:
    raw = _read_json(path)
    expected = {
        "schema",
        "profile_id",
        "k01_vector_path",
        "k04_vector_path",
        "k06_vector_path",
        "expected_k01_entrypoint_inventory_root",
        "expected_k04_topology_root",
        "expected_k06_seal_root",
        "deployment_paths",
        "direct_writer_markers",
        "forbidden_plaintext_markers",
        "required_production_markers",
        "known_launch_bindings",
        "expected_findings",
        "nonclaims",
    }
    if set(raw) != expected:
        raise K07BuildError("K07 config fields are not exact")
    if raw["schema"] != "zenodex/fcis/m6/k07/deployment-audit-config/v1":
        raise K07BuildError("K07 config schema is wrong")
    _text(raw["profile_id"], "profile_id")
    for name in ("k01_vector_path", "k04_vector_path", "k06_vector_path"):
        _path(raw[name], name)
    for name in (
        "expected_k01_entrypoint_inventory_root",
        "expected_k04_topology_root",
        "expected_k06_seal_root",
    ):
        _digest(raw[name], name)
    for name in (
        "deployment_paths",
        "direct_writer_markers",
        "forbidden_plaintext_markers",
        "required_production_markers",
    ):
        _sorted_strings(raw[name], name)
    bindings = raw["known_launch_bindings"]
    if type(bindings) is not list or not bindings:
        raise K07BuildError("known_launch_bindings must be a nonempty list")
    for index, value in enumerate(bindings):
        if type(value) is not dict:
            raise K07BuildError(f"known_launch_bindings[{index}] is not an object")
        row = cast(dict[str, object], value)
        if set(row) != {
            "launcher_id",
            "source_path",
            "command",
            "publisher_id",
            "effect_capable",
        }:
            raise K07BuildError(f"known_launch_bindings[{index}] fields are not exact")
        _text(row["launcher_id"], f"known_launch_bindings[{index}].launcher_id")
        _path(row["source_path"], f"known_launch_bindings[{index}].source_path")
        _text(row["command"], f"known_launch_bindings[{index}].command")
        _text(row["publisher_id"], f"known_launch_bindings[{index}].publisher_id")
        if type(row["effect_capable"]) is not bool:
            raise K07BuildError(f"known_launch_bindings[{index}].effect_capable is not bool")
    expected_findings = raw["expected_findings"]
    if type(expected_findings) is not list:
        raise K07BuildError("expected_findings must be a list")
    for index, value in enumerate(expected_findings):
        if type(value) is not dict:
            raise K07BuildError(f"expected_findings[{index}] is not an object")
        row = cast(dict[str, object], value)
        if set(row) != {"kind", "path", "marker"}:
            raise K07BuildError(f"expected_findings[{index}] fields are not exact")
        try:
            K07FindingKindV1(_text(row["kind"], f"expected_findings[{index}].kind"))
        except ValueError as exc:
            raise K07BuildError(f"expected_findings[{index}] kind is unsupported") from exc
        _path(row["path"], f"expected_findings[{index}].path")
        _text(row["marker"], f"expected_findings[{index}].marker")
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or any(type(item) is not str or not item for item in nonclaims)
    ):
        raise K07BuildError("nonclaims must be a nonempty string list")
    return raw


def _vector(path: Path) -> dict[str, object]:
    return _read_json((ROOT / path).resolve())


def _first_marker_lines(path: str, source: str, markers: tuple[str, ...]) -> list[K07FindingV1]:
    hits: dict[str, int] = {}
    try:
        tree = ast.parse(source, filename=path)
    except SyntaxError as exc:
        return [
            K07FindingV1(
                kind=K07FindingKindV1.MISSING_SOURCE,
                path=path,
                line=max(1, int(exc.lineno or 1)),
                marker="syntax_error",
            )
        ]
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and type(node.value) is str:
            upper = node.value.upper()
            line = int(getattr(node, "lineno", 1))
            for marker in markers:
                if marker.upper() in upper:
                    hits[marker] = min(hits.get(marker, line), line)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            owner = node.func.value
            if (
                node.func.attr == "connect"
                and isinstance(owner, ast.Name)
                and owner.id == "sqlite3"
                and "sqlite3.connect" in markers
            ):
                line = int(getattr(node, "lineno", 1))
                hits["sqlite3.connect"] = min(hits.get("sqlite3.connect", line), line)
    return [
        K07FindingV1(
            kind=K07FindingKindV1.DIRECT_PROTECTED_WRITER,
            path=path,
            line=line,
            marker=marker,
        )
        for marker, line in hits.items()
    ]


def _non_python_marker_lines(
    path: str, source: str, markers: tuple[str, ...]
) -> list[K07FindingV1]:
    hits: dict[str, int] = {}
    for line_number, line in enumerate(source.splitlines(), 1):
        stripped = line.lstrip()
        if stripped.startswith(("#", "//", "/*", "*")):
            continue
        upper = line.upper()
        for marker in markers:
            if marker.upper() in upper:
                hits[marker] = min(hits.get(marker, line_number), line_number)
    return [
        K07FindingV1(
            kind=K07FindingKindV1.DIRECT_PROTECTED_WRITER,
            path=path,
            line=line,
            marker=marker,
        )
        for marker, line in hits.items()
    ]


def _credential_findings(path: str, source: str, markers: tuple[str, ...]) -> list[K07FindingV1]:
    findings: list[K07FindingV1] = []
    for marker in markers:
        for line_number, line in enumerate(source.splitlines(), 1):
            if marker in line:
                findings.append(
                    K07FindingV1(
                        kind=K07FindingKindV1.CREDENTIAL_POLICY_GAP,
                        path=path,
                        line=line_number,
                        marker=marker,
                    )
                )
                break
    return findings


def _binding_rows(value: object) -> tuple[K07LaunchBindingV1, ...]:
    if type(value) is not list:
        raise K07BuildError("known_launch_bindings is not a list")
    bindings = tuple(
        K07LaunchBindingV1(
            launcher_id=_text(cast(dict[str, object], row)["launcher_id"], "launcher_id"),
            source_path=_path(cast(dict[str, object], row)["source_path"], "source_path"),
            command=_text(cast(dict[str, object], row)["command"], "command"),
            publisher_id=_text(cast(dict[str, object], row)["publisher_id"], "publisher_id"),
            effect_capable=cast(bool, cast(dict[str, object], row)["effect_capable"]),
        )
        for row in value
    )
    if bindings != tuple(sorted(bindings, key=lambda item: item.launcher_id.encode("utf-8"))):
        raise K07BuildError("known_launch_bindings are not canonically ordered")
    return bindings


def _expected_keys(value: object) -> tuple[tuple[str, str, str], ...]:
    if type(value) is not list:
        raise K07BuildError("expected_findings is not a list")
    keys: list[tuple[str, str, str]] = []
    for row in value:
        mapping = cast(dict[str, object], row)
        keys.append(
            (
                _text(mapping["kind"], "expected.kind"),
                _path(mapping["path"], "expected.path"),
                _text(mapping["marker"], "expected.marker"),
            )
        )
    return tuple(sorted(set(keys), key=lambda item: (item[1].encode("utf-8"), item[0], item[2])))


def build_audit(config_path: Path = ROOT / DEFAULT_CONFIG_PATH) -> K07DeploymentAuditV1:
    """Regenerate K01/K04/K06 before scanning deployment and source paths."""

    config = _load_config(config_path.resolve())
    k01 = build_k01_payload(ROOT / K01_CONFIG_PATH)
    k04 = build_k04_payload()
    k06 = build_k06_payload()
    if k01["entrypoint_inventory_root"] != config["expected_k01_entrypoint_inventory_root"]:
        raise K07BuildError("K01 root differs from K07 pin")
    if k04["topology_anchor_root"] != config["expected_k04_topology_root"]:
        raise K07BuildError("K04 root differs from K07 pin")
    if k06["seal_root"] != config["expected_k06_seal_root"]:
        raise K07BuildError("K06 seal root differs from K07 pin")

    k01_vector = _vector(Path(_path(config["k01_vector_path"], "k01_vector_path")))
    k04_vector = _vector(Path(_path(config["k04_vector_path"], "k04_vector_path")))
    k06_vector = _vector(Path(_path(config["k06_vector_path"], "k06_vector_path")))
    if canonical_json_bytes(k01) != canonical_json_bytes(k01_vector):
        raise K07BuildError("K01 vector is stale")
    if canonical_json_bytes(k04) != canonical_json_bytes(k04_vector):
        raise K07BuildError("K04 vector is stale")
    if canonical_json_bytes(k06) != canonical_json_bytes(k06_vector):
        raise K07BuildError("K06 vector is stale")

    source_paths_raw = k04.get("source_paths")
    if type(source_paths_raw) is not list:
        raise K07BuildError("K04 source_paths are malformed")
    audited_paths = tuple(
        sorted(
            {_path(item, "K04.source_paths") for item in source_paths_raw},
            key=lambda item: item.encode("utf-8"),
        )
    )
    deployment_paths = _sorted_strings(config["deployment_paths"], "deployment_paths")
    if not set(deployment_paths).issubset(set(audited_paths)):
        raise K07BuildError("deployment paths are not covered by K04")
    direct_markers = _sorted_strings(config["direct_writer_markers"], "direct_writer_markers")
    plaintext_markers = _sorted_strings(
        config["forbidden_plaintext_markers"], "forbidden_plaintext_markers"
    )
    required_markers = _sorted_strings(
        config["required_production_markers"], "required_production_markers"
    )
    findings: list[K07FindingV1] = []
    for path in audited_paths:
        candidate = (ROOT / path).resolve()
        try:
            candidate.relative_to(ROOT)
        except ValueError as exc:
            raise K07BuildError(f"audited path escapes repository: {path}") from exc
        if not candidate.is_file():
            findings.append(K07FindingV1(K07FindingKindV1.MISSING_SOURCE, path, 1, path))
            continue
        source = candidate.read_text(encoding="utf-8")
        if path.endswith(".py"):
            findings.extend(_first_marker_lines(path, source, direct_markers))
        else:
            findings.extend(_non_python_marker_lines(path, source, direct_markers))
    for path in deployment_paths:
        source = (ROOT / path).read_text(encoding="utf-8")
        findings.extend(_credential_findings(path, source, plaintext_markers))
    production_path = "config/deploy/production-strict.yaml"
    production_source = (ROOT / production_path).read_text(encoding="utf-8")
    for marker in required_markers:
        if marker not in production_source:
            findings.append(
                K07FindingV1(
                    K07FindingKindV1.MISSING_REQUIRED_MARKER,
                    production_path,
                    1,
                    marker,
                )
            )

    bindings = _binding_rows(config["known_launch_bindings"])
    for binding in bindings:
        source = (ROOT / binding.source_path).read_text(encoding="utf-8")
        if binding.command not in source:
            findings.append(
                K07FindingV1(
                    K07FindingKindV1.MISSING_LAUNCH_BINDING,
                    binding.source_path,
                    1,
                    binding.command,
                )
            )

    entrypoints = k01.get("entrypoints")
    if type(entrypoints) is not list:
        raise K07BuildError("K01 entrypoints are malformed")
    for index, row in enumerate(entrypoints):
        if type(row) is not dict:
            raise K07BuildError(f"K01 entrypoints[{index}] is malformed")
        kind = row.get("kind")
        if (
            type(kind) is not str
            or "worker" not in kind
            and "migration" not in kind
            and "recovery" not in kind
        ):
            continue
        source_rows = row.get("source_paths")
        if type(source_rows) is not list:
            raise K07BuildError(f"K01 worker source_paths[{index}] is malformed")
        for source_path in source_rows:
            checked_path = _path(source_path, f"K01.entrypoints[{index}].source_paths")
            if checked_path not in audited_paths:
                findings.append(
                    K07FindingV1(
                        K07FindingKindV1.UNTRACKED_WORKER,
                        checked_path,
                        1,
                        _text(row.get("publisher_id"), "publisher_id"),
                    )
                )

    findings_tuple = tuple(sorted(set(findings), key=K07FindingV1.sort_key))
    actual_keys = tuple(
        (finding.kind.value, finding.path, finding.marker) for finding in findings_tuple
    )
    if actual_keys != _expected_keys(config["expected_findings"]):
        raise K07BuildError(
            f"deployment findings differ from the reviewed baseline: {actual_keys!r}"
        )
    status = K07AuditStatusV1.GAP if findings_tuple else K07AuditStatusV1.PASS
    return _mint_deployment_audit_v1(
        k04_topology_root=cast(str, k04["topology_anchor_root"]),
        k06_seal_root=cast(str, k06["seal_root"]),
        k01_entrypoint_inventory_root=cast(str, k01["entrypoint_inventory_root"]),
        audited_paths=audited_paths,
        deployment_paths=deployment_paths,
        launch_bindings=bindings,
        findings=findings_tuple,
        status=status,
    )


def build_payload(config_path: Path = ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    audit = build_audit(config_path)
    return {
        "schema": "zenodex/fcis/m6/k07/deployment-audit-vector/v1",
        "profile_id": "research-unmounted-k07-deployment-boundary",
        "audit": audit.to_wire(),
        "audit_root": audit.audit_root,
        "status": audit.status.value,
        "finding_count": len(audit.findings),
        "finding_kinds": sorted({finding.kind.value for finding in audit.findings}),
        "upstream_roots": {
            "k01_entrypoint_inventory_root": audit.k01_entrypoint_inventory_root,
            "k04_topology_root": audit.k04_topology_root,
            "k06_seal_root": audit.k06_seal_root,
        },
    }


def main(argv: list[str] | None = None) -> int:
    args = list(argv or sys.argv[1:])
    config = ROOT / DEFAULT_CONFIG_PATH
    output = ROOT / DEFAULT_OUTPUT_PATH
    check = False
    index = 0
    while index < len(args):
        token = args[index]
        if token == "--check":
            check = True
        elif token == "--config" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            config = candidate if candidate.is_absolute() else ROOT / candidate
        elif token == "--output" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            output = candidate if candidate.is_absolute() else ROOT / candidate
        else:
            raise SystemExit(f"unknown or incomplete argument: {token}")
        index += 1
    payload = build_payload(config)
    encoded = canonical_json_bytes(payload) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: K07 deployment-audit vector is stale")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)
    print("K07_DEPLOYMENT_AUDIT", payload["status"], payload["audit_root"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
