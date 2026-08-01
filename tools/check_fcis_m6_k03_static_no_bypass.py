"""Syntax-aware K03 static no-bypass checker for the FCIS M6 core slice.

Python sources are parsed with ``ast``. Rust sources use a comment/string-aware
tokenizer so imports and calls are checked as tokens rather than by a regular
expression over raw bytes. The current M6 checkout has no Rust M6 publisher
path in the protected set; that absence is reported explicitly.
"""

from __future__ import annotations

import ast
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Final, cast

ROOT: Final = Path(__file__).resolve().parents[1]
POLICY_PATH: Final = Path("config/deploy/fcis_m6_k03_static_no_bypass_policy_v1.json")
SCHEMA: Final = "zenodex/fcis/m6/k03/static-no-bypass/v1"


class K03PolicyError(ValueError):
    """Raised for a malformed K03 policy."""


@dataclass(frozen=True, slots=True)
class K03PolicyV1:
    unique_port_module: str
    python_protected_paths: tuple[str, ...]
    rust_protected_paths: tuple[str, ...]
    forbidden_core_imports: frozenset[str]
    forbidden_python_calls: frozenset[str]
    forbidden_rust_modules: frozenset[str]
    forbidden_rust_calls: frozenset[str]
    legacy_publisher_calls: frozenset[str]
    legacy_allowed_paths: frozenset[str]
    authoritative_constructor_calls: frozenset[str]
    authoritative_allowed_paths: frozenset[str]
    direct_writer_sql_markers: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class K03TokenV1:
    text: str
    line: int


def _text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise K03PolicyError(f"{name} must be a nonempty string")
    return value


def _path_list(value: object, name: str, *, allow_empty: bool = False) -> tuple[str, ...]:
    if type(value) is not list or any(type(item) is not str or not item for item in value):
        raise K03PolicyError(f"{name} must be a list of nonempty strings")
    if not allow_empty and not value:
        raise K03PolicyError(f"{name} must be nonempty")
    paths = tuple(cast(str, item) for item in value)
    if len(set(paths)) != len(paths):
        raise K03PolicyError(f"{name} contains duplicates")
    if paths != tuple(sorted(paths, key=lambda item: item.encode("utf-8"))):
        raise K03PolicyError(f"{name} is not canonically ordered")
    return paths


def _string_set(value: object, name: str) -> frozenset[str]:
    return frozenset(_path_list(value, name))


def load_policy(path: Path = ROOT / POLICY_PATH) -> K03PolicyV1:
    """Load the exact closed K03 policy configuration."""

    value = json.loads(path.read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise K03PolicyError("K03 policy must be an object")
    raw = cast(dict[str, object], value)
    expected = {
        "schema",
        "profile_id",
        "unique_port_module",
        "python_protected_paths",
        "rust_protected_paths",
        "forbidden_core_imports",
        "forbidden_python_calls",
        "forbidden_rust_modules",
        "forbidden_rust_calls",
        "legacy_publisher_calls",
        "legacy_allowed_paths",
        "authoritative_constructor_calls",
        "authoritative_allowed_paths",
        "direct_writer_sql_markers",
        "nonclaims",
    }
    if set(raw) != expected:
        raise K03PolicyError("K03 policy fields are not exact")
    if raw["schema"] != "zenodex/fcis/m6/k03/static-no-bypass-policy/v1":
        raise K03PolicyError("K03 policy schema is wrong")
    _text(raw["profile_id"], "profile_id")
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or any(type(item) is not str or not item for item in nonclaims)
    ):
        raise K03PolicyError("nonclaims must be a nonempty string list")
    markers = _path_list(raw["direct_writer_sql_markers"], "direct_writer_sql_markers")
    return K03PolicyV1(
        unique_port_module=_text(raw["unique_port_module"], "unique_port_module"),
        python_protected_paths=_path_list(raw["python_protected_paths"], "python_protected_paths"),
        rust_protected_paths=_path_list(
            raw["rust_protected_paths"], "rust_protected_paths", allow_empty=True
        ),
        forbidden_core_imports=_string_set(raw["forbidden_core_imports"], "forbidden_core_imports"),
        forbidden_python_calls=_string_set(raw["forbidden_python_calls"], "forbidden_python_calls"),
        forbidden_rust_modules=_string_set(raw["forbidden_rust_modules"], "forbidden_rust_modules"),
        forbidden_rust_calls=_string_set(raw["forbidden_rust_calls"], "forbidden_rust_calls"),
        legacy_publisher_calls=_string_set(raw["legacy_publisher_calls"], "legacy_publisher_calls"),
        legacy_allowed_paths=_string_set(raw["legacy_allowed_paths"], "legacy_allowed_paths"),
        authoritative_constructor_calls=_string_set(
            raw["authoritative_constructor_calls"], "authoritative_constructor_calls"
        ),
        authoritative_allowed_paths=_string_set(
            raw["authoritative_allowed_paths"], "authoritative_allowed_paths"
        ),
        direct_writer_sql_markers=markers,
    )


def _issue(path: str, line: int, kind: str, detail: str) -> dict[str, object]:
    return {"path": path, "line": line, "kind": kind, "detail": detail}


def _call_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def _import_root(node: ast.Import | ast.ImportFrom) -> str:
    if isinstance(node, ast.Import):
        return node.names[0].name.split(".")[0]
    if node.level:
        return ""
    return (node.module or "").split(".")[0]


def scan_python_source(
    source: str, relative_path: str, policy: K03PolicyV1
) -> list[dict[str, object]]:
    """Scan one Python source with syntax-aware AST rules."""

    try:
        tree = ast.parse(source, filename=relative_path)
    except SyntaxError as exc:
        return [_issue(relative_path, int(exc.lineno or 0), "syntax_error", str(exc))]
    issues: list[dict[str, object]] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            root = _import_root(node)
            if root in policy.forbidden_core_imports:
                issues.append(
                    _issue(
                        relative_path,
                        int(getattr(node, "lineno", 0)),
                        "forbidden_core_import",
                        root,
                    )
                )
        elif isinstance(node, ast.Call):
            name = _call_name(node.func)
            if name is None:
                continue
            if name in policy.forbidden_python_calls:
                issues.append(
                    _issue(
                        relative_path,
                        int(getattr(node, "lineno", 0)),
                        "forbidden_direct_effect_call",
                        name,
                    )
                )
            if (
                name in policy.legacy_publisher_calls
                and relative_path not in policy.legacy_allowed_paths
            ):
                issues.append(
                    _issue(
                        relative_path,
                        int(getattr(node, "lineno", 0)),
                        "legacy_publisher_call",
                        name,
                    )
                )
            if (
                name in policy.authoritative_constructor_calls
                and relative_path not in policy.authoritative_allowed_paths
            ):
                issues.append(
                    _issue(
                        relative_path,
                        int(getattr(node, "lineno", 0)),
                        "direct_authoritative_constructor",
                        name,
                    )
                )
            if name == "publish_v1" and relative_path != policy.unique_port_module:
                issues.append(
                    _issue(
                        relative_path,
                        int(getattr(node, "lineno", 0)),
                        "direct_publication_port_bypass",
                        name,
                    )
                )
        elif isinstance(node, ast.Constant) and type(node.value) is str:
            upper = node.value.upper()
            for marker in policy.direct_writer_sql_markers:
                if marker in upper:
                    issues.append(
                        _issue(
                            relative_path,
                            int(getattr(node, "lineno", 0)),
                            "protected_table_write_literal",
                            marker,
                        )
                    )
                    break
    return issues


def _rust_tokens(source: str) -> tuple[K03TokenV1, ...]:
    """Tokenize Rust identifiers/punctuation while skipping comments/strings."""

    tokens: list[K03TokenV1] = []
    index = 0
    line = 1
    length = len(source)
    while index < length:
        character = source[index]
        if character in " \t\r":
            index += 1
            continue
        if character == "\n":
            line += 1
            index += 1
            continue
        if source.startswith("//", index):
            newline = source.find("\n", index + 2)
            if newline == -1:
                break
            line += 1
            index = newline + 1
            continue
        if source.startswith("/*", index):
            end = source.find("*/", index + 2)
            if end == -1:
                break
            line += source[index:end].count("\n")
            index = end + 2
            continue
        if character in {'"', "'"}:
            quote = character
            index += 1
            while index < length:
                if source[index] == "\\":
                    index += 2
                    continue
                if source[index] == quote:
                    index += 1
                    break
                if source[index] == "\n":
                    line += 1
                index += 1
            continue
        if character.isalpha() or character == "_":
            start = index
            index += 1
            while index < length and (source[index].isalnum() or source[index] == "_"):
                index += 1
            tokens.append(K03TokenV1(source[start:index], line))
            continue
        if source.startswith("::", index):
            tokens.append(K03TokenV1("::", line))
            index += 2
            continue
        tokens.append(K03TokenV1(character, line))
        index += 1
    return tuple(tokens)


def scan_rust_source(
    source: str, relative_path: str, policy: K03PolicyV1
) -> list[dict[str, object]]:
    """Scan Rust tokens for forbidden imports and direct effect calls."""

    tokens = _rust_tokens(source)
    issues: list[dict[str, object]] = []
    for index, token in enumerate(tokens):
        if token.text == "use":
            path_tokens: list[str] = []
            cursor = index + 1
            while cursor < len(tokens) and tokens[cursor].text != ";":
                path_tokens.append(tokens[cursor].text)
                cursor += 1
            if path_tokens:
                joined_path = "".join(path_tokens)
                for forbidden_module in policy.forbidden_rust_modules:
                    if joined_path == forbidden_module or joined_path.startswith(
                        forbidden_module + "::"
                    ):
                        issues.append(
                            _issue(
                                relative_path,
                                token.line,
                                "forbidden_rust_import",
                                forbidden_module,
                            )
                        )
                        break
        if index + 1 < len(tokens) and tokens[index + 1].text == "(":
            if token.text in policy.forbidden_rust_calls:
                issues.append(
                    _issue(relative_path, token.line, "forbidden_rust_effect_call", token.text)
                )
    return issues


def _read_source(root: Path, relative_path: str) -> str:
    path = (root / relative_path).resolve()
    try:
        path.relative_to(root.resolve())
    except ValueError as exc:
        raise K03PolicyError(f"protected path escapes root: {relative_path}") from exc
    return path.read_text(encoding="utf-8")


def run_static_scan(root: Path = ROOT, policy: K03PolicyV1 | None = None) -> dict[str, object]:
    """Run the configured Python and Rust protected-source scan."""

    exact_policy = policy or load_policy(root / POLICY_PATH)
    issues: list[dict[str, object]] = []
    python_count = 0
    rust_count = 0
    for relative_path in exact_policy.python_protected_paths:
        path = root / relative_path
        if not path.is_file():
            issues.append(_issue(relative_path, 0, "missing_protected_source", relative_path))
            continue
        python_count += 1
        issues.extend(
            scan_python_source(path.read_text(encoding="utf-8"), relative_path, exact_policy)
        )
    for relative_path in exact_policy.rust_protected_paths:
        path = root / relative_path
        if not path.is_file():
            issues.append(_issue(relative_path, 0, "missing_protected_source", relative_path))
            continue
        rust_count += 1
        issues.extend(
            scan_rust_source(path.read_text(encoding="utf-8"), relative_path, exact_policy)
        )
    issues.sort(
        key=lambda item: (str(item["path"]), int(cast(int, item["line"])), str(item["kind"]))
    )
    return {
        "schema": SCHEMA,
        "ok": not issues,
        "python_checked_file_count": python_count,
        "rust_checked_file_count": rust_count,
        "rust_scope_status": "unmounted_no_m6_rust_publisher" if rust_count == 0 else "checked",
        "issues": issues,
        "nonclaims": [
            "The scan covers only the protected source paths named by the reviewed policy.",
            "It does not prove deployment reachability, complete call-graph closure, or datastore authority.",
            "No production value movement is authorized by a passing scan.",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    _ = argv
    report = run_static_scan()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
