"""Language-specific operation vocabularies for the O-007B inventory.

The scanners are deliberately conservative lexical or AST observers.  They do
not claim reachability or mediation.  Exact source and observation roots make a
newly introduced operation fail the reviewed manifest until it is inspected.
"""

from __future__ import annotations

import ast
import re
from collections import defaultdict

from tools.m6_cross_language_sinks.model import (
    CrossLanguageObservationV1,
    GeneratedPythonOwnerV1,
    canonical_root,
)
from tools.m6_value_sinks.operations import SINK_KINDS
from tools.m6_value_sinks.scanner import scan_module

RUST_OPERATION_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "RISC0_JOURNAL_COMMIT",
        re.compile(r"\b(?:risc0_zkvm::guest::)?env::commit(?:_slice)?\s*\("),
    ),
    ("RUST_FS_WRITE", re.compile(r"\b(?:std::)?fs::write\s*\(")),
    ("RUST_FS_COPY", re.compile(r"\b(?:std::)?fs::copy\s*\(")),
    ("RUST_FILE_CREATE", re.compile(r"\b(?:std::fs::)?File::create\s*\(")),
    ("RUST_OPEN_OPTIONS", re.compile(r"\bOpenOptions::new\s*\(")),
    (
        "RUST_PATH_MUTATION",
        re.compile(
            r"\b(?:std::)?fs::(?:rename|remove_file|remove_dir|remove_dir_all|"
            r"create_dir|create_dir_all|set_permissions|hard_link)\s*\("
        ),
    ),
    (
        "RUST_DESCRIPTOR_WRITE",
        re.compile(r"\.(?:write|write_all|write_fmt|set_len|sync_all|sync_data)\s*\("),
    ),
    ("RUST_PROCESS_DISPATCH", re.compile(r"\b(?:std::process::)?Command::new\s*\(")),
    (
        "RUST_NETWORK_EFFECT",
        re.compile(r"\b(?:TcpStream|UdpSocket)::(?:connect|bind)\s*\("),
    ),
    (
        "RUST_UNSAFE_OR_FFI_SURFACE",
        re.compile(
            r"\bunsafe\b|\bextern\s+(?:\{|fn\b)|\b(?:libc|nix)::|"
            r"\b(?:asm|global_asm)!\s*\("
        ),
    ),
)

_RUST_FS_FUNCTION_KINDS = {
    "copy": "RUST_FS_COPY",
    "create_dir": "RUST_PATH_MUTATION",
    "create_dir_all": "RUST_PATH_MUTATION",
    "hard_link": "RUST_PATH_MUTATION",
    "remove_dir": "RUST_PATH_MUTATION",
    "remove_dir_all": "RUST_PATH_MUTATION",
    "remove_file": "RUST_PATH_MUTATION",
    "rename": "RUST_PATH_MUTATION",
    "set_permissions": "RUST_PATH_MUTATION",
    "write": "RUST_FS_WRITE",
}
_RUST_FS_USE_RE = re.compile(
    r"\buse\s+(?:std::)?fs::(?P<name>[a-z_][a-z0-9_]*)"
    r"(?:\s+as\s+(?P<alias>[a-zA-Z_][a-zA-Z0-9_]*))?\s*;"
)
_RUST_FS_GROUP_USE_RE = re.compile(r"\buse\s+(?:std::)?fs::\{(?P<body>[^}]*)\}\s*;")
_RUST_FS_GROUP_ITEM_RE = re.compile(
    r"\A\s*(?P<name>[a-z_][a-z0-9_]*)"
    r"(?:\s+as\s+(?P<alias>[a-zA-Z_][a-zA-Z0-9_]*))?\s*\Z"
)

SHELL_OPERATION_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "SHELL_FILE_MUTATION",
        re.compile(
            r"(?:^|[;&|()]\s*)(?:sudo\s+)?(?:install|cp|mv|rm|mkdir|rmdir|touch|"
            r"chmod|chown|ln|tee|dd)\b"
        ),
    ),
    ("SHELL_IN_PLACE_EDIT", re.compile(r"(?:^|[;&|()]\s*)sed\b[^\n]*\s-i(?:\s|$)")),
    (
        "SHELL_SERVICE_MUTATION",
        re.compile(
            r"(?:^|[;&|()]\s*)(?:sudo\s+)?systemctl\s+(?:start|stop|restart|enable|disable)\b"
        ),
    ),
    (
        "SHELL_CONTAINER_MUTATION",
        re.compile(r"(?:^|[;&|()]\s*)(?:docker|podman)\s+(?:run|rm|create|compose|build|push)\b"),
    ),
    (
        "SHELL_NETWORK_EFFECT",
        re.compile(r"(?:^|[;&|()]\s*)(?:curl|wget|nc|netcat)\b"),
    ),
    (
        "SHELL_CROSS_LANGUAGE_DISPATCH",
        re.compile(r"(?:^|[;&|()]\s*)(?:python[0-9.]*|cargo|tau|bash|sh)\b"),
    ),
    (
        "SHELL_DYNAMIC_DISPATCH",
        re.compile(r"(?:^|[;&|()]\s*)(?:eval|source|\.|xargs)\s+|\bfind\b[^\n]*\s-exec\b"),
    ),
)

_SHELL_REDIRECT_RE = re.compile(r"(?<![0-9])(?:>>|>)(?![>&])")
_DOCKER_DIRECTIVE_RE = re.compile(
    r"\A(?P<directive>RUN|COPY|ADD|CMD|ENTRYPOINT)\s+(?P<body>.*)\Z",
    re.IGNORECASE,
)
_TAU_OUTPUT_RE = re.compile(r"\bo(?P<index>[1-9][0-9]*)\[t\]\s*:")
_IR_HASH_RE = re.compile(r"IR hash:\s*sha256:(?P<digest>[0-9a-f]{64})")


def _effect_class(kind: str) -> str:
    if kind in {"TAU_OUTPUT_PROPOSAL", "RISC0_JOURNAL_COMMIT"}:
        return "PROPOSAL"
    if kind in {
        "RUST_PROCESS_DISPATCH",
        "SHELL_CROSS_LANGUAGE_DISPATCH",
        "SHELL_DYNAMIC_DISPATCH",
        "SHELL_CONTAINER_COMMAND_DISPATCH",
    }:
        return "DISPATCH"
    if kind in {"RUST_NETWORK_EFFECT", "SHELL_NETWORK_EFFECT"}:
        return "NETWORK_EFFECT"
    if kind == "RUST_UNSAFE_OR_FFI_SURFACE":
        return "UNSAFE_OR_FFI_SURFACE"
    if kind == "STATE_ATTRIBUTE_ASSIGN":
        return "IN_MEMORY_STATE_MUTATION"
    return "DURABLE_MUTATION"


def _definition(kind: str, syntax: str) -> dict[str, str]:
    return {
        "effect_class": _effect_class(kind),
        "operation_kind": kind,
        "syntax_basis": syntax,
    }


def language_operation_definitions() -> dict[str, list[dict[str, str]]]:
    """Return the exact reviewed operation vocabulary for each source language."""

    return {
        "PYTHON": [
            _definition(kind, "O007A_AST_OPERATION_REGISTRY") for kind in sorted(SINK_KINDS)
        ],
        "RUST": [
            _definition(kind, "RUST_LEXICAL_OPERATION_REGISTRY")
            for kind in sorted({kind for kind, _ in RUST_OPERATION_PATTERNS})
        ],
        "SHELL": [
            _definition(kind, "SHELL_OR_DOCKER_OPERATION_REGISTRY")
            for kind in sorted(
                {kind for kind, _ in SHELL_OPERATION_PATTERNS}
                | {
                    "SHELL_CONTAINER_COMMAND_DISPATCH",
                    "SHELL_CONTAINER_COPY_ADD",
                    "SHELL_REDIRECTION_WRITE",
                }
            )
        ],
        "TAU": [_definition("TAU_OUTPUT_PROPOSAL", "TAU_OUTPUT_DEFINITION")],
    }


def _operation_fingerprint(*, language: str, path: str, kind: str, matches: tuple[str, ...]) -> str:
    return canonical_root(
        {
            "kind": kind,
            "language": language,
            "matches": list(matches),
            "path": path,
        }
    )


def _mediation_status(language: str, kind: str, source_role: str, provenance: str) -> str:
    if source_role.startswith("NONDEPLOYED_"):
        return "NONDEPLOYED_TEST_OR_RESEARCH_SOURCE"
    if kind == "TAU_OUTPUT_PROPOSAL":
        return "SPEC_PROPOSAL_NO_DURABLE_AUTHORITY"
    if kind == "RISC0_JOURNAL_COMMIT":
        return "PROOF_JOURNAL_PROPOSAL_NO_PUBLICATION_AUTHORITY"
    if provenance == "GENERATED_REFERENCE" and kind == "STATE_ATTRIBUTE_ASSIGN":
        return "REFERENCE_MODEL_IN_MEMORY_STATE"
    if provenance == "GENERATED_REFERENCE":
        return "UNMEDIATED_GENERATED_CODE_WRITER"
    return "UNMEDIATED_CROSS_LANGUAGE_WRITER"


def _aggregate_matches(
    *,
    language: str,
    path: str,
    provenance: str,
    source_role: str,
    matches: dict[str, list[str]],
) -> tuple[CrossLanguageObservationV1, ...]:
    return tuple(
        CrossLanguageObservationV1(
            language=language,
            path=path,
            operation_kind=kind,
            effect_class=_effect_class(kind),
            occurrence_count=len(values),
            fingerprint=_operation_fingerprint(
                language=language,
                path=path,
                kind=kind,
                matches=tuple(values),
            ),
            mediation_status=_mediation_status(language, kind, source_role, provenance),
            provenance=provenance,
            source_role=source_role,
        )
        for kind, values in sorted(matches.items())
    )


def _normalized_line(line_number: int, line: str) -> str:
    return f"{line_number}:{' '.join(line.strip().split())}"


def _mask_rust_noncode(source: str) -> str:
    output: list[str] = []
    index = block_depth = 0
    string_delimiter: str | None = None
    escaped = False
    while index < len(source):
        character = source[index]
        following = source[index + 1] if index + 1 < len(source) else ""
        if block_depth:
            if character == "/" and following == "*":
                block_depth += 1
                output.extend((" ", " "))
                index += 2
                continue
            if character == "*" and following == "/":
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
                continue
            output.append("\n" if character == "\n" else " ")
            index += 1
            continue
        if string_delimiter is not None:
            if source.startswith(string_delimiter, index) and not escaped:
                output.extend(" " for _ in string_delimiter)
                index += len(string_delimiter)
                string_delimiter = None
                continue
            escaped = string_delimiter == '"' and character == "\\" and not escaped
            output.append("\n" if character == "\n" else " ")
            index += 1
            continue
        if character == "/" and following == "/":
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            output.extend(" " for _ in range(end - index))
            index = end
            continue
        if character == "/" and following == "*":
            block_depth = 1
            output.extend((" ", " "))
            index += 2
            continue
        raw = re.match(r'r(?P<hashes>#{0,255})"', source[index:])
        if raw is not None:
            opening = raw.group(0)
            string_delimiter = '"' + raw.group("hashes")
            output.extend(" " for _ in opening)
            index += len(opening)
            continue
        if character == '"':
            string_delimiter = '"'
            escaped = False
            output.append(" ")
            index += 1
            continue
        output.append(character)
        index += 1
    return "".join(output)


def _rust_fs_aliases(code: str) -> dict[str, str]:
    aliases: dict[str, str] = {}
    for match in _RUST_FS_USE_RE.finditer(code):
        name = match.group("name")
        kind = _RUST_FS_FUNCTION_KINDS.get(name)
        if kind is not None:
            aliases[match.group("alias") or name] = kind
    for group in _RUST_FS_GROUP_USE_RE.finditer(code):
        for item in group.group("body").split(","):
            item_match = _RUST_FS_GROUP_ITEM_RE.fullmatch(item)
            if item_match is None:
                continue
            name = item_match.group("name")
            kind = _RUST_FS_FUNCTION_KINDS.get(name)
            if kind is not None:
                aliases[item_match.group("alias") or name] = kind
    return aliases


def scan_rust_source(
    path: str,
    source: str,
    *,
    source_role: str = "PRODUCTION_OR_PROOF_SOURCE",
) -> tuple[CrossLanguageObservationV1, ...]:
    matches: dict[str, list[str]] = defaultdict(list)
    source_lines = source.splitlines()
    masked = _mask_rust_noncode(source)
    code_lines = masked.splitlines()
    aliases = _rust_fs_aliases(masked)
    for line_number, (line, code) in enumerate(zip(source_lines, code_lines, strict=True), start=1):
        for kind, pattern in RUST_OPERATION_PATTERNS:
            for _match in pattern.finditer(code):
                matches[kind].append(_normalized_line(line_number, line))
        for alias, kind in aliases.items():
            for _match in re.finditer(rf"\b{re.escape(alias)}\s*\(", code):
                matches[kind].append(_normalized_line(line_number, line))
    return _aggregate_matches(
        language="RUST",
        path=path,
        provenance="HANDWRITTEN",
        source_role=source_role,
        matches=matches,
    )


def scan_shell_source(
    path: str,
    source: str,
    *,
    source_role: str = "OPERATOR_OR_DEPLOYMENT_SHELL",
) -> tuple[CrossLanguageObservationV1, ...]:
    matches: dict[str, list[str]] = defaultdict(list)
    for line_number, line in enumerate(source.splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        scanned_line = line.lstrip()
        if source_role == "CONTAINER_BUILD_SHELL":
            directive = _DOCKER_DIRECTIVE_RE.fullmatch(scanned_line)
            if directive is None:
                continue
            directive_name = directive.group("directive").upper()
            scanned_line = directive.group("body")
            if directive_name in {"COPY", "ADD"}:
                matches["SHELL_CONTAINER_COPY_ADD"].append(_normalized_line(line_number, line))
                continue
            if directive_name in {"CMD", "ENTRYPOINT"}:
                matches["SHELL_CONTAINER_COMMAND_DISPATCH"].append(
                    _normalized_line(line_number, line)
                )
                continue
        for kind, pattern in SHELL_OPERATION_PATTERNS:
            for _match in pattern.finditer(scanned_line):
                matches[kind].append(_normalized_line(line_number, line))
        for _match in _SHELL_REDIRECT_RE.finditer(scanned_line):
            matches["SHELL_REDIRECTION_WRITE"].append(_normalized_line(line_number, line))
    return _aggregate_matches(
        language="SHELL",
        path=path,
        provenance="HANDWRITTEN",
        source_role=source_role,
        matches=matches,
    )


def scan_tau_source(
    path: str,
    source: str,
    *,
    source_role: str = "TAU_FORMAL_SPEC_SOURCE",
) -> tuple[CrossLanguageObservationV1, ...]:
    output_indices = tuple(match.group("index") for match in _TAU_OUTPUT_RE.finditer(source))
    if not output_indices:
        return ()
    matches = {"TAU_OUTPUT_PROPOSAL": list(output_indices)}
    return _aggregate_matches(
        language="TAU",
        path=path,
        provenance="HANDWRITTEN",
        source_role=source_role,
        matches=matches,
    )


def generated_python_owner(path: str, source: str) -> GeneratedPythonOwnerV1:
    header = source[:8192]
    ir_match = _IR_HASH_RE.search(header)
    if ir_match is None:
        raise ValueError(f"{path}: generated owner metadata has no IR hash")
    owner_lines = [
        line.strip()
        for line in header.splitlines()
        if "Generated by " in line or "Generated from " in line
    ]
    if len(owner_lines) != 1:
        raise ValueError(f"{path}: generated owner metadata is missing or ambiguous")
    declared_owner = owner_lines[0]
    lowered = declared_owner.lower()
    if "esso" in lowered:
        owner_class = "ESSO_DECLARED"
    elif "private toolchain" in lowered:
        owner_class = "PRIVATE_TOOLCHAIN_DECLARED"
    elif "offline verifier toolchain" in lowered:
        owner_class = "OFFLINE_VERIFIER_DECLARED"
    else:
        owner_class = "OTHER_DECLARED_GENERATOR"
    return GeneratedPythonOwnerV1(
        path=path,
        owner_class=owner_class,
        declared_owner=declared_owner,
        ir_sha256=ir_match.group("digest"),
        replay_binding="DECLARED_OWNER_WITHOUT_PINNED_GENERATOR_REPLAY",
    )


def scan_generated_python_source(
    path: str,
    source: str,
    *,
    source_role: str = "GENERATED_REFERENCE_SOURCE",
) -> tuple[CrossLanguageObservationV1, ...]:
    tree = ast.parse(source, filename=path)
    grouped: dict[str, list[str]] = defaultdict(list)
    for observation in scan_module(path, tree):
        grouped[observation.sink_kind].append(observation.fingerprint)
    return _aggregate_matches(
        language="PYTHON",
        path=path,
        provenance="GENERATED_REFERENCE",
        source_role=source_role,
        matches=grouped,
    )
