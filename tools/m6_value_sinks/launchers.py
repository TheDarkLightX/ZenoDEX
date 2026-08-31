"""Decode the launchers a deployment step installs or a container runs.

Scan scope comes from these operations rather than from a declared source root.
A launcher the decoder cannot read becomes a typed finding, so an unmodelled
launcher shape cannot silently shrink the scanned surface.

Every path is resolved inside the exact repository root.  A symlink that
escapes, dangles, or loops rejects instead of widening the read set.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

LAUNCHER_DIRECTORY = "bin"
INSTALL_SCRIPT = "scripts/install_zenodex.sh"

MAX_LAUNCHER_BYTES = 256 * 1024
MAX_DOCKERFILES = 64

_INSTALL_WRAPPER_RE = re.compile(
    r"^install_wrapper\s+\"(?P<name>[^\"]+)\"\s+python3?\s+\"\$\{repo_dir\}/(?P<target>[^\"]+)\""
)
_LAUNCHER_EXEC_RE = re.compile(r"^exec\s+python3?\s+\"\$\{repo_dir\}/(?P<target>[^\"]+)\"")
_SHELL_MODULE_RE = re.compile(r"\bpython3?\s+-m\s+(?P<module>[A-Za-z_][A-Za-z0-9_.]*)")
_SHELL_SCRIPT_RE = re.compile(r"\bpython3?\s+(?P<target>[A-Za-z0-9_./-]+\.py)\b")
_DOCKER_DISPATCH_RE = re.compile(r"^(?:ENTRYPOINT|CMD)\b(?P<body>.*)$")
_SHELL_TOKEN_RE = re.compile(r"[A-Za-z0-9_./-]+\.sh\b")


@dataclass(frozen=True, slots=True, order=True)
class DeployedEntrypointV2:
    entrypoint_id: str
    target: str
    discovery: str

    def to_dict(self) -> dict[str, str]:
        return {
            "discovery": self.discovery,
            "entrypoint_id": self.entrypoint_id,
            "target": self.target,
        }


@dataclass(frozen=True, slots=True, order=True)
class ClosureFindingV2:
    path: str
    rule_id: str
    evidence: str

    def to_dict(self) -> dict[str, str]:
        return {"evidence": self.evidence, "path": self.path, "rule_id": self.rule_id}


def canonical_relative_path(value: str) -> str | None:
    """Reject absolute, escaping, or noncanonical repository paths."""

    if not value or value.startswith("/") or "\\" in value or ":" in value:
        return None
    if any(ord(character) < 32 or ord(character) == 127 for character in value):
        return None
    # Inspect the literal components: PurePosixPath silently folds away "." parts.
    if any(part in {"", ".", ".."} for part in value.split("/")):
        return None
    return PurePosixPath(value).as_posix()


def safe_relative(path: Path, root: Path) -> str | None:
    """Resolve a path inside the exact repository root, or reject it.

    A symlink may leave the root, dangle, or loop.  Resolution failure and
    escape both reject, so the scan never reads outside the subject tree and
    never raises on a hostile tree.
    """

    try:
        resolved = path.resolve(strict=False)
    except (OSError, RuntimeError, ValueError):
        return None
    try:
        if not resolved.is_relative_to(root):
            return None
        return resolved.relative_to(root).as_posix()
    except (OSError, ValueError):
        return None


def contained_file(path: Path, root: Path) -> Path | None:
    """Return the resolved path when it is a regular file inside the root."""

    if safe_relative(path, root) is None:
        return None
    try:
        resolved = path.resolve(strict=False)
        return resolved if resolved.is_file() else None
    except (OSError, RuntimeError, ValueError):
        return None


def classify_unscannable_candidate(candidate: Path, root: Path) -> str | None:
    """Explain why a lexically present candidate cannot be scanned.

    A path that exists in the tree, including as a symlink, is a reachable edge.
    Returning ``None`` for it would drop that edge silently, so escaping,
    dangling, and looping candidates each receive a reason instead.  A candidate
    with no lexical presence is an ordinary external import and stays out of
    scope.
    """

    if not (candidate.is_symlink() or candidate.exists()):
        return None
    try:
        resolved = candidate.resolve(strict=True)
    except FileNotFoundError:
        return "dangling"
    except (OSError, RuntimeError, ValueError):
        return "unresolvable"
    if not resolved.is_relative_to(root):
        return "escapes_root"
    return None if resolved.is_file() else "unresolvable"


def read_bounded_text(path: Path, maximum: int) -> tuple[str | None, str | None]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        return None, str(exc)
    if len(raw) > maximum:
        return None, f"exceeds {maximum} bytes"
    try:
        return raw.decode("utf-8", errors="strict"), None
    except UnicodeDecodeError as exc:
        return None, str(exc)


def _decode_install_script(root: Path) -> tuple[list[DeployedEntrypointV2], list[ClosureFindingV2]]:
    script = root / INSTALL_SCRIPT
    if not script.is_file():
        return [], [
            ClosureFindingV2(INSTALL_SCRIPT, "install_script_missing", "no deployment source")
        ]
    text, error = read_bounded_text(script, MAX_LAUNCHER_BYTES)
    if text is None:
        return [], [
            ClosureFindingV2(INSTALL_SCRIPT, "install_script_unreadable", error or "unreadable")
        ]
    entrypoints: list[DeployedEntrypointV2] = []
    findings: list[ClosureFindingV2] = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped.startswith("install_wrapper "):
            continue
        match = _INSTALL_WRAPPER_RE.match(stripped)
        if match is None:
            findings.append(
                ClosureFindingV2(INSTALL_SCRIPT, "undecodable_install_wrapper", stripped)
            )
            continue
        entrypoints.append(
            DeployedEntrypointV2(match.group("name"), match.group("target"), "INSTALL_SCRIPT")
        )
    if not entrypoints and not findings:
        findings.append(
            ClosureFindingV2(
                INSTALL_SCRIPT, "install_script_declares_no_launcher", "zero install_wrapper calls"
            )
        )
    return entrypoints, findings


def _decode_launcher_directory(
    root: Path,
) -> tuple[list[DeployedEntrypointV2], list[ClosureFindingV2]]:
    directory = root / LAUNCHER_DIRECTORY
    if not directory.is_dir():
        return [], []
    entrypoints: list[DeployedEntrypointV2] = []
    findings: list[ClosureFindingV2] = []
    for path in sorted(directory.iterdir()):
        relative = safe_relative(path, root)
        if relative is None:
            findings.append(
                ClosureFindingV2(path.name, "launcher_escapes_repository_root", LAUNCHER_DIRECTORY)
            )
            continue
        if not path.is_file():
            findings.append(
                ClosureFindingV2(relative, "launcher_is_not_a_regular_file", LAUNCHER_DIRECTORY)
            )
            continue
        text, error = read_bounded_text(path, MAX_LAUNCHER_BYTES)
        if text is None:
            findings.append(
                ClosureFindingV2(relative, "launcher_unreadable", error or "unreadable")
            )
            continue
        targets = [
            match.group("target")
            for line in text.splitlines()
            if (match := _LAUNCHER_EXEC_RE.match(line.strip())) is not None
        ]
        if not targets:
            findings.append(
                ClosureFindingV2(relative, "undecodable_launcher", "no decodable exec target")
            )
            continue
        entrypoints.extend(
            DeployedEntrypointV2(path.name, target, "LAUNCHER_WRAPPER") for target in targets
        )
    return entrypoints, findings


def _shell_scripts_by_name(root: Path) -> dict[str, str]:
    names: dict[str, str] = {}
    for candidate in sorted(root.rglob("*.sh")):
        resolved = safe_relative(candidate, root)
        if resolved is not None and candidate.is_file() and ".git" not in candidate.parts:
            names.setdefault(candidate.name, resolved)
    return names


def _container_shell_scripts(root: Path) -> tuple[list[str], list[ClosureFindingV2]]:
    """Resolve shell scripts that a container image designates as its dispatch."""

    scripts: set[str] = set()
    findings: list[ClosureFindingV2] = []
    dockerfiles = sorted(path for path in root.glob("Dockerfile*") if path.is_file())[
        :MAX_DOCKERFILES
    ]
    shell_by_name = _shell_scripts_by_name(root)
    for dockerfile in dockerfiles:
        relative = safe_relative(dockerfile, root)
        if relative is None:
            continue
        text, error = read_bounded_text(dockerfile, MAX_LAUNCHER_BYTES)
        if text is None:
            findings.append(
                ClosureFindingV2(relative, "dockerfile_unreadable", error or "unreadable")
            )
            continue
        for line in text.splitlines():
            match = _DOCKER_DISPATCH_RE.match(line.strip())
            if match is None:
                continue
            for token in _SHELL_TOKEN_RE.findall(match.group("body")):
                resolved = shell_by_name.get(PurePosixPath(token).name)
                if resolved is None:
                    findings.append(
                        ClosureFindingV2(relative, "undecodable_container_dispatch", token)
                    )
                else:
                    scripts.add(resolved)
    return sorted(scripts), findings


def _decode_container_entrypoints(
    root: Path,
) -> tuple[list[DeployedEntrypointV2], list[ClosureFindingV2]]:
    scripts, findings = _container_shell_scripts(root)
    entrypoints: list[DeployedEntrypointV2] = []
    for script in scripts:
        text, error = read_bounded_text(root / script, MAX_LAUNCHER_BYTES)
        if text is None:
            findings.append(
                ClosureFindingV2(script, "container_script_unreadable", error or "unreadable")
            )
            continue
        entrypoints.extend(
            DeployedEntrypointV2(script, f"-m {match.group('module')}", "CONTAINER_ENTRYPOINT")
            for match in _SHELL_MODULE_RE.finditer(text)
        )
        entrypoints.extend(
            DeployedEntrypointV2(script, match.group("target"), "CONTAINER_ENTRYPOINT")
            for match in _SHELL_SCRIPT_RE.finditer(text)
        )
    return entrypoints, findings


def derive_deployed_entrypoints(
    root: Path,
) -> tuple[tuple[DeployedEntrypointV2, ...], tuple[ClosureFindingV2, ...]]:
    """Decode every launcher a deployment step installs or a container runs."""

    root = root.resolve()
    entrypoints: list[DeployedEntrypointV2] = []
    findings: list[ClosureFindingV2] = []
    for decode in (
        _decode_install_script,
        _decode_launcher_directory,
        _decode_container_entrypoints,
    ):
        decoded, decoded_findings = decode(root)
        entrypoints.extend(decoded)
        findings.extend(decoded_findings)
    unique = tuple(sorted(set(entrypoints)))
    findings.extend(_validate_targets(unique, root))
    return unique, tuple(sorted(findings))


def _validate_targets(
    entrypoints: tuple[DeployedEntrypointV2, ...], root: Path
) -> list[ClosureFindingV2]:
    findings: list[ClosureFindingV2] = []
    for entrypoint in entrypoints:
        if entrypoint.target.startswith("-m "):
            continue
        if canonical_relative_path(entrypoint.target) is None:
            findings.append(
                ClosureFindingV2(
                    entrypoint.target, "launcher_target_noncanonical", entrypoint.entrypoint_id
                )
            )
        elif contained_file(root / entrypoint.target, root) is None:
            # Missing, non-regular, dangling, or escaping targets all reject here.
            findings.append(
                ClosureFindingV2(
                    entrypoint.target, "launcher_target_unresolvable", entrypoint.entrypoint_id
                )
            )
    return findings
