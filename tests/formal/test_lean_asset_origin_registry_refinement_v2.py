"""Source-pinned formal gate for the V2 asset-origin registry model.

The Lean model covers the exact 12-code protocol rejection order, rejection
no-op behavior, authority and occurrence prerequisites, deterministic record
insertion, and the authority-free accepted effect shape.  Python and Rust
source hashes plus enum/registry parity reopen this review when either mirror
changes.

This is bounded evidence.  It grants no codec or hash equivalence, runtime
mount, migration, settlement, release, or production authority.
"""

from __future__ import annotations

import ast
import hashlib
import os
import re
import shutil
import subprocess
from pathlib import Path
from typing import TypedDict

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
PROOF = LEAN_DIR / "Proofs" / "AssetOriginRegistryRefinementV2.lean"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"
PYTHON_TYPES = ROOT / "src" / "core" / "asset_origin_registry_types_v2.py"
PYTHON_TRANSITION = ROOT / "src" / "core" / "asset_origin_registry_v2.py"
RUST_TYPES = (
    ROOT / "zk" / "global_settlement_abi_v2" / "src" / "asset_origin_registry_types.rs"
)
RUST_TRANSITION = (
    ROOT / "zk" / "global_settlement_abi_v2" / "src" / "asset_origin_registry.rs"
)

NAMESPACE = "Proofs.AssetOriginRegistryRefinementV2"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"
PINNED_SOURCES = {
    PYTHON_TYPES: "b41118756ca47b3287cb862e1ea5bd3dffa6248759c6ac7b548d9b87747466e1",
    PYTHON_TRANSITION: "30a94b99eda4c395b5510fb11bf295171399290f3db72112092a42eb00850be4",
    RUST_TYPES: "4d6bd2a4b64b48c02bd8f5d9cc7bf911a50832cd2d4642d4c97abf7197bd436d",
    RUST_TRANSITION: "0aa6a0c8c6450b23599d88514e24e068930f5354abbf1cf90001466dcb0804d8",
}

EXPECTED_REJECT_CODES = (
    "MISSING_OCCURRENCE",
    "OCCURRENCE_BINDING_MISMATCH",
    "RELEASE_MISMATCH",
    "UNKNOWN_COMMAND",
    "OCCURRENCE_COMMAND_MISMATCH",
    "UNAUTHORIZED_SUBJECT",
    "GRANT_MISMATCH",
    "DECIMAL_SCALE_MISMATCH",
    "DISABLED_ORIGIN_KIND",
    "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED",
    "DUPLICATE_ASSET",
    "DUPLICATE_ORIGIN",
)

THEOREMS = (
    "production_authority_is_none",
    "all_reject_codes_length",
    "all_reject_codes_wire_order",
    "all_reject_codes_complete",
    "all_reject_codes_no_duplicates",
    "RejectCode.rank_injective",
    "mem_insert_record",
    "command_record_mem_post",
    "pre_record_mem_post",
    "post_assets_length",
    "firstFailing_eq_none_iff",
    "firstFailing_some_spec",
    "exact_reject_precedence",
    "acceptance_witness",
    "native_registration_rejection_witness",
    "transition_total",
    "rejected_is_exact_noop",
    "accepted_has_exact_effect_shape",
    "accepted_consumes_exact_occurrence",
    "accepted_registers_exact_command_record",
    "accepted_requires_authority_and_tau_origin",
    "disabled_native_precedes_native_unimplemented",
    "duplicate_asset_precedes_duplicate_origin",
)

ALLOWED_STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})


class CompiledPacket(TypedDict):
    root: Path
    lean: Path
    environment: dict[str, str]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "asset-origin formal gate requires lake"
    return lake


def _repository_candidates() -> tuple[Path, ...]:
    result = subprocess.run(
        ["git", "rev-parse", "--path-format=absolute", "--git-common-dir"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    common_dir = Path(result.stdout.strip()).resolve()
    candidates = (ROOT, common_dir.parent)
    return tuple(dict.fromkeys(candidates))


def _cached_lean_directory() -> Path:
    for candidate in _repository_candidates():
        lean_dir = candidate / "lean-mathlib"
        if (
            (lean_dir / "lean-toolchain").is_file()
            and (lean_dir / ".lake" / "packages" / "mathlib").exists()
            and (candidate / "external" / "mathlib4").exists()
        ):
            assert (lean_dir / "lean-toolchain").read_text(encoding="utf-8").strip() == (
                PINNED_TOOLCHAIN
            )
            return lean_dir
    raise AssertionError("no existing pinned Lean/mathlib cache was found")


def _lake_cached(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [_require_lake(), *args],
        cwd=_cached_lean_directory(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )


@pytest.fixture(scope="module")
def compiled_packet(tmp_path_factory: pytest.TempPathFactory) -> CompiledPacket:
    build_root = tmp_path_factory.mktemp("asset-origin-registry-v2-lean")
    (build_root / "Proofs").mkdir()

    lean_result = _lake_cached("env", "which", "lean")
    assert lean_result.returncode == 0, lean_result.stdout + lean_result.stderr
    lean = Path(lean_result.stdout.strip())
    assert lean.is_file()

    version = subprocess.run(
        [str(lean), "--version"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        check=False,
    )
    assert version.returncode == 0, version.stdout + version.stderr
    assert "version 4.27.0" in version.stdout

    path_result = _lake_cached("env", "printenv", "LEAN_PATH")
    assert path_result.returncode == 0, path_result.stdout + path_result.stderr
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(
        (str(build_root), path_result.stdout.strip())
    )

    module_output = build_root / "Proofs" / "AssetOriginRegistryRefinementV2.olean"
    result = subprocess.run(
        [
            str(lean),
            "-DwarningAsError=true",
            "-o",
            str(module_output),
            str(PROOF),
        ],
        cwd=ROOT,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=300,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""
    assert module_output.is_file()
    return {"root": build_root, "lean": lean, "environment": environment}


def _python_enum_codes(source: str) -> tuple[str, ...]:
    tree = ast.parse(source)
    enum_class = next(
        node
        for node in tree.body
        if isinstance(node, ast.ClassDef)
        and node.name == "AssetOriginRegistrationRejectCodeV2"
    )
    codes: list[str] = []
    for node in enum_class.body:
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if not isinstance(target, ast.Name) or not target.id.isupper():
            continue
        value = ast.literal_eval(node.value)
        assert value == target.id
        codes.append(target.id)
    return tuple(codes)


def _required_match(pattern: str, source: str) -> re.Match[str]:
    found = re.search(pattern, source, flags=re.MULTILINE | re.DOTALL)
    assert found is not None, pattern
    return found


def _rust_enum_codes(source: str) -> tuple[str, ...]:
    body = _required_match(
        r"pub enum AssetOriginRegistrationRejectCodeV2 \{(?P<body>.*?)^\}",
        source,
    ).group("body")
    return tuple(re.findall(r"^\s{4}([A-Z][A-Z0-9_]+),$", body, re.MULTILINE))


def _rust_registry_codes(source: str) -> tuple[str, ...]:
    body = _required_match(
        r"pub const ALL_ASSET_ORIGIN_REGISTRATION_REJECT_CODES_V2:.*?= \["
        r"(?P<body>.*?)^\];",
        source,
    ).group("body")
    return tuple(
        re.findall(
            r"AssetOriginRegistrationRejectCodeV2::([A-Z][A-Z0-9_]+)",
            body,
        )
    )


def _lean_wire_codes(source: str) -> tuple[str, ...]:
    start = source.index("def RejectCode.code")
    end = source.index("def RejectCode.rank", start)
    return tuple(re.findall(r'=> "([A-Z_]+)"', source[start:end]))


def _theorem_declarations(source: str) -> tuple[str, ...]:
    return tuple(
        re.findall(
            r"^theorem\s+([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)"
            r"(?=\s|:)",
            source,
            re.MULTILINE,
        )
    )


def _axiom_dependencies(output: str) -> set[str]:
    dependencies: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL):
        dependencies.update(item.strip() for item in body.split(",") if item.strip())
    return dependencies


def test_modeled_python_and_rust_sources_are_exactly_pinned() -> None:
    for path, expected in PINNED_SOURCES.items():
        assert path.is_file(), path
        assert _sha256(path) == expected, path


def test_reject_registry_has_exact_python_rust_lean_parity() -> None:
    python_source = PYTHON_TYPES.read_text(encoding="utf-8")
    rust_source = RUST_TYPES.read_text(encoding="utf-8")
    lean_source = PROOF.read_text(encoding="utf-8")

    assert _python_enum_codes(python_source) == EXPECTED_REJECT_CODES
    assert _rust_enum_codes(rust_source) == EXPECTED_REJECT_CODES
    assert _rust_registry_codes(rust_source) == EXPECTED_REJECT_CODES
    assert _lean_wire_codes(lean_source) == EXPECTED_REJECT_CODES


def test_theorem_surface_is_closed_and_model_compiles(
    compiled_packet: CompiledPacket,
) -> None:
    del compiled_packet
    source = PROOF.read_text(encoding="utf-8")
    assert _theorem_declarations(source) == THEOREMS


def test_model_has_no_unproved_placeholders() -> None:
    result = subprocess.run(
        ["python3", str(SCANNER), "--json", str(PROOF)],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=60,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_every_theorem_uses_only_standard_axioms(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
) -> None:
    probe = tmp_path / "AssetOriginRegistryRefinementV2Axioms.lean"
    probe.write_text(
        "import Proofs.AssetOriginRegistryRefinementV2\n"
        + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in THEOREMS)
        + "\n",
        encoding="utf-8",
    )
    result = subprocess.run(
        [
            str(compiled_packet["lean"]),
            "-DwarningAsError=true",
            str(probe),
        ],
        cwd=ROOT,
        env=compiled_packet["environment"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=300,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr.strip() == ""
    assert _axiom_dependencies(result.stdout) <= ALLOWED_STANDARD_AXIOMS


def test_claim_ceiling_stays_explicit() -> None:
    source = PROOF.read_text(encoding="utf-8")
    assert 'def productionAuthority : String := "NONE"' in source
    for term in (
        "cryptographic hashes",
        "Python/Rust/Lean execution equivalence",
        "mounting",
        "settlement",
        "migration",
        "release",
        "production authority",
    ):
        assert term in source
