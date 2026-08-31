"""Source-pinned formal gate for the V2 asset-origin registry model.

The Lean model covers the exact 12-code protocol rejection order on an explicit
valid-state/valid-command domain, rejection no-op behavior, deterministic
record insertion and invariant preservation, and the authority-free typed
accepted effect shape.  Python and Rust source hashes plus deterministic
semantic extractors reopen this review when the modeled source surface changes.

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
PYTHON_ASSET_TYPES = ROOT / "src" / "core" / "asset_transfer_types_v2.py"
PYTHON_PRIMITIVES = ROOT / "src" / "core" / "global_settlement_primitives_v2.py"
PYTHON_EFFECT_VALUES = ROOT / "src" / "core" / "global_settlement_effect_values_v2.py"
PYTHON_EFFECT_PLAN = ROOT / "src" / "core" / "global_settlement_effect_plan_v2.py"
PYTHON_PROOF = ROOT / "src" / "core" / "global_economic_proof_v2.py"
PYTHON_SETTLEMENT_FACADE = ROOT / "src" / "core" / "global_settlement_types_v2.py"
RUST_ASSET_TYPES = (
    ROOT / "zk" / "global_settlement_abi_v2" / "src" / "asset_transfer_types.rs"
)
RUST_CANONICAL = ROOT / "zk" / "global_settlement_abi_v2" / "src" / "canonical.rs"
RUST_EFFECT_VALUES = (
    ROOT / "zk" / "global_settlement_abi_v2" / "src" / "effect_values.rs"
)
RUST_EFFECT_PLAN = ROOT / "zk" / "global_settlement_abi_v2" / "src" / "effects.rs"
RUST_PROOF = ROOT / "zk" / "global_settlement_abi_v2" / "src" / "proof.rs"

NAMESPACE = "Proofs.AssetOriginRegistryRefinementV2"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"
PINNED_SOURCES = {
    PYTHON_TYPES: "b41118756ca47b3287cb862e1ea5bd3dffa6248759c6ac7b548d9b87747466e1",
    PYTHON_TRANSITION: "30a94b99eda4c395b5510fb11bf295171399290f3db72112092a42eb00850be4",
    RUST_TYPES: "4d6bd2a4b64b48c02bd8f5d9cc7bf911a50832cd2d4642d4c97abf7197bd436d",
    RUST_TRANSITION: "0aa6a0c8c6450b23599d88514e24e068930f5354abbf1cf90001466dcb0804d8",
    PYTHON_ASSET_TYPES: "345ddc4a414b8526d7e52e53b22cbc987bfa4b9ad3b2573d0aa5ae37c8f74283",
    PYTHON_PRIMITIVES: "11a26694357812e91b398bddc2b6bbec0a93063731ccd5b23818de1d0c0ca01e",
    PYTHON_EFFECT_VALUES: "a366616f8a11f35d5c69d29c91e1d0b8598ac48499eb44d86d8011c73d30fb9a",
    PYTHON_EFFECT_PLAN: "e352b67a13ac22e09d31d5aebf94d10aa7f540ef3149050ed2675854f6b839f0",
    PYTHON_PROOF: "087b4df5295d82d112d552bac136b66cf0010f078915c29869d7a427fd8d5705",
    PYTHON_SETTLEMENT_FACADE: "25624adb564c5b0c610638d707a8c09893afb754b3574299eb9a369d6cf73f39",
    RUST_ASSET_TYPES: "599b478ff18e7270650eddd005c22c2124ceebbe137a029fb7b7fe6e51efe3c2",
    RUST_CANONICAL: "b17a76d6e8ce5915ba1d250982147dceda0d7368911b396f7ae83fd860216053",
    RUST_EFFECT_VALUES: "2546015b68ddf0197cdf584dcefde8a7d7ae0eb6d77e24f98ba86fb375400f24",
    RUST_EFFECT_PLAN: "38f4be8275fdabed5b3af792dc9c16292a4ed6b2cd57ee1812afa881c301cf84",
    RUST_PROOF: "f0fb984ae594284795c1c01a54a6e0dffacd69b4732a2fd7153128ce7a691dce",
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

EXPECTED_ORIGIN_KINDS = ("NATIVE", "TAU_ORIGINATED")
EXPECTED_ASSET_CLASSES = (
    "TAU_NATIVE_COIN",
    "CANONICAL_ZUSD",
    "LP_SHARE",
    "ZDEX_PROTOCOL_TOKEN",
    "SEALED_BID_PAYMENT_OR_INVENTORY",
    "REGISTERED_ORDINARY_TOKEN",
)

DECLARATIONS = (
    ("theorem", "all_reject_codes_length"),
    ("theorem", "all_reject_codes_wire_order"),
    ("theorem", "all_reject_codes_complete"),
    ("theorem", "all_reject_codes_no_duplicates"),
    ("theorem", "RejectCode.rank_injective"),
    ("theorem", "mem_insert_record"),
    ("theorem", "command_record_mem_post"),
    ("theorem", "pre_record_mem_post"),
    ("theorem", "post_assets_length"),
    ("theorem", "insertRecord_perm"),
    ("theorem", "insertRecord_preserves_strict_asset_order"),
    ("theorem", "strict_asset_order_implies_unique_assets"),
    ("theorem", "unique_assets_implies_rows_nodup"),
    ("theorem", "insertRecord_preserves_unique_origins"),
    ("theorem", "insertRecord_preserves_native_unique"),
    ("theorem", "insertRecord_preserves_record_validity"),
    ("theorem", "firstFailing_eq_none_iff"),
    ("theorem", "firstFailing_some_spec"),
    ("theorem", "exact_reject_precedence"),
    ("theorem", "acceptance_witness"),
    ("theorem", "native_registration_rejection_witness"),
    ("theorem", "acceptance_witness_on_valid_domain"),
    ("theorem", "every_reject_code_reachable_on_valid_domain"),
    ("theorem", "adjacent_double_failure_precedence"),
    ("theorem", "rejected_is_exact_noop"),
    ("theorem", "accepted_has_exact_effect_shape"),
    ("theorem", "accepted_reject_code_is_none"),
    ("theorem", "accepted_all_guards_pass"),
    ("theorem", "accepted_consumes_exact_occurrence"),
    ("theorem", "accepted_registers_exact_command_record"),
    ("theorem", "accepted_requires_authority_and_tau_origin"),
    ("theorem", "accepted_preserves_valid_state"),
    ("theorem", "accepted_preserves_registry_invariants"),
    ("theorem", "accepted_inserts_exactly_one_command_record"),
    ("theorem", "disabled_native_precedes_native_unimplemented"),
    ("theorem", "duplicate_asset_precedes_duplicate_origin"),
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


def _python_enum_entries(source: str, class_name: str) -> tuple[tuple[str, str], ...]:
    tree = ast.parse(source)
    enum_class = next(
        node
        for node in tree.body
        if isinstance(node, ast.ClassDef)
        and node.name == class_name
    )
    entries: list[tuple[str, str]] = []
    for node in enum_class.body:
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if not isinstance(target, ast.Name) or not target.id.isupper():
            continue
        value = ast.literal_eval(node.value)
        assert isinstance(value, str), (class_name, target.id)
        entries.append((target.id, value))
    assert entries, class_name
    return tuple(entries)


def _constant_value(node: ast.expr) -> object:
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.BinOp):
        left = _constant_value(node.left)
        right = _constant_value(node.right)
        if isinstance(node.op, ast.Add) and isinstance(left, str) and isinstance(right, str):
            return left + right
        if isinstance(node.op, ast.Mult):
            if isinstance(left, str) and isinstance(right, int):
                return left * right
            if isinstance(left, int) and isinstance(right, str):
                return left * right
    raise AssertionError(ast.dump(node))


def _python_constant(source: str, name: str) -> object:
    tree = ast.parse(source)
    for node in tree.body:
        if (
            isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.target.id == name
            and node.value is not None
        ):
            return _constant_value(node.value)
        if isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == name for target in node.targets
        ):
            return _constant_value(node.value)
    raise AssertionError(name)


def _python_function_source(source: str, name: str) -> str:
    tree = ast.parse(source)
    function = next(
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name
    )
    segment = ast.get_source_segment(source, function)
    assert segment is not None, name
    return segment


def _required_match(pattern: str, source: str) -> re.Match[str]:
    found = re.search(pattern, source, flags=re.MULTILINE | re.DOTALL)
    assert found is not None, pattern
    return found


def _rust_enum_members(source: str, name: str) -> tuple[str, ...]:
    body = _required_match(
        rf"pub enum {re.escape(name)} \{{(?P<body>.*?)^\}}",
        source,
    ).group("body")
    members = tuple(
        re.findall(r"^\s{4}([A-Za-z_][A-Za-z0-9_]+),$", body, re.MULTILINE)
    )
    assert members, name
    return members


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


def _rust_as_str_entries(source: str) -> tuple[tuple[str, str], ...]:
    body = _required_match(
        r"impl AssetOriginRegistrationRejectCodeV2 \{.*?"
        r"pub const fn as_str\(self\).*?match self \{(?P<body>.*?)^\s{8}\}",
        source,
    ).group("body")
    entries = tuple(
        re.findall(
            r'Self::([A-Z][A-Z0-9_]+)\s*=>\s*"([A-Z][A-Z0-9_]+)"',
            body,
        )
    )
    assert entries
    return entries


def _rust_function_slice(source: str, name: str, next_name: str) -> str:
    start = source.index(f"fn {name}(")
    end = source.index(f"fn {next_name}(", start)
    return source[start:end]


def _rust_reject_codes(source: str) -> tuple[str, ...]:
    return tuple(
        re.findall(r"AssetOriginRegistrationRejectCodeV2::([A-Z][A-Z0-9_]+)", source)
    )


def _python_reject_codes(source: str) -> tuple[str, ...]:
    return tuple(
        re.findall(r"AssetOriginRegistrationRejectCodeV2\.([A-Z][A-Z0-9_]+)", source)
    )


def _rust_const_expression(source: str, name: str) -> str:
    return _required_match(
        rf"^pub const {re.escape(name)}:[^=]+=(?P<value>[^;]+);$",
        source,
    ).group("value").strip()


def _lean_wire_codes(source: str) -> tuple[str, ...]:
    start = source.index("def RejectCode.code")
    end = source.index("def RejectCode.rank", start)
    return tuple(re.findall(r'=> "([A-Z_]+)"', source[start:end]))


def _lean_inductive_members(source: str, name: str) -> tuple[str, ...]:
    body = _required_match(
        rf"^inductive {re.escape(name)} where$(?P<body>.*?)^\s+deriving ",
        source,
    ).group("body")
    members = tuple(
        re.findall(r"^\s+\|\s+([A-Za-z_][A-Za-z0-9_]*)$", body, re.MULTILINE)
    )
    assert members, name
    return members


def _proof_declarations(source: str) -> tuple[tuple[str, str], ...]:
    return tuple(
        re.findall(
            r"^\s*(?:(?:private|protected|local|noncomputable)\s+)*"
            r"(theorem|lemma)\s+"
            r"([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)"
            r"(?=\s|:)",
            source,
            re.MULTILINE,
        )
    )


def _axiom_reports(output: str) -> tuple[tuple[str, frozenset[str]], ...]:
    pattern = re.compile(
        r"'(?P<name>[^']+)' (?:(?:does not depend on any axioms)|"
        r"(?:depends on axioms:\s*\[(?P<deps>[^\]]*)\]))",
        re.DOTALL,
    )
    reports: list[tuple[str, frozenset[str]]] = []
    cursor = 0
    for found in pattern.finditer(output):
        assert output[cursor : found.start()].strip() == "", output[cursor : found.start()]
        dependencies = frozenset(
            item.strip() for item in (found.group("deps") or "").split(",") if item.strip()
        )
        reports.append((found.group("name"), dependencies))
        cursor = found.end()
    assert output[cursor:].strip() == "", output[cursor:]
    assert reports
    return tuple(reports)


def test_modeled_python_and_rust_sources_are_exactly_pinned() -> None:
    for path, expected in PINNED_SOURCES.items():
        assert path.is_file(), path
        assert _sha256(path) == expected, path


def test_reject_registry_has_exact_python_rust_lean_parity() -> None:
    python_source = PYTHON_TYPES.read_text(encoding="utf-8")
    rust_source = RUST_TYPES.read_text(encoding="utf-8")
    lean_source = PROOF.read_text(encoding="utf-8")

    python_entries = _python_enum_entries(
        python_source,
        "AssetOriginRegistrationRejectCodeV2",
    )
    assert tuple(name for name, _ in python_entries) == EXPECTED_REJECT_CODES
    assert tuple(value for _, value in python_entries) == EXPECTED_REJECT_CODES
    assert (
        _rust_enum_members(rust_source, "AssetOriginRegistrationRejectCodeV2")
        == EXPECTED_REJECT_CODES
    )
    assert _rust_registry_codes(rust_source) == EXPECTED_REJECT_CODES
    assert _rust_as_str_entries(rust_source) == tuple(
        (code, code) for code in EXPECTED_REJECT_CODES
    )
    assert _lean_wire_codes(lean_source) == EXPECTED_REJECT_CODES


def test_reject_guard_order_is_extracted_from_both_runtime_mirrors() -> None:
    python_source = PYTHON_TRANSITION.read_text(encoding="utf-8")
    python_transition = _python_function_source(
        python_source,
        "transition_asset_origin_registration_v2",
    )
    assert _python_reject_codes(python_transition) == EXPECTED_REJECT_CODES

    rust_source = RUST_TRANSITION.read_text(encoding="utf-8")
    binding = _rust_function_slice(
        rust_source,
        "binding_reject_code",
        "authority_reject_code",
    )
    authority = _rust_function_slice(
        rust_source,
        "authority_reject_code",
        "uniqueness_reject_code",
    )
    uniqueness = _rust_function_slice(
        rust_source,
        "uniqueness_reject_code",
        "registration_reject_code",
    )
    binding_codes = _rust_reject_codes(binding)
    authority_codes = _rust_reject_codes(authority)
    uniqueness_codes = _rust_reject_codes(uniqueness)
    assert authority_codes[0] == "MISSING_OCCURRENCE"
    assert binding_codes + authority_codes[1:] + uniqueness_codes == EXPECTED_REJECT_CODES

    registration = _rust_function_slice(
        rust_source,
        "registration_reject_code",
        "build_post_state",
    )
    assert re.findall(
        r"\b(binding_reject_code|authority_reject_code|uniqueness_reject_code)\(",
        registration,
    ) == ["binding_reject_code", "authority_reject_code", "uniqueness_reject_code"]


def test_modeled_enums_constants_and_effect_shape_are_source_bound() -> None:
    python_types = PYTHON_TYPES.read_text(encoding="utf-8")
    python_asset_types = PYTHON_ASSET_TYPES.read_text(encoding="utf-8")
    python_primitives = PYTHON_PRIMITIVES.read_text(encoding="utf-8")
    python_transition = _python_function_source(
        PYTHON_TRANSITION.read_text(encoding="utf-8"),
        "transition_asset_origin_registration_v2",
    )
    rust_types = RUST_TYPES.read_text(encoding="utf-8")
    rust_asset_types = RUST_ASSET_TYPES.read_text(encoding="utf-8")
    rust_transition = RUST_TRANSITION.read_text(encoding="utf-8")
    rust_canonical = RUST_CANONICAL.read_text(encoding="utf-8")
    lean_source = PROOF.read_text(encoding="utf-8")

    assert tuple(
        name for name, _ in _python_enum_entries(python_types, "AssetOriginKindV2")
    ) == EXPECTED_ORIGIN_KINDS
    assert _rust_enum_members(rust_types, "AssetOriginKindV2") == EXPECTED_ORIGIN_KINDS
    assert _lean_inductive_members(lean_source, "OriginKind") == ("native", "tauOriginated")

    assert tuple(
        name for name, _ in _python_enum_entries(python_asset_types, "AssetClassV2")
    ) == EXPECTED_ASSET_CLASSES
    assert _rust_enum_members(rust_asset_types, "AssetClassV2") == (
        "TauNativeCoin",
        "CanonicalZusd",
        "LpShare",
        "ZdexProtocolToken",
        "SealedBidPaymentOrInventory",
        "RegisteredOrdinaryToken",
    )
    assert _lean_inductive_members(lean_source, "AssetClass") == (
        "tauNativeCoin",
        "canonicalZusd",
        "lpShare",
        "zdexProtocolToken",
        "sealedBidPaymentOrInventory",
        "registeredOrdinaryToken",
    )

    assert _python_constant(python_types, "ASSET_ORIGIN_REGISTRATION_COMMAND_V2") == (
        "register_asset_origin"
    )
    assert _rust_const_expression(
        rust_types,
        "ASSET_ORIGIN_REGISTRATION_COMMAND_V2",
    ) == '"register_asset_origin"'
    assert _python_constant(python_asset_types, "ASSET_ATOM_DECIMALS_V2") == 8
    assert _rust_const_expression(rust_asset_types, "ASSET_ATOM_DECIMALS_V2") == "8"
    assert _python_constant(python_asset_types, "ASSET_LANE_PRODUCTION_AUTHORITY_V2") == (
        "NONE"
    )
    assert _rust_const_expression(
        rust_asset_types,
        "ASSET_LANE_PRODUCTION_AUTHORITY_V2",
    ) == '"NONE"'
    zero_root = "0x" + "00" * 32
    assert _python_constant(python_primitives, "ZERO_ROOT_V2") == zero_root
    assert _rust_const_expression(rust_canonical, "ZERO_ROOT_V2") == f'"{zero_root}"'
    witness_roots = re.findall(
        r'^def opaqueRoot[AB] : Root :=\s*\n\s*"(0x[0-9a-f]+)"$',
        lean_source,
        re.MULTILINE,
    )
    assert len(witness_roots) == 2
    assert len(set(witness_roots)) == 2
    assert all(len(root) == 66 and root != zero_root for root in witness_roots)

    python_lane_entries = _python_enum_entries(python_primitives, "LaneIdV2")
    assert python_lane_entries[0] == ("ASSET_TRANSFER", "ASSET_TRANSFER")
    rust_lane_members = _rust_enum_members(
        RUST_EFFECT_VALUES.read_text(encoding="utf-8"),
        "LaneIdV2",
    )
    assert rust_lane_members[0] == "ASSET_TRANSFER"
    assert _lean_inductive_members(lean_source, "LaneId") == ("assetTransfer",)

    for fragment in (
        "rows=()",
        "asset_conservation=()",
        "fee_conservation=()",
        "LaneIdV2.ASSET_TRANSFER",
        "occurrence_consumptions=(occurrence.occurrence_id,)",
        "external_outbox_enqueue=()",
        "private_port_root=ZERO_ROOT_V2",
        "terminal_obligations_root=ZERO_ROOT_V2",
        "oracle_occurrence_plan_root=ZERO_ROOT_V2",
    ):
        assert fragment in python_transition

    rust_effect_builder = _rust_function_slice(
        rust_transition,
        "build_effect_plan",
        "build_module_journal",
    )
    for fragment in (
        "rows: Vec::new()",
        "asset_conservation: Vec::new()",
        "fee_conservation: Vec::new()",
        "lane_id: LaneIdV2::ASSET_TRANSFER",
        "occurrence_consumptions: vec![occurrence_id]",
        "external_outbox_enqueue: Vec::new()",
    ):
        assert fragment in rust_effect_builder

    for fragment in (
        "laneId := .assetTransfer",
        "preStateRoot := ctx.preStateRootObservation",
        "postStateRoot := ctx.postStateRootObservation",
        "occurrenceConsumptions := [occurrence.occurrenceId]",
        "valueEffects := []",
        "externalOutbox := []",
        'def productionAuthority : String := "NONE"',
        f'def zeroRoot : Root := "{zero_root}"',
    ):
        assert fragment in lean_source


def test_proof_declaration_surface_is_closed_and_model_compiles(
    compiled_packet: CompiledPacket,
) -> None:
    del compiled_packet
    source = PROOF.read_text(encoding="utf-8")
    assert _proof_declarations(source) == DECLARATIONS


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


def test_every_proof_declaration_uses_only_standard_axioms(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
) -> None:
    probe = tmp_path / "AssetOriginRegistryRefinementV2Axioms.lean"
    probe.write_text(
        "import Proofs.AssetOriginRegistryRefinementV2\n"
        + "\n".join(f"#print axioms {NAMESPACE}.{name}" for _, name in DECLARATIONS)
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
    reports = _axiom_reports(result.stdout)
    expected_names = tuple(f"{NAMESPACE}.{name}" for _, name in DECLARATIONS)
    assert tuple(name for name, _ in reports) == expected_names
    for _, dependencies in reports:
        assert dependencies <= ALLOWED_STANDARD_AXIOMS


def test_claim_ceiling_stays_explicit() -> None:
    source = PROOF.read_text(encoding="utf-8")
    assert 'def productionAuthority : String := "NONE"' in source
    for term in (
        "source-pinned abstract model",
        "ValidState",
        "ValidCommand",
        "cryptographic hashes",
        "Python/Rust/Lean execution equivalence",
        "universal refinement proof",
        "256-asset admission cap",
        "unbounded runtime acceptance",
        "mounting",
        "settlement",
        "migration",
        "release",
        "production authority",
    ):
        assert term in source
