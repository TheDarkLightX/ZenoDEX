"""Source-pinned formal gate for the V2 asset-origin registry model.

The Lean model covers the exact 13-code protocol rejection order on an explicit
valid-state/valid-command domain, rejection no-op behavior, deterministic
record insertion, exact release/policy preservation, exact rejection selection,
successor-order coverage, and the authority-free typed accepted effect shape,
including the shared 256-record capacity boundary.
Python and Rust source hashes plus deterministic semantic extractors reopen
this review when the modeled source surface changes.

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
from dataclasses import dataclass, field
from pathlib import Path

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
PYTHON_RESOURCE_LIMITS = (
    ROOT / "src" / "core" / "global_settlement_resource_limits_v2.py"
)
RUST_ASSET_TYPES = (
    ROOT / "zk" / "global_settlement_abi_v2" / "src" / "asset_transfer_types.rs"
)
RUST_CANONICAL = ROOT / "zk" / "global_settlement_abi_v2" / "src" / "canonical.rs"
RUST_EFFECT_VALUES = (
    ROOT / "zk" / "global_settlement_abi_v2" / "src" / "effect_values.rs"
)
RUST_EFFECT_PLAN = ROOT / "zk" / "global_settlement_abi_v2" / "src" / "effects.rs"
RUST_PROOF = ROOT / "zk" / "global_settlement_abi_v2" / "src" / "proof.rs"
RUST_RESOURCE_LIMITS = (
    ROOT / "zk" / "global_settlement_abi_v2" / "src" / "resource_limits.rs"
)

NAMESPACE = "Proofs.AssetOriginRegistryRefinementV2"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"
PINNED_SOURCES = {
    PYTHON_TYPES: "45665fa755a0f806474feed0856c9a5b4630bd98a4c9d1d924809b5109587e39",
    PYTHON_TRANSITION: "b1846290fcdf2dc7255e54933ceca076e2ab3f3f07f5c1cf8fca0909bad30659",
    RUST_TYPES: "f51dedc44e9546de4216f36a6634e06789273fbaa16d8ce8012d8e4d6829397a",
    RUST_TRANSITION: "0ace78787e46575ea225ba975d164b946dc8cfca44588b5d444cc61e4b34d647",
    PYTHON_ASSET_TYPES: "ec067739d9da4a409347e8525c16188ecfcaad1e6b75172bfe1ca93e17cec40c",
    PYTHON_PRIMITIVES: "11a26694357812e91b398bddc2b6bbec0a93063731ccd5b23818de1d0c0ca01e",
    PYTHON_EFFECT_VALUES: "a366616f8a11f35d5c69d29c91e1d0b8598ac48499eb44d86d8011c73d30fb9a",
    PYTHON_EFFECT_PLAN: "e352b67a13ac22e09d31d5aebf94d10aa7f540ef3149050ed2675854f6b839f0",
    PYTHON_PROOF: "1ed46aad640fd1e887d228bbace65fc9f2449f6bbb16428a16537b9d9cc95ae4",
    PYTHON_SETTLEMENT_FACADE: "5c8c94f75f26b32b8b72b1a608600012b5a22152014202616162ed7b30cee58f",
    PYTHON_RESOURCE_LIMITS: "92c2211d9e1ccc7b0e3f03da8cc0c4cc4ab9d9acba86006c352a7aec43dd06ad",
    RUST_ASSET_TYPES: "994f3cbc8609444015e61f054c6ce5c57e1d5d9531f29f6f8b1e6afda8a41fc3",
    RUST_CANONICAL: "b17a76d6e8ce5915ba1d250982147dceda0d7368911b396f7ae83fd860216053",
    RUST_EFFECT_VALUES: "2546015b68ddf0197cdf584dcefde8a7d7ae0eb6d77e24f98ba86fb375400f24",
    RUST_EFFECT_PLAN: "031e732c7512a68d577a23be2354ede51b57324c6ee666b93d62b509ded41f7d",
    RUST_PROOF: "0314ef43cc82bd358c627420d4463d8dc682d9e86138cb57a8fac10371c55781",
    RUST_RESOURCE_LIMITS: "b3415d5389be553420916477d646ebfaf6b9b6c1e395df445fcab5cf2b448244",
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
    "REGISTRY_CAPACITY_EXCEEDED",
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
    ("theorem", "replicate_a_lt_of_lt"),
    ("theorem", "capacity_key_lt"),
    ("theorem", "capacity_key_injective"),
    ("theorem", "capacity_witness_state_valid"),
    ("theorem", "capacity_key_ne_witness_asset"),
    ("theorem", "capacity_key_ne_witness_origin"),
    ("theorem", "capacity_witness_has_no_asset"),
    ("theorem", "capacity_witness_has_no_origin"),
    ("theorem", "capacity_witness_has_origin_zero"),
    ("theorem", "capacity_witness_reject_code"),
    ("theorem", "capacity_duplicate_origin_reject_code"),
    ("theorem", "full_capacity_rejection_witness"),
    ("theorem", "every_reject_code_reachable_on_valid_domain"),
    ("theorem", "next_reject_code_iff_rank_successor"),
    ("theorem", "next_reject_code_iff_mem_successor_edges"),
    ("theorem", "reject_successor_edges_exact_coverage"),
    ("theorem", "adjacent_double_failure_precedence"),
    ("theorem", "rejected_is_exact_noop"),
    ("theorem", "rejected_carries_exact_selector"),
    ("theorem", "accepted_has_exact_effect_shape"),
    ("theorem", "accepted_preserves_module_release_id_and_exact_policy"),
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

SEMANTIC_MUTATIONS = (
    (
        "accepted_policy_authority_subject_rewrite",
        "  policy := pre.policy\n",
        '  policy := { pre.policy with authoritySubject := "mutated-authority" }\n',
        "accepted_preserves_module_release_id_and_exact_policy",
    ),
    (
        "rejected_non_capacity_code_remap",
        "      code := code\n",
        (
            "      code :=\n"
            "        if code = .registryCapacityExceeded then code "
            "else .missingOccurrence\n"
        ),
        "rejected_carries_exact_selector",
    ),
    (
        "missing_occurrence_successor_skip",
        "  | .missingOccurrence => some .occurrenceBindingMismatch\n",
        "  | .missingOccurrence => some .unauthorizedSubject\n",
        "next_reject_code_iff_rank_successor",
    ),
)


@dataclass(frozen=True, slots=True)
class CompiledPacket:
    root: Path
    lean: Path
    environment: dict[str, str] = field(repr=False)


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
    return CompiledPacket(root=build_root, lean=lean, environment=environment)


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


def _python_constant_reference(source: str, name: str) -> str:
    tree = ast.parse(source)
    for node in tree.body:
        if (
            isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.target.id == name
            and isinstance(node.value, ast.Name)
        ):
            return node.value.id
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


def _compile_lean_file(
    compiled_packet: CompiledPacket,
    source: Path,
) -> subprocess.CompletedProcess[str]:
    command = [str(compiled_packet.lean), "-DwarningAsError=true"]
    command.append(str(source))
    return subprocess.run(
        command,
        cwd=ROOT,
        env=compiled_packet.environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=300,
        check=False,
    )


def _declaration_line_span(source: str, theorem: str) -> tuple[int, int]:
    declaration = _required_match(
        rf"^theorem {re.escape(theorem)}(?=\s|:)",
        source,
    )
    start = source.count("\n", 0, declaration.start()) + 1
    following = re.search(
        r"^(?:def|theorem|lemma|structure|inductive|instance)\s+",
        source[declaration.end() :],
        re.MULTILINE,
    )
    end_offset = (
        len(source)
        if following is None
        else declaration.end() + following.start()
    )
    end = source.count("\n", 0, end_offset) + 1
    return start, end


def _lean_diagnostic_lines(output: str, source: Path) -> tuple[int, ...]:
    return tuple(
        int(line)
        for line in re.findall(
            rf"{re.escape(str(source))}:(\d+):\d+: (?:error|warning):",
            output,
        )
    )


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
    python_resource_limits = PYTHON_RESOURCE_LIMITS.read_text(encoding="utf-8")
    python_transition = _python_function_source(
        PYTHON_TRANSITION.read_text(encoding="utf-8"),
        "transition_asset_origin_registration_v2",
    )
    rust_types = RUST_TYPES.read_text(encoding="utf-8")
    rust_asset_types = RUST_ASSET_TYPES.read_text(encoding="utf-8")
    rust_transition = RUST_TRANSITION.read_text(encoding="utf-8")
    rust_canonical = RUST_CANONICAL.read_text(encoding="utf-8")
    rust_resource_limits = RUST_RESOURCE_LIMITS.read_text(encoding="utf-8")
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
    assert _python_constant_reference(
        python_types,
        "MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2",
    ) == "MAX_ASSETS_PER_ASSET_STATE_V2"
    assert _python_constant(
        python_resource_limits,
        "MAX_ASSETS_PER_ASSET_STATE_V2",
    ) == 256
    assert _rust_const_expression(
        rust_types,
        "MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2",
    ) == "MAX_ASSETS_PER_ASSET_STATE_V2"
    assert _rust_const_expression(
        rust_resource_limits,
        "MAX_ASSETS_PER_ASSET_STATE_V2",
    ) == "256"
    assert "def maxAssetOriginRegistryAssets : Nat := 256" in lean_source
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
    assert "environment" not in repr(compiled_packet)
    source = PROOF.read_text(encoding="utf-8")
    assert _proof_declarations(source) == DECLARATIONS


def test_load_bearing_semantic_theorem_signatures_compile(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
) -> None:
    probe = tmp_path / "AssetOriginRegistryRefinementV2Signatures.lean"
    probe.write_text(
        """import Proofs.AssetOriginRegistryRefinementV2

open Proofs.AssetOriginRegistryRefinementV2

example {ctx : Context} {pre : State} {command : Command} {accepted : Accepted}
    (h : transition ctx pre command = .accepted accepted) :
    accepted.post.moduleReleaseId = pre.moduleReleaseId ∧
      accepted.post.policy = pre.policy ∧
      accepted.post.policy.authoritySubject = pre.policy.authoritySubject ∧
      accepted.post.policy.authorityGrantRoot = pre.policy.authorityGrantRoot ∧
      accepted.post.policy.allowNative = pre.policy.allowNative ∧
      accepted.post.policy.allowTauOriginated = pre.policy.allowTauOriginated :=
  accepted_preserves_module_release_id_and_exact_policy h

example {ctx : Context} {pre : State} {command : Command} {rejected : Rejected}
    (h : transition ctx pre command = .rejected rejected) :
    rejectCode ctx pre command = some rejected.code :=
  rejected_carries_exact_selector h

example (current successor : RejectCode) :
    nextRejectCode current = some successor ↔
      successor.rank = current.rank + 1 :=
  next_reject_code_iff_rank_successor current successor

example (current successor : RejectCode) :
    nextRejectCode current = some successor ↔
      (current, successor) ∈ rejectSuccessorEdges :=
  next_reject_code_iff_mem_successor_edges current successor

example :
    rejectSuccessorEdges = allRejectCodes.zip allRejectCodes.tail ∧
      rejectSuccessorEdges.length = allRejectCodes.length - 1 ∧
      rejectSuccessorEdges.length = 12 ∧ rejectSuccessorEdges.Nodup ∧
      ∀ current successor,
        (current, successor) ∈ rejectSuccessorEdges ↔
          successor.rank = current.rank + 1 :=
  reject_successor_edges_exact_coverage
""",
        encoding="utf-8",
    )
    result = _compile_lean_file(compiled_packet, probe)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""


@pytest.mark.parametrize(
    ("mutation_name", "original", "replacement", "load_bearing_theorem"),
    SEMANTIC_MUTATIONS,
    ids=tuple(mutation[0] for mutation in SEMANTIC_MUTATIONS),
)
def test_semantic_mutations_fail_inside_load_bearing_theorem(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
    mutation_name: str,
    original: str,
    replacement: str,
    load_bearing_theorem: str,
) -> None:
    source = PROOF.read_text(encoding="utf-8")
    assert source.count(original) == 1, mutation_name
    mutated_source = source.replace(original, replacement)
    theorem_start, theorem_end = _declaration_line_span(
        mutated_source,
        load_bearing_theorem,
    )
    mutant = tmp_path / f"AssetOriginRegistryRefinementV2_{mutation_name}.lean"
    mutant.write_text(mutated_source, encoding="utf-8")

    result = _compile_lean_file(
        compiled_packet,
        mutant,
    )
    diagnostics = result.stdout + result.stderr
    assert result.returncode != 0, mutation_name
    error_lines = _lean_diagnostic_lines(diagnostics, mutant)
    assert any(theorem_start <= line < theorem_end for line in error_lines), (
        mutation_name,
        load_bearing_theorem,
        error_lines,
        diagnostics,
    )


def test_compiled_packet_repr_cannot_disclose_environment_values() -> None:
    packet = CompiledPacket(
        root=Path("bounded-build-root"),
        lean=Path("pinned-lean"),
        environment={"FORMAL_GATE_SECRET": "environment-secret-sentinel"},
    )
    rendered = repr(packet)
    assert "environment" not in rendered
    assert "FORMAL_GATE_SECRET" not in rendered
    assert "environment-secret-sentinel" not in rendered


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
            str(compiled_packet.lean),
            "-DwarningAsError=true",
            str(probe),
        ],
        cwd=ROOT,
        env=compiled_packet.environment,
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
        "shared 256-record registry ceiling",
        "all other resource bounds",
        "unbounded runtime acceptance",
        "mounting",
        "settlement",
        "migration",
        "release",
        "production authority",
    ):
        assert term in source
