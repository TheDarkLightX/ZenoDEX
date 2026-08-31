from __future__ import annotations

import ast
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import TypedDict

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
CORE = LEAN_DIR / "Proofs" / "GlobalSettlementCoreV2.lean"
OUTCOME = LEAN_DIR / "Proofs" / "GlobalEconomicRefinementOutcomeV2.lean"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"
PYTHON_OUTCOME = ROOT / "src" / "core" / "global_economic_refinement_outcome_v2.py"
RUST_OUTCOME = ROOT / "zk" / "global_settlement_abi_v2" / "src" / "outcome.rs"

NAMESPACE = "Proofs.GlobalEconomicRefinementOutcomeV2"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"
PINNED_SOURCES = {
    PYTHON_OUTCOME: "953d39c231cd46978d40ea7e06879c9e88fc74ff0564f5873b432e02fb5f11de",
    RUST_OUTCOME: "4ac6535a809f0c617fcb58a238ca0f22cfa8d09da030eb12bf93f5bafdd805f4",
}

EXPECTED_WIRE_CODES = (
    "MALFORMED_CANDIDATE",
    "EXTERNAL_OUTBOX_REQUIRES_PUBLISHER",
    "ZERO_OCCURRENCE_NOT_STATIC",
    "FIXED_CONTEXT_CHANGED",
    "LANE_OWNERSHIP_CHANGED",
    "DISABLED_LANE_WRITE",
    "LANE_WRITE_COVERAGE_MISMATCH",
    "LANE_WRITE_ROOT_MISMATCH",
    "SIGNED_STATE_DELTA_OVERFLOW",
    "BALANCES_STATE_EFFECT_MISMATCH",
    "CUSTODY_STATE_EFFECT_MISMATCH",
    "LIABILITIES_STATE_EFFECT_MISMATCH",
    "RESERVES_STATE_EFFECT_MISMATCH",
    "SUPPLY_EFFECT_TOTAL_OVERFLOW",
    "SUPPLY_ISSUE_BURN_MISMATCH",
    "OWNED_ACCOUNTING_TOTAL_OVERFLOW",
    "OWNED_TOTAL_NOT_SUPPLY",
    "CONSERVATION_ASSET_COVERAGE_MISMATCH",
    "CONSERVATION_STATE_MISMATCH",
    "ANNOTATION_MIRROR_OVERFLOW",
    "FEE_ALLOCATION_NOT_MIRRORED",
    "REWARD_OR_SLASH_NOT_MIRRORED",
    "ZERO_FEE_CONSERVATION_ROW",
    "FEE_RESIDUE_OVERFLOW",
    "FEE_RESIDUE_STATE_MISMATCH",
    "CUSTODY_BACKING_TOTAL_OVERFLOW",
    "LIABILITY_TOTAL_OVERFLOW",
    "LIABILITIES_EXCEED_BACKING",
    "OPEN_TERMINAL_TOTAL_OVERFLOW",
    "OPEN_TERMINAL_EXCEEDS_LIABILITY",
    "TERMINAL_LIABILITY_DELTA_OVERFLOW",
    "TERMINAL_PRE_STATE_MISMATCH",
    "TERMINAL_OWNING_LANE_WRITE_MISSING",
    "TERMINAL_PLAN_MISMATCH",
    "TERMINAL_LIABILITY_MISMATCH",
    "ORACLE_LANE_WRITE_MISSING",
    "ORACLE_PRE_STATE_MISMATCH",
    "ORACLE_PLAN_MISMATCH",
    "OCCURRENCES_NOT_ORDERED_UNIQUE",
    "REPLAY_CONSUMPTION_MISMATCH",
    "OCCURRENCE_CONTEXT_MISMATCH",
    "REPLAY_ALREADY_CONSUMED",
    "REPLAY_POST_STATE_MISMATCH",
    "HEIGHT_PROGRESSION_MISMATCH",
    "OCCURRENCE_HEIGHT_MISMATCH",
    "INTERNAL_CONTRACT_DRIFT",
)

THEOREMS = (
    "production_authority_is_none",
    "all_reject_codes_length",
    "all_reject_codes_wire_order",
    "all_reject_codes_complete",
    "all_reject_codes_no_duplicates",
    "all_reject_code_wires_no_duplicates",
    "RejectCode.wire_injective",
    "known_validation_preserves_code",
    "unknown_validation_maps_to_internal_contract_drift",
    "external_outbox_precedes_zero_occurrence",
    "zero_occurrence_selected_when_outbox_absent",
    "rejected_post_state_root_is_pre_state_root",
    "rejected_effect_plan_is_empty",
    "rejected_terminal_and_oracle_plans_are_empty",
    "rejected_consumes_no_occurrences",
    "rejected_outbox_is_empty",
    "rejected_authority_is_none",
    "rejected_outcome_is_complete_no_op",
    "every_reject_code_is_complete_no_op",
)

ALLOWED_STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})


class CompiledPacket(TypedDict):
    root: Path
    lean: Path
    env: dict[str, str]


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "formal V2 outcome gate requires lake"
    return lake


def _worktree_paths() -> tuple[Path, ...]:
    result = subprocess.run(
        ["git", "worktree", "list", "--porcelain"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    return tuple(
        Path(line.removeprefix("worktree "))
        for line in result.stdout.splitlines()
        if line.startswith("worktree ")
    )


def _cached_lean_directory() -> Path:
    """Reuse one existing pinned cache without materializing another mathlib."""

    for worktree in (ROOT, *_worktree_paths()):
        lean_dir = worktree / "lean-mathlib"
        if not (
            (lean_dir / "lean-toolchain").is_file()
            and (lean_dir / ".lake" / "packages" / "mathlib").exists()
            and (worktree / "external" / "mathlib4").exists()
        ):
            continue
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
    build_root = tmp_path_factory.mktemp("global-refinement-outcome-v2-lean")
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
    environment["LEAN_PATH"] = os.pathsep.join((str(build_root), path_result.stdout.strip()))

    for target in (CORE, OUTCOME):
        module_output = build_root / "Proofs" / f"{target.stem}.olean"
        result = subprocess.run(
            [
                str(lean),
                "-DwarningAsError=true",
                "-o",
                str(module_output),
                str(target),
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

    return {"root": build_root, "lean": lean, "env": environment}


def _run_lean_probe(
    compiled_packet: CompiledPacket,
    path: Path,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(compiled_packet["lean"]), "-DwarningAsError=true", str(path)],
        cwd=ROOT,
        env=compiled_packet["env"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=300,
        check=False,
    )


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _python_enum_codes(source: str) -> tuple[str, ...]:
    tree = ast.parse(source)
    enum_class = next(
        node
        for node in tree.body
        if isinstance(node, ast.ClassDef) and node.name == "GlobalEconomicRefinementRejectCodeV2"
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
        r"pub enum GlobalEconomicRefinementRejectCodeV2 \{(?P<body>.*?)^\}",
        source,
    ).group("body")
    return tuple(re.findall(r"^\s{4}([A-Z][A-Z0-9_]+),$", body, re.MULTILINE))


def _rust_registry_codes(source: str) -> tuple[str, ...]:
    body = _required_match(
        r"pub const ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2:.*?= \["
        r"(?P<body>.*?)^\];",
        source,
    ).group("body")
    return tuple(
        re.findall(
            r"GlobalEconomicRefinementRejectCodeV2::([A-Z][A-Z0-9_]+)",
            body,
        )
    )


def _rust_wire_codes(source: str) -> tuple[str, ...]:
    body = _required_match(
        r"pub const fn as_str\(self\).*?match self \{(?P<body>.*?)^\s{8}\}",
        source,
    ).group("body")
    pairs = re.findall(
        r"Self::([A-Z][A-Z0-9_]+)\s*=>\s*\"([A-Z][A-Z0-9_]+)\"",
        body,
    )
    assert all(variant == wire for variant, wire in pairs)
    return tuple(wire for _, wire in pairs)


def _lean_wire_codes(source: str) -> tuple[str, ...]:
    body = _required_match(
        r"def RejectCode\.wire.*?(?P<body>.*?)^def allRejectCodes",
        source,
    ).group("body")
    return tuple(re.findall(r'=>\s*"([A-Z][A-Z0-9_]+)"', body))


def _theorem_names(source: str) -> tuple[str, ...]:
    return tuple(re.findall(r"^theorem\s+([A-Za-z0-9_.]+)", source, re.MULTILINE))


def _axiom_dependencies(output: str) -> set[str]:
    dependencies: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL):
        dependencies.update(item.strip() for item in body.split(",") if item.strip())
    return dependencies


def _run_scanner(path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCANNER), str(path), "--json"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )


def test_packet_compiles_with_pinned_lean_and_warnings_as_errors(
    compiled_packet: CompiledPacket,
) -> None:
    assert compiled_packet["lean"].is_file()


def test_python_and_rust_outcome_sources_are_exactly_pinned() -> None:
    for path, expected_sha256 in PINNED_SOURCES.items():
        source = path.read_bytes()
        assert _sha256(source) == expected_sha256
        assert _sha256(source + b"\n") != expected_sha256


def test_python_rust_and_lean_reject_registries_have_exact_wire_order() -> None:
    python_source = PYTHON_OUTCOME.read_text(encoding="utf-8")
    rust_source = RUST_OUTCOME.read_text(encoding="utf-8")
    lean_source = OUTCOME.read_text(encoding="utf-8")

    assert len(EXPECTED_WIRE_CODES) == 46
    assert len(set(EXPECTED_WIRE_CODES)) == 46
    assert _python_enum_codes(python_source) == EXPECTED_WIRE_CODES
    assert _rust_enum_codes(rust_source) == EXPECTED_WIRE_CODES
    assert _rust_registry_codes(rust_source) == EXPECTED_WIRE_CODES
    assert _rust_wire_codes(rust_source) == EXPECTED_WIRE_CODES
    assert _lean_wire_codes(lean_source) == EXPECTED_WIRE_CODES


def test_runtime_source_shapes_keep_unknown_drift_and_complete_no_op() -> None:
    python_source = PYTHON_OUTCOME.read_text(encoding="utf-8")
    rust_source = RUST_OUTCOME.read_text(encoding="utf-8")

    assert "_CODE_BY_VALIDATION_MESSAGE_V2.get(" in python_source
    assert "GlobalEconomicRefinementRejectCodeV2.INTERNAL_CONTRACT_DRIFT" in (python_source)
    assert 'object.__setattr__(self, "post_state_root", pre_state_root)' in (python_source)
    assert "return GlobalEconomicEffectPlanV2.empty()" in python_source
    assert "return GlobalTerminalObligationPlanV2.empty()" in python_source
    assert "return GlobalOracleOccurrencePlanV2.empty()" in python_source

    assert "_ => Code::INTERNAL_CONTRACT_DRIFT" in rust_source
    assert "&self.pre_state_root" in rust_source
    assert "GlobalEconomicEffectPlanV2::empty()" in rust_source
    assert "GlobalTerminalObligationPlanV2::empty()" in rust_source
    assert "GlobalOracleOccurrencePlanV2::empty()" in rust_source


def test_repository_placeholder_scanner_is_clean_and_rejects_injection(
    tmp_path: Path,
) -> None:
    assert SCANNER.is_file()
    clean = _run_scanner(OUTCOME)
    assert clean.returncode == 0, clean.stdout + clean.stderr
    clean_payload = json.loads(clean.stdout)
    assert clean_payload["blocked"] is False
    assert clean_payload["match_count"] == 0
    assert clean_payload["axiom_check"] is True

    injected = tmp_path / "InjectedPlaceholder.lean"
    injected.write_text("theorem injected : True := by\n  sorry\n", encoding="utf-8")
    blocked = _run_scanner(injected)
    assert blocked.returncode == 1, blocked.stdout + blocked.stderr
    blocked_payload = json.loads(blocked.stdout)
    assert blocked_payload["blocked"] is True
    assert blocked_payload["match_count"] == 1
    assert blocked_payload["matches"][0]["rule"] == "lean_sorry"


def test_theorem_surface_is_exact_and_removal_is_observable() -> None:
    source = OUTCOME.read_text(encoding="utf-8")
    assert _theorem_names(source) == THEOREMS

    weakened = source.replace(
        "theorem every_reject_code_is_complete_no_op",
        "lemma every_reject_code_is_complete_no_op",
        1,
    )
    assert _theorem_names(weakened) != THEOREMS


def test_theorem_surface_uses_only_standard_axioms(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
) -> None:
    qualified = tuple(f"{NAMESPACE}.{name}" for name in THEOREMS)
    probe = tmp_path / "GlobalEconomicRefinementOutcomeV2Axioms.lean"
    probe.write_text(
        "import Proofs.GlobalEconomicRefinementOutcomeV2\n\n"
        + "\n".join(f"#print axioms {name}" for name in qualified)
        + "\n",
        encoding="utf-8",
    )
    result = _run_lean_probe(compiled_packet, probe)
    assert result.returncode == 0, result.stdout + result.stderr
    for name in qualified:
        assert f"'{name}'" in result.stdout, name
    assert _axiom_dependencies(result.stdout) <= ALLOWED_STANDARD_AXIOMS


def test_semantic_theorem_signatures_are_compiler_bound(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
) -> None:
    expected_list = ",\n      ".join(f'"{code}"' for code in EXPECTED_WIRE_CODES)
    probe = tmp_path / "GlobalEconomicRefinementOutcomeV2Signatures.lean"
    probe.write_text(
        f"""import Proofs.GlobalEconomicRefinementOutcomeV2

namespace Proofs.GlobalEconomicRefinementOutcomeV2Signatures
open GlobalSettlementCoreV2 GlobalEconomicRefinementOutcomeV2

example : outcomeAuthority = "NONE" := production_authority_is_none
example : allRejectCodes.length = 46 := all_reject_codes_length
example : allRejectCodes.map RejectCode.wire =
    [ {expected_list} ] := all_reject_codes_wire_order
example (code : RejectCode) : code ∈ allRejectCodes :=
  all_reject_codes_complete code
example : allRejectCodes.Nodup := all_reject_codes_no_duplicates
example : (allRejectCodes.map RejectCode.wire).Nodup :=
  all_reject_code_wires_no_duplicates
example {{left right : RejectCode}} (sameWire : left.wire = right.wire) :
    left = right := RejectCode.wire_injective sameWire
example (code : RejectCode) : classifyValidation (.mapped code) = code :=
  known_validation_preserves_code code
example : classifyValidation .unknown = .internalContractDrift :=
  unknown_validation_maps_to_internal_contract_drift
example : firstValidationFailure outboxAndZeroOccurrenceFailures =
    some .externalOutboxRequiresPublisher :=
  external_outbox_precedes_zero_occurrence
example : firstValidationFailure ⟨false, true⟩ = some .zeroOccurrenceNotStatic :=
  zero_occurrence_selected_when_outbox_absent
example (rejected : RejectedOutcome) :
    rejected.postStateRoot = rejected.preStateRoot :=
  rejected_post_state_root_is_pre_state_root rejected
example (rejected : RejectedOutcome) : rejected.effectPlan.IsEmpty :=
  rejected_effect_plan_is_empty rejected
example (rejected : RejectedOutcome) :
    rejected.terminalPlanDeltas = [] ∧ rejected.oraclePlanDeltas = [] :=
  rejected_terminal_and_oracle_plans_are_empty rejected
example (rejected : RejectedOutcome) : rejected.consumedOccurrences = [] :=
  rejected_consumes_no_occurrences rejected
example (rejected : RejectedOutcome) : rejected.outbox = [] :=
  rejected_outbox_is_empty rejected
example (rejected : RejectedOutcome) : rejected.productionAuthority = "NONE" :=
  rejected_authority_is_none rejected
example (rejected : RejectedOutcome) : CompleteNoOp rejected :=
  rejected_outcome_is_complete_no_op rejected
example : ∀ code preStateRoot, CompleteNoOp (reject code preStateRoot) :=
  every_reject_code_is_complete_no_op

end Proofs.GlobalEconomicRefinementOutcomeV2Signatures
""",
        encoding="utf-8",
    )
    result = _run_lean_probe(compiled_packet, probe)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""


def test_claim_boundary_keeps_all_authority_and_runtime_nonclaims_explicit() -> None:
    source = OUTCOME.read_text(encoding="utf-8")
    for phrase in (
        "no Python/Rust runtime refinement",
        "verifier or",
        "publisher authority",
        "settlement or value-moving authority",
        "migration result",
        "release status",
        "production readiness",
        "do not mount a runtime route",
    ):
        assert phrase in source
