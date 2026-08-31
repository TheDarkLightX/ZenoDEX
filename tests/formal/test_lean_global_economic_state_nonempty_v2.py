"""Fail-closed gate for the V2 nonempty global refinement witness.

The Lean witness models one bounded asset transfer across the combined global
state, effect, conservation, lane-write, replay, and pre-O-009 outbox relation.
It is non-vacuity evidence only.  It grants no Python/Rust execution
refinement, runtime reachability, verifier authority, settlement authority,
release status, or production readiness.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
CORE = LEAN_DIR / "Proofs" / "GlobalSettlementCoreV2.lean"
REFINEMENT = LEAN_DIR / "Proofs" / "GlobalEconomicStateRefinementV2.lean"
NONEMPTY = (
    LEAN_DIR / "Proofs" / "GlobalEconomicStateRefinementV2Nonempty.lean"
)
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"

NAMESPACE = "Proofs.GlobalEconomicStateRefinementV2Nonempty"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"
PINNED_SOURCES = {
    CORE: "2ce254367dc8e8299f82f8a93e09c1d470f3a218ed01af7efb766946a34255a4",
    REFINEMENT: "c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1",
    NONEMPTY: "b62aef117f9eac23905b943f98e0b692b90535e8031762e41d76464ffa9858ce",
}
THEOREMS = (
    "transfer_pre_quantities_admitted",
    "transfer_post_quantities_admitted",
    "transfer_effect_plan_admitted",
    "transfer_states_preserve_owned_supply",
    "transfer_balance_delta_identity",
    "transfer_running_deltas_fit",
    "transfer_account_table_exact",
    "transfer_state_bearing_aggregates_fit",
    "transfer_global_state_verified",
    "combined_verified_relation_has_nonempty_asset_transfer",
)
ALLOWED_STANDARD_AXIOMS = frozenset(
    {"propext", "Quot.sound", "Classical.choice"}
)


@dataclass(frozen=True, slots=True)
class CompiledPacket:
    root: Path
    lean: Path
    environment: dict[str, str] = field(repr=False)


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "nonempty global refinement gate requires lake"
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
    return tuple(dict.fromkeys((ROOT, common_dir.parent)))


def _cached_lean_directory() -> Path:
    for candidate in _repository_candidates():
        lean_dir = candidate / "lean-mathlib"
        if (
            (lean_dir / "lean-toolchain").is_file()
            and (lean_dir / ".lake" / "packages" / "mathlib").exists()
            and (candidate / "external" / "mathlib4").exists()
        ):
            actual_toolchain = (lean_dir / "lean-toolchain").read_text(
                encoding="utf-8"
            ).strip()
            assert actual_toolchain == PINNED_TOOLCHAIN
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
    build_root = tmp_path_factory.mktemp("global-economic-nonempty-v2-lean")
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

    for source in (CORE, REFINEMENT, NONEMPTY):
        output = build_root / "Proofs" / f"{source.stem}.olean"
        result = subprocess.run(
            [
                str(lean),
                "-DwarningAsError=true",
                "-o",
                str(output),
                str(source),
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
        assert output.is_file()

    return CompiledPacket(root=build_root, lean=lean, environment=environment)


def _run_probe(
    compiled_packet: CompiledPacket, path: Path
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(compiled_packet.lean), "-DwarningAsError=true", str(path)],
        cwd=ROOT,
        env=compiled_packet.environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=300,
        check=False,
    )


_AXIOM_RESULT = re.compile(
    r"'(?P<name>[^'\n]+)'\s+"
    r"(?:does not depend on any axioms|"
    r"depends on axioms:\s*\[(?P<axioms>[^\]]*)\])",
    re.DOTALL,
)
_AXIOM_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*")


def _parse_axiom_report(
    output: str, expected_theorems: tuple[str, ...]
) -> dict[str, frozenset[str]]:
    parsed: dict[str, frozenset[str]] = {}
    matches = tuple(_AXIOM_RESULT.finditer(output))
    for match in matches:
        name = match.group("name")
        if name in parsed:
            raise ValueError(f"duplicate axiom result: {name}")
        body = match.group("axioms")
        if body is None:
            parsed[name] = frozenset()
            continue
        names = tuple(item.strip() for item in body.split(","))
        if not names or any(not _AXIOM_NAME.fullmatch(item) for item in names):
            raise ValueError(f"malformed axiom list for {name}")
        parsed[name] = frozenset(names)

    if tuple(parsed) != expected_theorems:
        raise ValueError(
            f"axiom theorem sequence mismatch: {tuple(parsed)!r}"
        )
    if _AXIOM_RESULT.sub("", output).strip():
        raise ValueError("unrecognized axiom report output")
    return parsed


def test_sources_are_exactly_pinned() -> None:
    for source, expected_sha256 in PINNED_SOURCES.items():
        assert source.is_file(), source
        assert hashlib.sha256(source.read_bytes()).hexdigest() == expected_sha256


def test_packet_compiles_with_pinned_lean_and_warnings_as_errors(
    compiled_packet: CompiledPacket,
) -> None:
    assert compiled_packet.lean.is_file()
    assert "environment" not in repr(compiled_packet)


@pytest.mark.parametrize(
    "output",
    (
        "",
        "'Demo.theorem' uses axioms: [Evil.ax]",
        "'Demo.theorem' depends on axioms: []",
        "'Demo.theorem' depends on axioms: [propext]\ntrailing output",
        "'Demo.theorem' does not depend on any axioms\n"
        "'Demo.theorem' does not depend on any axioms",
    ),
)
def test_axiom_report_parser_rejects_missing_or_unrecognized_output(
    output: str,
) -> None:
    with pytest.raises(ValueError):
        _parse_axiom_report(output, ("Demo.theorem",))


def test_axiom_report_parser_accepts_only_recognized_complete_results() -> None:
    parsed = _parse_axiom_report(
        "'Demo.first' depends on axioms: [propext,\n Quot.sound]\n"
        "'Demo.second' does not depend on any axioms\n",
        ("Demo.first", "Demo.second"),
    )
    assert parsed == {
        "Demo.first": frozenset({"propext", "Quot.sound"}),
        "Demo.second": frozenset(),
    }


def test_placeholder_and_axiom_checks_fail_closed(
    compiled_packet: CompiledPacket, tmp_path: Path
) -> None:
    scan = subprocess.run(
        [
            shutil.which("python3") or "python3",
            str(SCANNER),
            str(CORE),
            str(REFINEMENT),
            str(NONEMPTY),
            "--json",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    assert scan.returncode == 0, scan.stdout + scan.stderr
    payload = json.loads(scan.stdout)
    assert payload["blocked"] is False
    assert payload["match_count"] == 0
    assert payload["axiom_check"] is True
    assert set(payload["scanned_files"]) == {
        str(CORE.resolve()),
        str(REFINEMENT.resolve()),
        str(NONEMPTY.resolve()),
    }

    source = NONEMPTY.read_text(encoding="utf-8")
    declared = tuple(re.findall(r"^theorem\s+([A-Za-z0-9_.]+)", source, re.MULTILINE))
    assert declared == THEOREMS
    probe = tmp_path / "GlobalEconomicNonemptyV2Axioms.lean"
    probe.write_text(
        "import Proofs.GlobalEconomicStateRefinementV2Nonempty\n\n"
        + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in THEOREMS)
        + "\n",
        encoding="utf-8",
    )
    result = _run_probe(compiled_packet, probe)
    assert result.returncode == 0, result.stdout + result.stderr
    qualified = tuple(f"{NAMESPACE}.{name}" for name in THEOREMS)
    report = _parse_axiom_report(result.stdout, qualified)
    dependencies = frozenset().union(*report.values())
    assert dependencies <= ALLOWED_STANDARD_AXIOMS


def test_compiler_binds_nonempty_transfer_semantics(
    compiled_packet: CompiledPacket, tmp_path: Path
) -> None:
    probe = tmp_path / "GlobalEconomicNonemptyV2Semantics.lean"
    probe.write_text(
        """import Proofs.GlobalEconomicStateRefinementV2Nonempty

namespace Proofs.GlobalEconomicNonemptyV2Semantics
open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open GlobalEconomicStateRefinementV2Nonempty

example : transferEffects.rows.length = 2 := by decide
example : transferEffects.rows != [] := by decide
example : transferEffects.occurrenceConsumptions = ["occurrence-transfer-1"] := rfl
example : transferEffects.externalOutboxEnqueue = [] := rfl
example : transferPreState.height = 0 := rfl
example : transferPostState.height = 1 := rfl
example : transferPreState ≠ transferPostState := by
  intro same
  have heights := congrArg GlobalState.height same
  change 0 = 1 at heights
  omega
example : amountAt transferPreState.balances "alice" "ZUSD" "accounts" = 10 := by decide
example : amountAt transferPostState.balances "alice" "ZUSD" "accounts" = 7 := by decide
example : amountAt transferPostState.balances "bob" "ZUSD" "accounts" = 3 := by decide
example : transferReplayPost "replay-transfer-1" = some "occurrence-transfer-1" := by decide
example : LaneWrittenBy transferEffects .assetTransfer := by
  exact ⟨⟨.assetTransfer, "lane-root-pre", "lane-root-post"⟩, by simp [transferEffects], rfl⟩
example : Verified transferPreState transferEffects transferTerminalPlan
    transferOraclePlan [transferOccurrence] transferPostState :=
  transfer_global_state_verified
example : ∃ accepted : Accepted transferPreState,
    accepted.post = transferPostState ∧
    accepted.occurrences = [transferOccurrence] ∧
    accepted.effects.laneWrites =
      [⟨.assetTransfer, "lane-root-pre", "lane-root-post"⟩] ∧
    accepted.effects.externalOutboxEnqueue = [] :=
  combined_verified_relation_has_nonempty_asset_transfer

end Proofs.GlobalEconomicNonemptyV2Semantics
""",
        encoding="utf-8",
    )
    result = _run_probe(compiled_packet, probe)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""
