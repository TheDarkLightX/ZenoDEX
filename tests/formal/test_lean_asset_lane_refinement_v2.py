"""Source-pinned formal gate for the bounded V2 asset-lane functional core.

The two Lean modules model the deciding transfer and managed issue/burn
arithmetic, reject precedence, occurrence consumption, empty external effects,
and coordinator projection/rebinding.  This gate compiles those modules with
the repository-pinned Lean 4.27 toolchain, checks their explicit theorem
surface with ``#print axioms``, and pins the Python sources whose shape the
model describes.

The evidence remains bounded.  It supplies no hash/codec equivalence, runtime
mount, release/profile authentication, settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

from src.core.asset_transfer_types_v2 import AssetTransferRejectCodeV2
from src.core.managed_asset_lifecycle_result_v2 import ManagedAssetLifecycleRejectCodeV2
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import lean as lean
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    outcome_lean as outcome_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import shared_lean as shared_lean
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    transfer_outcome_lean as transfer_outcome_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
ASSET_PROOF = LEAN_DIR / "Proofs" / "AssetTransferRefinementV2.lean"
MANAGED_PROOF = LEAN_DIR / "Proofs" / "ManagedAssetLifecycleRefinementV2.lean"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"

ASSET_NAMESPACE = "Proofs.AssetTransferRefinementV2"
MANAGED_NAMESPACE = "Proofs.ManagedAssetLifecycleRefinementV2"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"

# Source changes are exactly the reviewed resource repair at 0d57b7634.
# These pins detect drift; finite model checks below establish their scoped relation.
PINNED_MODELED_SOURCES = {
    "src/core/asset_transfer_types_v2.py":
        "958a55683e30d9af6030a621d62ba80d04070a51ee378b617151ae297e3ebc48",
    "src/core/asset_transfer_module_v2.py":
        "b18030eb4e5631e6315e5d483b4cca3f0f601af4747ac18c2e3b94d8b3f96cf3",
    "src/core/managed_asset_lifecycle_state_v2.py":
        "c89fcf0130f2fec66aa3485beeb7e74cf7a327294b4c1e7116119522a4666590",
    "src/core/managed_asset_lifecycle_result_v2.py":
        "40ea055822ff08d0729bf1aa94fbc71b253bd774ea7758aaa059d591c1e574b6",
    "src/core/managed_asset_lifecycle_module_v2.py":
        "16f68aec399ef620e9e665ccdcd67a3dbd5a5255fde554e420d31213b4abf1eb",
    "src/core/asset_lane_state_v2.py":
        "650dc5ab0a2a6010b9b512bfc59bcb7a33e7d376bbffffdb106bda5abb65f5a2",
    "src/core/asset_lane_coordinator_values_v2.py":
        "e8f885483f497a5cc675650128b44e0f5504bf3e07fb0f9a03ea526c23d4a844",
    "src/core/asset_lane_coordinator_v2.py":
        "61fde299a03aacc8a453134925602ea439c1bc58c194c5891cc9c9cefc7e795b",
    "src/core/global_settlement_resource_limits_v2.py":
        "7989ce33ec7bfb8e60cee7f5f8aba7f9cd1de16ee7444e121bd69ec2b98d8d5e",
    "src/core/global_settlement_primitives_v2.py":
        "11a26694357812e91b398bddc2b6bbec0a93063731ccd5b23818de1d0c0ca01e",
    "src/state/canonical.py":
        "3e1be2d2233b04d1e0e241e6f4c012ec458a2b1c66646597de410dd079b2e611",
}

TRANSFER_REJECTS = (
    "MISSING_OCCURRENCE",
    "OCCURRENCE_BINDING_MISMATCH",
    "RELEASE_MISMATCH",
    "UNKNOWN_COMMAND",
    "OCCURRENCE_COMMAND_MISMATCH",
    "UNKNOWN_ASSET",
    "DISABLED_ASSET",
    "UNREGISTERED_ASSET",
    "ASSET_ORIGIN_MISMATCH",
    "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED",
    "UNAUTHORIZED_SUBJECT",
    "SELF_TRANSFER",
    "ZERO_AMOUNT",
    "FEE_LIMIT_EXCEEDED",
    "EFFECT_DELTA_OVERFLOW",
    "INSUFFICIENT_BALANCE",
    "BALANCE_OVERFLOW",
)

MANAGED_REJECTS = (
    "MISSING_OCCURRENCE",
    "OCCURRENCE_BINDING_MISMATCH",
    "RELEASE_MISMATCH",
    "UNKNOWN_COMMAND",
    "OCCURRENCE_COMMAND_MISMATCH",
    "UNKNOWN_ASSET",
    "DISABLED_ASSET",
    "ASSET_CLASS_MISMATCH",
    "ASSET_DECIMALS_MISMATCH",
    "UNREGISTERED_ASSET",
    "ASSET_ORIGIN_MISMATCH",
    "GENERIC_AUTHORITY_FORBIDDEN",
    "ISSUE_DISABLED",
    "BURN_DISABLED",
    "UNAUTHORIZED_SUBJECT",
    "AUTHORIZATION_ROOT_MISMATCH",
    "ZERO_AMOUNT",
    "EFFECT_DELTA_OVERFLOW",
    "INSUFFICIENT_BALANCE",
    "BALANCE_OVERFLOW",
    "SUPPLY_OVERFLOW",
)

# The old source-pinned proof and its 17/21 tuples remain deliberate economic
# prefixes.  The qualified finite models append the resource outcome and must
# agree with the live runtime enum at every rank.
TRANSFER_RUNTIME_REJECTS = TRANSFER_REJECTS + ("STATE_RESOURCE_LIMIT",)
MANAGED_RUNTIME_REJECTS = MANAGED_REJECTS + ("STATE_RESOURCE_LIMIT",)

# Every declaration in each file is enumerated. This list is also the exact
# surface checked by Lean's transitive ``#print axioms`` command.
ASSET_THEOREMS = (
    "u128Max_eq_pow",
    "i128Max_eq_pow",
    "i128Min_eq_pow",
    "production_authority_is_none",
    "all_asset_classes_complete",
    "all_reject_codes_length",
    "all_reject_codes_wire_order",
    "all_reject_codes_complete",
    "all_reject_codes_no_duplicates",
    "RejectCode.rank_injective",
    "mem_insert_principal",
    "mem_sort_principals",
    "firstFailing_eq_none_iff",
    "pre_balance_codes_rank_sorted",
    "pre_balance_codes_complete",
    "firstFailing_some_spec",
    "firstFailing_some_of",
    "pre_balance_reject_exact_precedence",
    "reject_code_none_parts",
    "balance_code_none_iff",
    "transition_total",
    "accepted_iff_no_reject",
    "rejected_post_eq_pre",
    "rejected_effects_empty",
    "accepted_post_and_effects",
    "accepted_pre_balance_guard",
    "accepted_consumes_exact_occurrence",
    "accepted_zero_external_roots",
    "accepted_conservation_row_exact",
    "accepted_supply_unchanged",
    "accepted_balance_eq",
    "delta_untouched",
    "fee_owner_sender_alias_is_locally_conserving",
    "sender_mem_ordered_roles",
    "recipient_mem_ordered_roles",
    "fee_owner_mem_ordered_roles",
    "accepted_deltas_i128",
    "accepted_balances_u128",
    "sumOver_add",
    "sumOver_indicator",
    "sumOver_delta",
    "accepted_conserves_enumerated_total",
    "replace_transfer_projects_leaf",
    "coordinator_rebind_preserves_payload_and_occurrence",
    "coordinator_rebind_exact_lane_write",
    "coordinator_transfer_projection_and_rebind",
    "sorted_failure_role_order",
    "sorted_balance_scan_can_report_overflow_before_sender_underflow",
    "missing_occurrence_precedes_other_failures",
    "omitted_origin_rejects_before_origin_equality_can_authorize",
    "native_asset_accounting_is_explicitly_unimplemented",
    "omitted_fee_credit_breaks_conservation_counterexample",
)

MANAGED_THEOREMS = (
    "production_authority_is_none",
    "all_reject_codes_length",
    "all_reject_codes_wire_order",
    "all_reject_codes_complete",
    "all_reject_codes_no_duplicates",
    "RejectCode.rank_injective",
    "firstFailing_eq_none_iff",
    "authorization_codes_rank_sorted",
    "authorization_codes_complete",
    "firstFailing_some_spec",
    "firstFailing_some_of",
    "authorization_reject_exact_precedence",
    "reject_code_none_parts",
    "issue_supply_overflow_precedes_balance_overflow",
    "transition_total",
    "accepted_iff_no_reject",
    "rejected_post_eq_pre",
    "rejected_effects_empty",
    "accepted_post_and_effects",
    "accepted_authorization_guard",
    "accepted_consumes_exact_occurrence",
    "accepted_zero_external_roots",
    "accepted_conservation_equations",
    "accepted_effect_delta_i128",
    "accepted_post_supply_u128",
    "accepted_post_selected_balance_u128",
    "accepted_issue_authority_exact",
    "accepted_burn_authority_exact",
    "protocol_asset_cannot_be_accepted",
    "coordinator_managed_projection_preserves_transfer",
    "coordinator_managed_projection_and_rebind",
    "stateful_issue_transfer_burn_trace",
    "issue_supply_overflow_precedes_balance_overflow_counterexample",
    "protocol_issue_rejects_generic_authority_counterexample",
    "wrong_grant_rejects_and_transition_is_noop",
)

ALLOWED_STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})


@dataclass(frozen=True)
class CompiledPacket:
    root: Path
    lean: Path
    environment: dict[str, str]


def _run(
    command: list[str],
    *,
    environment: dict[str, str] | None = None,
    timeout: int = 300,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )


def _theorem_declarations(source: str) -> tuple[str, ...]:
    return tuple(
        re.findall(
            r"^theorem\s+"
            r"([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)(?=\s|:)",
            source,
            re.MULTILINE,
        )
    )


def _lean_wire_values(source: str) -> tuple[str, ...]:
    start = source.index("def RejectCode.code")
    end = source.index("def RejectCode.rank", start)
    return tuple(re.findall(r'=>\s*"([A-Z_]+)"', source[start:end]))


def _python_enum_values(source: str, class_name: str) -> tuple[str, ...]:
    found = re.search(
        rf"^class {re.escape(class_name)}\(str, Enum\):\n(?P<body>(?:    [A-Z_]+ = \"[A-Z_]+\"\n)+)",
        source,
        re.MULTILINE,
    )
    assert found is not None, class_name
    return tuple(re.findall(r'= "([A-Z_]+)"', found.group("body")))


def _axiom_dependencies(output: str) -> set[str]:
    dependencies: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL):
        dependencies.update(item.strip() for item in body.split(",") if item.strip())
    return dependencies


FINITE_GATE_PREAMBLE = """
import Proofs.ManagedAssetFiniteOutcomeV2
import Proofs.AssetTransferFiniteOutcomeV2
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open Proofs
"""


def _finite_gate_consumer(
    subject: LeanSubject, name: str, body: str
) -> subprocess.CompletedProcess[str]:
    path = subject.source / f"{name}.lean"
    path.write_text(FINITE_GATE_PREAMBLE + body, encoding="utf-8")
    return _compile(subject, path)


FINITE_GATE_CONSUMER = r"""
def managedCodeRows (rank : Nat) :
    List Proofs.ManagedAssetFiniteOutcomeV2.RejectCode → List String
  | [] => []
  | code :: rest =>
      ("MANAGED_CODE," ++ toString rank ++ "," ++
        Proofs.ManagedAssetFiniteOutcomeV2.RejectCode.code code) ::
        managedCodeRows (rank + 1) rest

def transferCodeRows (rank : Nat) :
    List Proofs.AssetTransferFiniteOutcomeV2.RejectCode → List String
  | [] => []
  | code :: rest =>
      ("TRANSFER_CODE," ++ toString rank ++ "," ++
        Proofs.AssetTransferFiniteOutcomeV2.RejectCode.code code) ::
        transferCodeRows (rank + 1) rest

namespace ManagedCase
open Proofs.ManagedAssetFiniteOutcomeV2

def policy : M.Policy :=
  ⟨"USD", .registeredOrdinaryToken, some "origin", 8,
    some ⟨"issuer", "grant"⟩, some "burn", true⟩
def pre : State :=
  ⟨"release", [policy], [⟨"alice", "USD", "accounts", 9⟩], [⟨"USD", 9⟩]⟩
def command : M.Command :=
  ⟨"managed_asset_issue", "issue-body", "USD", .registeredOrdinaryToken,
    some "origin", 8, some "grant", "alice", 1⟩
def context : M.Context :=
  ⟨"release", "global", some ⟨"global", [], "managed_asset_issue", "issue-body",
    "issuer", "grant", "managed-occurrence"⟩⟩
def missingContext : M.Context := {context with occurrence := none}
def digest (_ : B.Bytes) : M.Root := "finite-digest"

def verdictName : Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => code.code

def emit (name : String) (result : Result) : IO Unit := do
  IO.println (String.intercalate "," [
    "MANAGED_RESULT", name, verdictName result.verdict,
    toString (result.post == pre),
    toString (result.effects == AssetTransferRefinementV2.EffectEnvelope.empty)])

end ManagedCase

namespace TransferCase
open Proofs.AssetTransferFiniteOutcomeV2

def policy : T.Policy :=
  ⟨"USD", "collector", 0, true, .registeredOrdinaryToken, some "origin", 8⟩
def pre : State :=
  ⟨"release", [policy], [⟨"sender", "USD", "accounts", 5⟩], [⟨"USD", 10⟩]⟩
def command : T.Command :=
  ⟨"asset_transfer", "transfer-body", "USD", "sender", "recipient", 5, 0, some "origin"⟩
def context : T.Context :=
  ⟨"release", "global", some ⟨"global", [], "asset_transfer", "transfer-body",
    "sender", "grant", "transfer-occurrence"⟩⟩
def missingContext : T.Context := {context with occurrence := none}
def digest (_ : B.Bytes) : T.Root := "finite-digest"

def verdictName : Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => code.code

def emit (name : String) (result : Result) : IO Unit := do
  IO.println (String.intercalate "," [
    "TRANSFER_RESULT", name, verdictName result.verdict,
    toString (result.post == pre),
    toString (result.effects == AssetTransferRefinementV2.EffectEnvelope.empty)])

end TransferCase

#eval IO.println (String.intercalate "\n"
  (managedCodeRows 0 Proofs.ManagedAssetFiniteOutcomeV2.allRejectCodes))
#eval IO.println (String.intercalate "\n"
  (transferCodeRows 0 Proofs.AssetTransferFiniteOutcomeV2.allRejectCodes))
#eval ManagedCase.emit "accepted"
  (Proofs.ManagedAssetFiniteOutcomeV2.transition ManagedCase.digest ManagedCase.context
    ManagedCase.pre ManagedCase.command)
#eval ManagedCase.emit "missing-occurrence"
  (Proofs.ManagedAssetFiniteOutcomeV2.transition ManagedCase.digest ManagedCase.missingContext
    ManagedCase.pre ManagedCase.command)
#eval TransferCase.emit "accepted"
  (Proofs.AssetTransferFiniteOutcomeV2.transition TransferCase.digest TransferCase.context
    TransferCase.pre TransferCase.command)
#eval TransferCase.emit "missing-occurrence"
  (Proofs.AssetTransferFiniteOutcomeV2.transition TransferCase.digest TransferCase.missingContext
    TransferCase.pre TransferCase.command)
"""


@pytest.fixture(scope="module")
def compiled_packet(tmp_path_factory: pytest.TempPathFactory) -> CompiledPacket:
    assert (LEAN_DIR / "lean-toolchain").read_text(encoding="utf-8").strip() == PINNED_TOOLCHAIN
    lean_executable = shutil.which("lean")
    assert lean_executable is not None, "formal gate requires the Lean executable"
    lean = Path(lean_executable)

    environment = os.environ.copy()
    environment["ELAN_TOOLCHAIN"] = PINNED_TOOLCHAIN
    environment.pop("LEAN_PATH", None)
    version = _run([str(lean), "--version"], environment=environment, timeout=30)
    assert version.returncode == 0, version.stdout + version.stderr
    assert "version 4.27.0" in version.stdout

    build_root = tmp_path_factory.mktemp("asset-lane-v2-lean")
    (build_root / "Proofs").mkdir()
    environment["LEAN_PATH"] = str(build_root)
    for target in (ASSET_PROOF, MANAGED_PROOF):
        output = build_root / "Proofs" / f"{target.stem}.olean"
        result = _run(
            [
                str(lean),
                "-DwarningAsError=true",
                "-R",
                str(LEAN_DIR),
                "-o",
                str(output),
                str(target),
            ],
            environment=environment,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout.strip() == ""
        assert result.stderr.strip() == ""
        assert output.is_file()
    return CompiledPacket(build_root, lean, environment)


def test_modules_compile_with_pinned_lean_and_warnings_as_errors(
    compiled_packet: CompiledPacket,
) -> None:
    assert (compiled_packet.root / "Proofs" / "AssetTransferRefinementV2.olean").is_file()
    assert (
        compiled_packet.root / "Proofs" / "ManagedAssetLifecycleRefinementV2.olean"
    ).is_file()


def test_modeled_python_sources_are_exactly_pinned() -> None:
    for relative_path, expected_sha256 in PINNED_MODELED_SOURCES.items():
        path = ROOT / relative_path
        assert path.is_file(), relative_path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected_sha256, relative_path


def test_every_theorem_declaration_is_explicitly_tracked() -> None:
    asset_source = ASSET_PROOF.read_text(encoding="utf-8")
    managed_source = MANAGED_PROOF.read_text(encoding="utf-8")
    assert _theorem_declarations(asset_source) == ASSET_THEOREMS
    assert _theorem_declarations(managed_source) == MANAGED_THEOREMS
    assert len(set(ASSET_THEOREMS)) == len(ASSET_THEOREMS)
    assert len(set(MANAGED_THEOREMS)) == len(MANAGED_THEOREMS)
    assert f"import {ASSET_NAMESPACE}" in managed_source


def test_repository_scanner_checks_both_proofs_with_axioms_enabled() -> None:
    assert SCANNER.is_file()
    result = _run(
        [sys.executable, str(SCANNER), str(ASSET_PROOF), str(MANAGED_PROOF), "--json"],
        timeout=120,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    assert payload["blocked"] is False
    assert payload["match_count"] == 0
    assert payload["axiom_check"] is True
    assert len(payload["scanned_files"]) == 2


def test_repository_scanner_ignores_prose_and_rejects_real_axiom(
    tmp_path: Path,
) -> None:
    probe = tmp_path / "ScannerConvention.lean"
    probe.write_text("/- axiom in prose is inert -/\naxiom localTrust : Prop\n", encoding="utf-8")
    result = _run([sys.executable, str(SCANNER), str(probe), "--json"], timeout=120)
    assert result.returncode == 1, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    assert payload["blocked"] is True
    assert payload["match_count"] == 1
    assert payload["matches"][0]["rule"] == "lean_axiom_declaration"
    assert payload["matches"][0]["line"] == 2


def test_every_tracked_theorem_uses_only_standard_axioms(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
) -> None:
    qualified = (
        *(f"{ASSET_NAMESPACE}.{name}" for name in ASSET_THEOREMS),
        *(f"{MANAGED_NAMESPACE}.{name}" for name in MANAGED_THEOREMS),
    )
    probe = tmp_path / "AssetLaneV2AxiomDependencies.lean"
    probe.write_text(
        f"import {MANAGED_NAMESPACE}\n\n"
        + "\n".join(f"#print axioms {name}" for name in qualified)
        + "\n",
        encoding="utf-8",
    )
    result = _run(
        [str(compiled_packet.lean), "-DwarningAsError=true", str(probe)],
        environment=compiled_packet.environment,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    for name in qualified:
        assert f"'{name}'" in result.stdout, name
    assert _axiom_dependencies(result.stdout) <= ALLOWED_STANDARD_AXIOMS


def test_axiom_output_parser_exposes_a_project_defined_dependency() -> None:
    sample = "'Demo.bad' depends on axioms: [propext, Demo.localTrust]"
    assert _axiom_dependencies(sample) - ALLOWED_STANDARD_AXIOMS == {"Demo.localTrust"}


def test_reject_wire_orders_match_the_source_pinned_python_enums() -> None:
    transfer_types = (ROOT / "src/core/asset_transfer_types_v2.py").read_text(
        encoding="utf-8"
    )
    managed_results = (ROOT / "src/core/managed_asset_lifecycle_result_v2.py").read_text(
        encoding="utf-8"
    )
    transfer_runtime = _python_enum_values(transfer_types, "AssetTransferRejectCodeV2")
    managed_runtime = _python_enum_values(managed_results, "ManagedAssetLifecycleRejectCodeV2")
    assert transfer_runtime[: len(TRANSFER_REJECTS)] == TRANSFER_REJECTS
    assert managed_runtime[: len(MANAGED_REJECTS)] == MANAGED_REJECTS
    assert transfer_runtime == TRANSFER_RUNTIME_REJECTS
    assert managed_runtime == MANAGED_RUNTIME_REJECTS
    assert _lean_wire_values(ASSET_PROOF.read_text(encoding="utf-8")) == TRANSFER_REJECTS
    assert _lean_wire_values(MANAGED_PROOF.read_text(encoding="utf-8")) == MANAGED_REJECTS


def test_finite_compiled_registry_and_transition_report_match_runtime_enums(
    transfer_outcome_lean: LeanSubject,
) -> None:
    """The qualified finite models own the appended resource-code rows."""
    result = _finite_gate_consumer(
        transfer_outcome_lean,
        "AssetLaneFiniteRegistryAndTransitionReport",
        FINITE_GATE_CONSUMER,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""

    managed_rows: list[tuple[int, str]] = []
    transfer_rows: list[tuple[int, str]] = []
    outcomes: dict[tuple[str, str], tuple[str, bool, bool]] = {}
    for line in result.stdout.splitlines():
        if line.startswith(("MANAGED_CODE,", "TRANSFER_CODE,")):
            fields = line.split(",", 2)
            assert len(fields) == 3
            row = (int(fields[1]), fields[2])
            if fields[0] == "MANAGED_CODE":
                managed_rows.append(row)
            else:
                transfer_rows.append(row)
        elif line.startswith(("MANAGED_RESULT,", "TRANSFER_RESULT,")):
            fields = line.split(",")
            assert len(fields) == 5
            outcomes[(fields[0], fields[1])] = (
                fields[2],
                fields[3] == "true",
                fields[4] == "true",
            )
        elif line.strip():
            raise AssertionError(f"unexpected finite gate output: {line}")

    assert managed_rows == list(enumerate(MANAGED_RUNTIME_REJECTS))
    assert transfer_rows == list(enumerate(TRANSFER_RUNTIME_REJECTS))
    assert [rank for rank, _ in managed_rows] == list(range(22))
    assert [rank for rank, _ in transfer_rows] == list(range(18))
    assert tuple(code.value for code in ManagedAssetLifecycleRejectCodeV2) == (
        MANAGED_RUNTIME_REJECTS
    )
    assert tuple(code.value for code in AssetTransferRejectCodeV2) == TRANSFER_RUNTIME_REJECTS

    assert outcomes == {
        ("MANAGED_RESULT", "accepted"): ("ACCEPTED", False, False),
        ("MANAGED_RESULT", "missing-occurrence"): (
            "MISSING_OCCURRENCE",
            True,
            True,
        ),
        ("TRANSFER_RESULT", "accepted"): ("ACCEPTED", False, False),
        ("TRANSFER_RESULT", "missing-occurrence"): (
            "MISSING_OCCURRENCE",
            True,
            True,
        ),
    }


def test_transfer_source_shape_pins_fixed_prefix_and_sorted_balance_scan() -> None:
    source = (ROOT / "src/core/asset_transfer_module_v2.py").read_text(encoding="utf-8")
    policy = source.split("def _transfer_policy", 1)[1].split("def _transfer_deltas", 1)[0]
    policy_rejects = tuple(re.findall(r"return AssetTransferRejectCodeV2\.([A-Z_]+)", policy))
    assert policy_rejects == TRANSFER_REJECTS[:14]

    deltas = source.split("def _transfer_deltas", 1)[1].split("@dataclass", 1)[0]
    assert "deltas[policy.fee_owner] = deltas.get(policy.fee_owner, 0)" in deltas
    assert "return tuple(sorted(deltas.items()))" in deltas
    assert deltas.index("EFFECT_DELTA_OVERFLOW") > deltas.index("deltas[policy.fee_owner]")

    balances = source.split("def _post_balances", 1)[1].split("def _effect_rows", 1)[0]
    assert balances.index("if post_atoms < 0:") < balances.index("if post_atoms > MAX_ATOMS_V2:")
    assert "for owner, delta_atoms in deltas:" in balances
    asset_proof = ASSET_PROOF.read_text(encoding="utf-8")
    assert "sorted_balance_scan_can_report_overflow_before_sender_underflow" in asset_proof
    assert "omitted_fee_credit_breaks_conservation_counterexample" in asset_proof


def test_managed_source_shape_pins_authority_and_supply_first_precedence() -> None:
    source = (ROOT / "src/core/managed_asset_lifecycle_module_v2.py").read_text(
        encoding="utf-8"
    )
    authorize = source.split("def _authorize", 1)[1].split("def _post_supply", 1)[0]
    assert "policy.asset_class is not AssetClassV2.REGISTERED_ORDINARY_TOKEN" in authorize
    assert "occurrence.subject_id != policy.issue_authority_subject" in authorize
    assert "occurrence.subject_id != command.account_owner" in authorize
    assert "occurrence.grant_root != expected_authorization_root" in authorize
    assert "command.authorization_root != expected_authorization_root" in authorize

    transition = source.split("def transition_managed_asset_lifecycle_v2", 1)[1]
    supply_call = transition.index("supplies = _post_supply(prepared)")
    balance_call = transition.index("balances = _post_balances(prepared)")
    accept_call = transition.index("return _accept(prepared, balances, supplies)")
    assert supply_call < balance_call < accept_call
    managed_proof = MANAGED_PROOF.read_text(encoding="utf-8")
    assert "issue_supply_overflow_precedes_balance_overflow_counterexample" in managed_proof
    assert "protocol_asset_cannot_be_accepted" in managed_proof
    assert "stateful_issue_transfer_burn_trace" in managed_proof


def test_coordinator_source_shape_pins_binding_projection_and_rebind() -> None:
    source = (ROOT / "src/core/asset_lane_coordinator_v2.py").read_text(encoding="utf-8")
    transition = source.split("def transition_asset_lane_v2", 1)[1].split("__all__", 1)[0]
    registry = transition.index("_policy_origin_bindings_hold_v2")
    candidate = transition.index("_candidate_binding_holds_v2")
    projection = transition.index("_projection_holds_v2")
    rebind = transition.index("return _rebind_candidate_v2")
    assert registry < candidate < projection < rebind

    rebound = source.split("def _rebind_candidate_v2", 1)[1].split(
        "def transition_asset_lane_v2", 1
    )[0]
    assert "effects.rows" in rebound
    assert "effects.asset_conservation" in rebound
    assert "effects.fee_conservation" in rebound
    assert "effects.occurrence_consumptions" in rebound
    assert "LaneWriteV2(LaneIdV2.ASSET_TRANSFER" in rebound
    assert "effects.occurrence_consumptions,\n        ()," in rebound


def test_resource_rejections_follow_leaf_candidate_construction_before_effects() -> None:
    transfer_source = (ROOT / "src/core/asset_transfer_module_v2.py").read_text(
        encoding="utf-8"
    )
    transfer_accept = transfer_source.split("def _accept_transfer", 1)[1].split(
        "def transition_asset_transfer_v2", 1
    )[0]
    transfer_candidate = transfer_accept.index("post_state = AssetTransferStateV2(")
    transfer_resource = transfer_accept.index("StateResourceLimitExceededV2")
    transfer_resource_code = transfer_accept.index("AssetTransferRejectCodeV2.STATE_RESOURCE_LIMIT")
    transfer_effects = transfer_accept.index("effects = _effect_plan(")
    assert transfer_candidate < transfer_resource < transfer_resource_code < transfer_effects

    managed_source = (ROOT / "src/core/managed_asset_lifecycle_module_v2.py").read_text(
        encoding="utf-8"
    )
    managed_accept = managed_source.split("def _accept", 1)[1].split(
        "def transition_managed_asset_lifecycle_v2", 1
    )[0]
    managed_candidate = managed_accept.index("post_state = ManagedAssetLifecycleStateV2(")
    managed_resource = managed_accept.index("StateResourceLimitExceededV2")
    managed_resource_code = managed_accept.index(
        "ManagedAssetLifecycleRejectCodeV2.STATE_RESOURCE_LIMIT"
    )
    managed_effects = managed_accept.index("effects = _effect_plan(")
    assert managed_candidate < managed_resource < managed_resource_code < managed_effects


def test_coordinator_routes_aggregate_resource_rejection_before_projection() -> None:
    source = (ROOT / "src/core/asset_lane_coordinator_v2.py").read_text(encoding="utf-8")
    transition = source.split("def transition_asset_lane_v2", 1)[1].split("__all__", 1)[0]
    candidate_binding = transition.index("if not _candidate_binding_holds_v2")
    aggregate = transition.index("post_state = _aggregate_post_state_v2")
    resource_exception = transition.index("StateResourceLimitExceededV2")
    resource_code = transition.index(
        "AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT"
    )
    projection = transition.index("if not _projection_holds_v2")
    rebind = transition.index("return _rebind_candidate_v2")
    assert candidate_binding < aggregate < resource_exception < resource_code < projection < rebind
    resource_block = transition[resource_exception:projection]
    assert "AssetLaneRouteV2.COORDINATOR" in resource_block


def test_claim_ceiling_and_sender_fee_owner_composition_limit_are_explicit() -> None:
    source = " ".join(
        (ASSET_PROOF.read_text(encoding="utf-8") + MANAGED_PROOF.read_text(encoding="utf-8"))
        .split()
    )
    for phrase in (
        "no hash or codec equivalence",
        "runtime mounting",
        "release/profile authentication",
        "settlement",
        "production authority",
        "no global-refinement acceptance",
        "same-key positive state-bearing credit",
        "does not obtain global acceptance",
    ):
        assert phrase in source, phrase
