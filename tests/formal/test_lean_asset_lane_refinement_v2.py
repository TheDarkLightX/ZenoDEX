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

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
ASSET_PROOF = LEAN_DIR / "Proofs" / "AssetTransferRefinementV2.lean"
MANAGED_PROOF = LEAN_DIR / "Proofs" / "ManagedAssetLifecycleRefinementV2.lean"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"

ASSET_NAMESPACE = "Proofs.AssetTransferRefinementV2"
MANAGED_NAMESPACE = "Proofs.ManagedAssetLifecycleRefinementV2"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"

PINNED_MODELED_SOURCES = {
    "src/core/asset_transfer_types_v2.py":
        "ec067739d9da4a409347e8525c16188ecfcaad1e6b75172bfe1ca93e17cec40c",
    "src/core/asset_transfer_module_v2.py":
        "df0a25077d508db805afa0b828edbe5c8becdd362401f778fef0ce1f8649d065",
    "src/core/managed_asset_lifecycle_state_v2.py":
        "c89fcf0130f2fec66aa3485beeb7e74cf7a327294b4c1e7116119522a4666590",
    "src/core/managed_asset_lifecycle_result_v2.py":
        "d5f19e377fe721d3bcd7fd99732128c80e2839bffa5315c76fa07dca9e74e35a",
    "src/core/managed_asset_lifecycle_module_v2.py":
        "a7278af80244a51302670138e9f50876ba72db1246bd8b6f1af90ac65b595a48",
    "src/core/asset_lane_state_v2.py":
        "650dc5ab0a2a6010b9b512bfc59bcb7a33e7d376bbffffdb106bda5abb65f5a2",
    "src/core/asset_lane_coordinator_values_v2.py":
        "e138c22f4fb85d85ba969e7f45ddc51b304ea5b11fb9ef4b866c282a8956efde",
    "src/core/asset_lane_coordinator_v2.py":
        "be82d0ad5a7bc5ed49305a44711de9ca53a21f4ac7fc69fd1f232b33bc9462f8",
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
    assert _python_enum_values(transfer_types, "AssetTransferRejectCodeV2") == TRANSFER_REJECTS
    assert _python_enum_values(
        managed_results, "ManagedAssetLifecycleRejectCodeV2"
    ) == MANAGED_REJECTS
    assert _lean_wire_values(ASSET_PROOF.read_text(encoding="utf-8")) == TRANSFER_REJECTS
    assert _lean_wire_values(MANAGED_PROOF.read_text(encoding="utf-8")) == MANAGED_REJECTS


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
