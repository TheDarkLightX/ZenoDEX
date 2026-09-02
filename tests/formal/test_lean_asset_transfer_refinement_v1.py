"""Formal claim gate for the Lean ``ASSET_TRANSFER`` refinement slice.

Subject: ``lean-mathlib/Proofs/AssetTransferRefinementV1.lean`` and its
challenge module. The Lean files formalize the rejection precedence and the
accepted arithmetic of one single-asset transfer under the three fee-owner
roles (distinct owner, owner equals sender, owner equals recipient) with
bounded-integer predicates for ``u128`` amounts and ``i128`` effect deltas.

Evidence families:

- ``formal``: deterministic ``lake`` compilation with warnings as errors, the
  repository placeholder scanner, and ``#print axioms`` over the explicit
  hand-maintained claim list below.
- ``replay`` / ``boundary``: an executable Lean report, produced by evaluating
  the modeled transition on a fixed vector table, compared field by field with
  the live Python ``transition_asset_transfer_v1`` on the same vectors.
- ``mutation``: a deliberately weakened Lean variant that drops the fee-owner
  credit must be observably non-conservative, and structural checks pin the
  guard order, the width literals, and the runtime facts that the Lean prose
  cites (final role aggregation and fixed failure-class precedence).

This is research-only formal evidence. It creates no settlement, release,
production, migration, or value-moving authority, and it is not a refinement
proof between the Lean model and the Python or Rust runtime.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
    transition_asset_transfer_v1,
)
from src.core.global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
PROOF = LEAN_DIR / "Proofs" / "AssetTransferRefinementV1.lean"
CHALLENGE = LEAN_DIR / "Proofs" / "AssetTransferRefinementV1Challenge.lean"
PROOFS_ROOT = LEAN_DIR / "Proofs.lean"
CORE_MODULE = "Proofs.AssetTransferRefinementV1"
CHALLENGE_MODULE = "Proofs.AssetTransferRefinementV1Challenge"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"
PYTHON_TRANSITION = ROOT / "src" / "core" / "asset_transfer_module_v1.py"
RUST_TRANSITION = ROOT / "zk" / "global_settlement_abi_v1" / "src" / "asset_transfer.rs"

ASSET = "USD"
PRINCIPALS = ("alice", "bob", "treasury")
U127 = 1 << 127

# Hand-maintained claim surface. Every name is a `theorem` in the named module
# and is passed to `#print axioms`; nothing else is claimed to be checked.
CORE_CLAIMS = (
    "u128Max_eq_pow",
    "i128Min_eq_pow",
    "i128Max_eq_pow",
    "allRejectCodes_codes",
    "allRejectCodes_complete",
    "allRejectCodes_no_duplicates",
    "RejectCode.rank_injective",
    "rejectCode_eq_some_iff",
    "rejectCode_eq_none_iff",
    "transition_total",
    "rejected_post_eq_pre",
    "rejected_effects_empty",
    "accepted_iff_all_guards",
    "accepted_supply_unchanged",
    "accepted_balance_eq",
    "accepted_untouched_unchanged",
    "accepted_conserves_total",
    "accepted_supply_cover_preserved",
    "accepted_balances_u128",
    "accepted_deltas_i128",
    "accepted_movement_rows_i128",
    "delta_distinct_roles",
    "delta_fee_owner_is_sender",
    "delta_fee_owner_is_recipient",
    "delta_untouched",
    "roleOrdered_eq_intended",
    "balanceOverflow_unreachable",
    "rejectCode_ne_postStateResourceBoundExceeded",
    "demo_accepted_values",
    "aliasSender_values",
    "aliasRecipient_values",
    "rejection_vectors",
    "oneAtom_accepted",
    "exactBalance_accepted",
    "insufficientNeighbor_rejected",
    "maximumNeighbor_accepted",
    "overflowNeighbor_rejected",
    "zeroFee_accepted_without_fee_row",
    "feeLimit_boundary",
    "widthMinDelta_accepted",
    "widthAliasSender_accepted",
    "widthFeeAlone_rejected",
    "effectDeltaOverflow_rejected",
)

CHALLENGE_CLAIMS = (
    "challenge_exact_precedence",
    "challenge_totality",
    "challenge_rejection_is_noop",
    "challenge_accepted_conservation",
    "challenge_accepted_bounds",
    "challenge_alias_formulas",
    "challenge_overflow_unreachable",
    "challenge_role_order_bridge",
    "leaky_breaks_conservation_on_demo",
    "leaky_is_not_conservative",
    "honest_conserves_on_demo",
    "report_vectors_cover_every_emittable_code",
    "roleOrdered_agrees_on_every_vector",
)

ALLOWED_STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "constant", "unsafe", "native_decide")

# Phrases the core proof must contain so the scope is stated, not implied.
REQUIRED_SCOPE_PHRASES = (
    "one asset",
    "canonical byte",
    "state roots",
    "journal",
    "route",
    "replay",
    "signature",
    "authentication derivation",
    "multi-asset lookup",
    "zero-balance elision",
    "No refinement between this model and the Python or Rust runtime is claimed",
    "MAX_ATOMS_V1",
    "MIN_DELTA_ATOMS_V1",
    "MAX_DELTA_ATOMS_V1",
    "negative-delta preflight",
    "accounting-location",
    "no statement here asserts custody, possession, title, control, or any "
    "enforceable claim over any asset",
)

FORBIDDEN_SCOPE_PHRASES = ("internal custody", "legal title", "possesses the assets")

REPORT_PROBE = f"""import {CHALLENGE_MODULE}

#eval IO.println {CHALLENGE_MODULE}.challengeReportV1
"""

# --------------------------------------------------------------------------
# Vector table, mirrored field for field by the Lean challenge module
# --------------------------------------------------------------------------

BASE_VECTOR: dict[str, object] = {
    "fee_owner": "treasury",
    "fee": 2,
    "enabled": True,
    "balances": {"alice": 100, "bob": 10, "treasury": 5},
    "supply": 115,
    "release_matches": True,
    "subject": "alice",
    "kind": ASSET_TRANSFER_COMMAND_KIND_V1,
    "asset": ASSET,
    "sender": "alice",
    "recipient": "bob",
    "amount": 30,
    "max_fee": 2,
}

VECTORS: dict[str, dict[str, object]] = {
    "accept_distinct": {},
    "alias_sender": {"fee_owner": "alice"},
    "alias_recipient": {"fee_owner": "bob"},
    "release_mismatch": {"release_matches": False},
    "unknown_command": {"kind": "unknown"},
    "unknown_asset": {"asset": "EUR"},
    "disabled_asset": {"enabled": False},
    "unauthorized_subject": {"subject": "mallory"},
    "self_transfer": {"recipient": "alice"},
    "zero_amount": {"amount": 0},
    "fee_limit_exceeded": {"max_fee": 1},
    "insufficient_balance": {"amount": 99},
    "insufficient_neighbor": {"balances": {"alice": 31, "bob": 10, "treasury": 5}, "supply": 46},
    "exact_balance": {"balances": {"alice": 32, "bob": 10, "treasury": 5}, "supply": 47},
    "one_atom": {
        "balances": {"alice": 1, "bob": 10, "treasury": 5},
        "supply": 16,
        "amount": 1,
        "fee": 0,
        "max_fee": 0,
    },
    "zero_fee": {"fee": 0, "max_fee": 0},
    "maximum_neighbor": {
        "balances": {"alice": 30, "bob": MAX_ATOMS_V1 - 30},
        "supply": MAX_ATOMS_V1,
        "fee": 0,
        "max_fee": 0,
    },
    "overflow_neighbor": {
        "balances": {"alice": 30, "bob": MAX_ATOMS_V1 - 29},
        "supply": MAX_ATOMS_V1,
        "fee": 0,
        "max_fee": 0,
    },
    "effect_delta_overflow": {
        "balances": {"alice": U127},
        "supply": U127,
        "amount": U127,
        "fee": 0,
        "max_fee": 0,
    },
    "width_min_delta": {
        "balances": {"alice": U127},
        "supply": U127,
        "amount": U127 - 1,
        "fee": 1,
        "max_fee": 1,
    },
    "width_alias_sender_aggregate": {
        "fee_owner": "alice",
        "balances": {"alice": U127 - 1},
        "supply": U127 - 1,
        "amount": U127 - 1,
        "fee": U127 - 1,
        "max_fee": U127 - 1,
    },
    "width_fee_alone": {
        "fee_owner": "alice",
        "balances": {"alice": 1},
        "supply": 1,
        "amount": 1,
        "fee": U127,
        "max_fee": U127,
    },
}

# The vector whose pre-state violates the Python supply cover; Python refuses
# to construct it, while the total Lean transition still decides it.
OUTSIDE_PYTHON_INVARIANT = "overflow_neighbor"

EXPECTED_VERDICTS: dict[str, str] = {
    "accept_distinct": "ACCEPTED",
    "alias_sender": "ACCEPTED",
    "alias_recipient": "ACCEPTED",
    "release_mismatch": "RELEASE_MISMATCH",
    "unknown_command": "UNKNOWN_COMMAND",
    "unknown_asset": "UNKNOWN_ASSET",
    "disabled_asset": "DISABLED_ASSET",
    "unauthorized_subject": "UNAUTHORIZED_SUBJECT",
    "self_transfer": "SELF_TRANSFER",
    "zero_amount": "ZERO_AMOUNT",
    "fee_limit_exceeded": "FEE_LIMIT_EXCEEDED",
    "insufficient_balance": "INSUFFICIENT_BALANCE",
    "insufficient_neighbor": "INSUFFICIENT_BALANCE",
    "exact_balance": "ACCEPTED",
    "one_atom": "ACCEPTED",
    "zero_fee": "ACCEPTED",
    "maximum_neighbor": "ACCEPTED",
    "overflow_neighbor": "BALANCE_OVERFLOW",
    "effect_delta_overflow": "EFFECT_DELTA_OVERFLOW",
    "width_min_delta": "ACCEPTED",
    "width_alias_sender_aggregate": "ACCEPTED",
    "width_fee_alone": "EFFECT_DELTA_OVERFLOW",
}

# Hand-computed post balances for the accepted vectors (alice, bob, treasury).
EXPECTED_POST: dict[str, tuple[int, int, int]] = {
    "accept_distinct": (68, 40, 7),
    "alias_sender": (70, 40, 5),
    "alias_recipient": (68, 42, 5),
    "exact_balance": (0, 40, 7),
    "one_atom": (0, 11, 5),
    "zero_fee": (70, 40, 5),
    "maximum_neighbor": (0, MAX_ATOMS_V1, 0),
    "width_min_delta": (0, U127 - 1, 1),
    "width_alias_sender_aggregate": (0, U127 - 1, 0),
}

# Aggregated fee-owner movement rows, as in the runtime alias test.
EXPECTED_ALIAS_MOVEMENTS: dict[str, set[tuple[str, int]]] = {
    "accept_distinct": {("alice", -32), ("bob", 30), ("treasury", 2)},
    "alias_sender": {("alice", -30), ("bob", 30)},
    "alias_recipient": {("alice", -32), ("bob", 32)},
}


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "formal claim gate requires the lake executable"
    return lake


def _lean(*args: str, timeout: int = 900) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [_require_lake(), *args],
        cwd=LEAN_DIR,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _spec(name: str) -> dict[str, object]:
    return {**BASE_VECTOR, **VECTORS[name]}


def _python_inputs(
    name: str,
) -> tuple[AssetTransferContextV1, AssetTransferStateV1, AssetTransferCommandV1]:
    spec = _spec(name)
    balances: dict[str, int] = spec["balances"]  # type: ignore[assignment]
    context = AssetTransferContextV1(
        chain_id="zeno-asset-formal",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        module_release_id=_root(3) if spec["release_matches"] else _root(99),
        command_occurrence_id=_root(4),
        subject_id=str(spec["subject"]),
        grant_root=_root(5),
    )
    rows = tuple(
        EconomicAmountV1(owner, ASSET, ACCOUNT_CUSTODY_DOMAIN_V1, atoms)
        for owner, atoms in sorted(balances.items())
        if atoms
    )
    state = AssetTransferStateV1(
        module_release_id=_root(3),
        policies=(
            AssetTransferPolicyV1(
                ASSET, str(spec["fee_owner"]), int(spec["fee"]), bool(spec["enabled"])  # type: ignore[arg-type]
            ),
        ),
        balances=rows,
        supplies=(AssetSupplyV1(ASSET, int(spec["supply"])),),  # type: ignore[arg-type]
    )
    command = AssetTransferCommandV1(
        command_kind=str(spec["kind"]),
        asset=str(spec["asset"]),
        sender=str(spec["sender"]),
        recipient=str(spec["recipient"]),
        amount_atoms=int(spec["amount"]),  # type: ignore[arg-type]
        max_fee_atoms=int(spec["max_fee"]),  # type: ignore[arg-type]
    )
    return context, state, command


def _pre_total(name: str) -> int:
    balances: dict[str, int] = _spec(name)["balances"]  # type: ignore[assignment]
    return sum(balances.values())


# --------------------------------------------------------------------------
# Compilation and placeholder gates
# --------------------------------------------------------------------------


@pytest.fixture(scope="module")
def built_challenge() -> None:
    """Build imports before direct warning checks, including in a clean worktree."""
    build = _lean("build", CHALLENGE_MODULE)
    assert build.returncode == 0, build.stdout + build.stderr


@pytest.mark.parametrize("target", [PROOF, CHALLENGE], ids=["core", "challenge"])
def test_lean_target_compiles_without_warnings(target: Path, built_challenge: None) -> None:
    result = _lean("env", "lean", "-DwarningAsError=true", str(target))
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""


def test_placeholder_gate_is_repository_owned_and_fails_closed() -> None:
    assert SCANNER.is_file(), "the placeholder gate must be committed to this repository"


def test_lean_targets_have_no_placeholders_with_axiom_checking() -> None:
    result = subprocess.run(
        [sys.executable, str(SCANNER), str(PROOF), str(CHALLENGE), "--json"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    assert payload["blocked"] is False
    assert payload["match_count"] == 0
    assert payload["axiom_check"] is True
    assert len(payload["scanned_files"]) == 2


def _axiom_dependencies(output: str) -> set[str]:
    dependencies: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, flags=re.DOTALL):
        dependencies.update(item.strip() for item in body.split(",") if item.strip())
    return dependencies


def _qualified_claims() -> tuple[str, ...]:
    return (
        *(f"{CORE_MODULE}.{name}" for name in CORE_CLAIMS),
        *(f"{CHALLENGE_MODULE}.{name}" for name in CHALLENGE_CLAIMS),
    )


def test_all_named_claims_depend_only_on_standard_lean_axioms(
    tmp_path: Path,
    built_challenge: None,
) -> None:
    qualified = _qualified_claims()
    probe = tmp_path / "AxiomDependencies.lean"
    probe.write_text(
        f"import {CHALLENGE_MODULE}\n\n"
        + "\n".join(f"#print axioms {name}" for name in qualified)
        + "\n",
        encoding="utf-8",
    )
    result = _lean("env", "lean", str(probe))
    assert result.returncode == 0, result.stdout + result.stderr
    for name in qualified:
        assert f"'{name}'" in result.stdout, name
    dependencies = _axiom_dependencies(result.stdout)
    assert dependencies <= ALLOWED_STANDARD_AXIOMS, dependencies


def test_axiom_dependency_parser_reveals_project_defined_axiom() -> None:
    output = "'Demo.bad' depends on axioms: [propext, Demo.trustMe]"
    assert _axiom_dependencies(output) - ALLOWED_STANDARD_AXIOMS == {"Demo.trustMe"}


def test_claim_surface_is_explicit_and_clean() -> None:
    core = PROOF.read_text(encoding="utf-8")
    challenge = CHALLENGE.read_text(encoding="utf-8")
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", core.lower()) is None, token
        assert re.search(rf"\b{re.escape(token)}\b", challenge.lower()) is None, token
    for claim in CORE_CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", core) is not None, claim
    for claim in CHALLENGE_CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", challenge) is not None, claim
    assert len(set(CORE_CLAIMS)) == len(CORE_CLAIMS)
    assert len(set(CHALLENGE_CLAIMS)) == len(CHALLENGE_CLAIMS)
    assert f"import {CORE_MODULE}" in challenge
    proofs_root = PROOFS_ROOT.read_text(encoding="utf-8")
    assert f"import {CORE_MODULE}\n" in proofs_root
    assert f"import {CHALLENGE_MODULE}\n" in proofs_root


# --------------------------------------------------------------------------
# Scope, abstraction, and wording checks against the live sources
# --------------------------------------------------------------------------


def test_proof_states_every_abstraction_and_nonclaim() -> None:
    flat = " ".join(PROOF.read_text(encoding="utf-8").split())
    for phrase in REQUIRED_SCOPE_PHRASES:
        assert phrase in flat, phrase
    lowered = flat.lower()
    for phrase in FORBIDDEN_SCOPE_PHRASES:
        assert phrase not in lowered, phrase
    challenge_flat = " ".join(CHALLENGE.read_text(encoding="utf-8").split())
    assert "bounded source comparison, not a runtime refinement proof" in challenge_flat


def test_lean_guard_order_matches_python_enum_and_transition_source() -> None:
    # Arrange: the Python enum order is the public precedence contract.
    enum_order = [code.value for code in AssetTransferRejectCodeV1]
    core = PROOF.read_text(encoding="utf-8")
    python_source = PYTHON_TRANSITION.read_text(encoding="utf-8")

    # Act: read the wire-string table and the Python if-chain in source order.
    code_def = re.search(r"def RejectCode\.code : RejectCode → String\n((?:\s*\|.*\n)+)", core)
    assert code_def is not None
    lean_order = re.findall(r'=> "([A-Z_]+)"', code_def.group(1))
    policy_body = python_source.split("def _transfer_policy", 1)[1].split("def _transfer_deltas", 1)[0]
    python_policy_order = re.findall(r"AssetTransferRejectCodeV1\.([A-Z_]+)", policy_body)

    # Assert: same closed set, same order, and the Python chain is a prefix.
    assert lean_order == enum_order
    assert len(lean_order) == 12
    assert python_policy_order == enum_order[:8]
    assert enum_order[8:] == [
        "EFFECT_DELTA_OVERFLOW", "INSUFFICIENT_BALANCE", "BALANCE_OVERFLOW",
        "POST_STATE_RESOURCE_BOUND_EXCEEDED",
    ]


def test_runtime_sources_still_match_final_aggregation_and_precedence() -> None:
    """Pins the runtime facts the Lean prose cites so drift re-opens review."""
    python_source = PYTHON_TRANSITION.read_text(encoding="utf-8")
    rust_source = RUST_TRANSITION.read_text(encoding="utf-8")
    aggregate = python_source.index(
        "deltas[policy.fee_owner] = deltas.get(policy.fee_owner, 0) + policy.transfer_fee_atoms"
    )
    width = python_source.index("MIN_DELTA_ATOMS_V1 or delta_atoms > MAX_DELTA_ATOMS_V1")
    assert aggregate < width, "Python aggregates the fee-owner delta before the width check"
    assert "for owner, delta_atoms in deltas.items():" in python_source
    assert "fn checked_negative_sum(left: u128, right: u128)" in rust_source
    assert "const I128_MIN_MAGNITUDE: u128 = 1_u128 << 127;" in rust_source
    assert "if policy.fee_owner == command.sender" in rust_source
    assert "else if policy.fee_owner == command.recipient" in rust_source
    assert "deltas.iter().filter(|(_, delta)| **delta < 0)" in rust_source
    assert "deltas.iter().filter(|(_, delta)| **delta >= 0)" in rust_source


def test_width_literals_match_python_constants_in_source() -> None:
    core = PROOF.read_text(encoding="utf-8")
    assert f"def u128Max : Int := {MAX_ATOMS_V1}\n" in core
    assert f"def i128Max : Int := {MAX_DELTA_ATOMS_V1}\n" in core
    assert f"def i128Min : Int := {MIN_DELTA_ATOMS_V1}\n" in core


# --------------------------------------------------------------------------
# Executable Lean report, compared against live Python behaviour
# --------------------------------------------------------------------------


@pytest.fixture(scope="module")
def report(
    tmp_path_factory: pytest.TempPathFactory,
    built_challenge: None,
) -> dict[str, list[list[str]]]:
    probe = tmp_path_factory.mktemp("challenge") / "Report.lean"
    probe.write_text(REPORT_PROBE, encoding="utf-8")
    result = _lean("env", "lean", str(probe))
    assert result.returncode == 0, result.stdout + result.stderr
    sections: dict[str, list[list[str]]] = {}
    for line in result.stdout.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        fields = line.split(",")
        sections.setdefault(fields[0], []).append(fields[1:])
    assert sections, result.stdout
    return sections


def _vector_row(report: dict[str, list[list[str]]], name: str) -> tuple[str, int, int, int, int]:
    rows = [r for r in report["VECTOR"] if r[0] == name]
    assert len(rows) == 1, (name, rows)
    _, verdict, alice, bob, treasury, supply = rows[0]
    return verdict, int(alice), int(bob), int(treasury), int(supply)


def _movement_rows(report: dict[str, list[list[str]]], name: str) -> set[tuple[str, int]]:
    return {(r[1], int(r[2])) for r in report.get("MOVE", []) if r[0] == name}


def _fee_rows(report: dict[str, list[list[str]]], name: str) -> set[tuple[str, int]]:
    return {(r[1], int(r[2])) for r in report.get("FEE", []) if r[0] == name}


def test_report_reject_code_rows_match_python_enum(report) -> None:
    rows = report["CODE"]
    assert [r[0] for r in rows] == [code.value for code in AssetTransferRejectCodeV1]
    assert len(rows) == 12


def test_report_width_row_matches_python_constants(report) -> None:
    rows = report["WIDTH"]
    assert len(rows) == 1
    assert [int(v) for v in rows[0]] == [MAX_ATOMS_V1, MIN_DELTA_ATOMS_V1, MAX_DELTA_ATOMS_V1]


def test_report_covers_exactly_the_vector_table(report) -> None:
    assert {r[0] for r in report["VECTOR"]} == set(VECTORS)
    assert set(EXPECTED_VERDICTS) == set(VECTORS)
    verdicts = {r[1] for r in report["VECTOR"]}
    # POST_STATE_RESOURCE_BOUND_EXCEEDED is model-unreachable by scope (no row
    # structure in the bounded model); its runtime reachability is pinned by the
    # transition totality suite, and the corpus records it in unreachable_codes.
    model_unreachable = {"POST_STATE_RESOURCE_BOUND_EXCEEDED"}
    assert verdicts == {"ACCEPTED", *(code.value for code in AssetTransferRejectCodeV1)} - model_unreachable


@pytest.mark.parametrize("name", [n for n in VECTORS if n != OUTSIDE_PYTHON_INVARIANT])
def test_vector_matches_live_python_transition(report, name: str) -> None:
    # Arrange
    context, state, command = _python_inputs(name)
    verdict, alice, bob, treasury, supply = _vector_row(report, name)

    # Act
    result = transition_asset_transfer_v1(context, state, command)

    # Assert: same verdict, same post balances, same supply, same rows.
    assert verdict == EXPECTED_VERDICTS[name]
    if isinstance(result, AssetTransferRejectedV1):
        assert result.code.value == verdict
        assert result.effects.is_empty
        assert result.post_state_root == state.state_root
        assert (alice, bob, treasury) == tuple(state.balance_atoms(p, ASSET) for p in PRINCIPALS)
        assert supply == state.supply_atoms(ASSET)
        assert _movement_rows(report, name) == set()
        assert _fee_rows(report, name) == set()
        return
    assert isinstance(result, AssetTransferAcceptedV1)
    assert verdict == "ACCEPTED"
    post = result.post_state
    assert (alice, bob, treasury) == tuple(post.balance_atoms(p, ASSET) for p in PRINCIPALS)
    assert (alice, bob, treasury) == EXPECTED_POST[name]
    assert supply == post.supply_atoms(ASSET) == state.supply_atoms(ASSET)
    python_movements = {
        (row.principal, row.delta_atoms)
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT
    }
    python_fees = {
        (row.principal, row.delta_atoms)
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
    }
    assert _movement_rows(report, name) == python_movements
    assert _fee_rows(report, name) == python_fees
    conservation = result.effects.asset_conservation[0]
    assert conservation.owned_and_custodied_post_atoms == conservation.owned_and_custodied_pre_atoms
    assert alice + bob + treasury == _pre_total(name)


def test_alias_rows_aggregate_before_effect_projection(report) -> None:
    for name, expected in EXPECTED_ALIAS_MOVEMENTS.items():
        assert _movement_rows(report, name) == expected, name
    assert _fee_rows(report, "accept_distinct") == {("treasury", 2)}
    assert _fee_rows(report, "alias_sender") == {("alice", 2)}
    assert _fee_rows(report, "alias_recipient") == {("bob", 2)}
    assert _fee_rows(report, "zero_fee") == set()
    assert _movement_rows(report, "zero_fee") == {("alice", -30), ("bob", 30)}


def test_overflow_neighbor_is_outside_the_python_state_invariant(report) -> None:
    # Arrange: one atom past the recipient maximum forces the total past supply.
    verdict, alice, bob, treasury, supply = _vector_row(report, OUTSIDE_PYTHON_INVARIANT)

    # Act / Assert: Python refuses the state; the total Lean transition rejects.
    with pytest.raises(ValueError, match="account balances exceed supply"):
        _python_inputs(OUTSIDE_PYTHON_INVARIANT)
    assert verdict == "BALANCE_OVERFLOW"
    assert (alice, bob, treasury, supply) == (30, MAX_ATOMS_V1 - 29, 0, MAX_ATOMS_V1)
    assert alice + bob > supply
    assert "balanceOverflow_unreachable" in CORE_CLAIMS


def test_leaky_variant_is_killed_by_the_conservation_check(report) -> None:
    rows = {r[0]: tuple(int(v) for v in r[1:]) for r in report["LEAKY"]}
    assert set(rows) == {"accept_distinct", "alias_sender", "alias_recipient"}
    for name, (pre_total, honest_total, leaky_total) in rows.items():
        # Arrange: the Python transition on the same vector.
        context, state, command = _python_inputs(name)
        # Act
        result = transition_asset_transfer_v1(context, state, command)
        # Assert: Python and the honest model conserve; the leaky variant does not.
        assert isinstance(result, AssetTransferAcceptedV1)
        python_total = sum(result.post_state.balance_atoms(p, ASSET) for p in PRINCIPALS)
        assert pre_total == _pre_total(name)
        assert honest_total == python_total == pre_total
        assert leaky_total != pre_total, name
        assert leaky_total == pre_total - 2, name


def test_role_ordered_loop_agrees_with_intended_rule_on_every_vector(report) -> None:
    rows = {r[0]: (r[1], r[2]) for r in report["ORDER"]}
    assert set(rows) == set(VECTORS)
    for name, (intended, ordered) in rows.items():
        assert intended == ordered, name
        verdict = _vector_row(report, name)[0]
        if verdict in {"INSUFFICIENT_BALANCE", "BALANCE_OVERFLOW"}:
            assert intended == verdict, name
        elif verdict == "ACCEPTED":
            assert intended == "NONE", name


def test_python_reject_is_a_no_op_for_every_rejected_vector() -> None:
    for name in VECTORS:
        if name == OUTSIDE_PYTHON_INVARIANT or EXPECTED_VERDICTS[name] == "ACCEPTED":
            continue
        context, state, command = _python_inputs(name)
        result = transition_asset_transfer_v1(context, state, command)
        assert isinstance(result, AssetTransferRejectedV1), name
        assert result.code is AssetTransferRejectCodeV1(EXPECTED_VERDICTS[name]), name
        assert result.pre_state_root == result.post_state_root == state.state_root
        assert result.effects.is_empty
