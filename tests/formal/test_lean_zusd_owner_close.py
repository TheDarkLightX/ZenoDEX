from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
from pathlib import Path

import pytest

PINNED_LIQUITY_COMMIT = "8f52f2906f99414c0b1c3a84c95c74c319b7a8c6"
PINNED_SOURCES = {
    "packages/contracts/contracts/BorrowerOperations.sol": (
        "b4108d5e529a3bb3ffb1f9a865c8653024e07c5949aa8f6964799fbd2dc03a65"
    ),
    "packages/contracts/contracts/TroveManager.sol": (
        "0b0ba14dc297938b98aa7f130924b3525706fa6b3736fa663c72c40f483f1895"
    ),
    "packages/contracts/contracts/Dependencies/LiquityBase.sol": (
        "a290cf752c79d305a02a6d8d357d36a8f105fd1b63582b1c3d08e3f1e34bae2a"
    ),
    "packages/contracts/contracts/LUSDToken.sol": (
        "d51c34e6b5b779da4ec2016fac2261d93432b8ea67cf76d31fbf677acb659969"
    ),
}


def _lean_context() -> tuple[str, Path, str]:
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("lake executable missing")

    root = Path(__file__).resolve().parents[2]
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    return lake, root / "lean-mathlib", "Proofs/ZUSDOwnerClose.lean"


def _run_lean(lake: str, lean_dir: Path, target: str | Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [lake, "env", "lean", str(target)],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )


def _replace_once(source: str, old: str, new: str) -> str:
    assert source.count(old) == 1, f"mutation anchor count for {old!r} was not one"
    return source.replace(old, new)


def test_lean_zusd_owner_close_typechecks_with_claim_surface() -> None:
    lake, lean_dir, target = _lean_context()
    source = (lean_dir / target).read_text(encoding="utf-8")

    for required in (
        "abbrev U256 := Fin u256Modulus",
        "structure VaultIdentity",
        "theorem vault_identity_value_ne_zero",
        "structure TargetReserveBinding",
        "def expectedTargetReserve",
        "theorem expected_target_reserve_binds_identity_and_amount",
        "theorem lifecycle_target_reserve_exact_partition",
        "structure OwnerCloseAcceptedCertificate",
        "def deriveRiskMode",
        "theorem deriveRiskMode_exact_partition",
        "theorem rejectOrder_has_fourteen_entries",
        "theorem rejectOrder_has_strict_rank_order",
        "theorem guardFailures_eq_nil_iff_admissible",
        "theorem run_owner_close_accepts_iff_admissible",
        "theorem run_owner_close_inadmissible_returns_exact_failures",
        "theorem run_ordered_rejection_is_noop",
        "theorem inadmissible_has_reported_failure",
        "theorem accepted_result_commits_exact_certificate_post",
        "theorem closed_by_owner_is_terminal_for_owner_close",
        "theorem accepted_burns_exact_net_plus_reserve",
        "theorem accepted_candidate_debt_covers_remaining_active_minimum",
        "theorem accepted_candidate_aggregate_has_positive_count_and_collateral_coverage",
        "theorem accepted_gas_pool_is_a_reserve_floor_with_exact_target_binding",
        "theorem accepted_clears_target_reserve_association",
        "theorem witness_ce094_exact_ccr_derives_normal",
        "theorem witness_ce096_ghost_active_minimum_debt_is_rejected",
        "theorem witness_ce097_zero_debt_max_inputs_derive_normal",
        "theorem witness_ce098_excess_gas_pool_donation_is_admissible",
        "theorem witness_ce098_aggregate_reserve_shortfall_is_rejected",
        "theorem witness_ce098_donated_excess_survives_exact_reserve_burn",
        "theorem witness_ce101_remaining_active_collateral_floor_is_rejected",
        "theorem witness_ce104_zero_count_reason_vector_is_complete",
        "theorem witness_ce105_wrong_reserve_target_identity_is_rejected",
        "theorem witness_wrong_reserve_amount_is_rejected",
        "theorem witness_target_reserve_insufficiency_has_exact_reason",
        "theorem witness_ce106_wrong_request_target_is_rejected",
        "effectVaultIdentityExact",
        "effectCloseOccurrenceExact",
        "CE-103 intentionally leaves cumulative burn history out of admission state",
        "Python or Rust refinement",
        "pending-reward calculation/application",
        "atomic",
    ):
        assert required in source

    for forbidden in ("sorry", "admit", "axiom", "unsafe", "native_decide"):
        assert re.search(rf"\b{forbidden}\b", source) is None
    assert "cumulativeZUSDBurn" not in source

    proc = _run_lean(lake, lean_dir, target)
    assert proc.returncode == 0, proc.stdout + proc.stderr


@pytest.mark.parametrize(
    ("label", "old", "new"),
    (
        (
            "strict_ccr",
            "    liquityV1CCRE18 ≤\n      collateral.val * priceE18.val / compositeDebtValue.val",
            "    liquityV1CCRE18 <\n      collateral.val * priceE18.val / compositeDebtValue.val",
        ),
        (
            "zero_debt_branch",
            "  compositeDebtValue.val = 0 ∨\n    liquityV1CCRE18 ≤",
            "  False ∨\n    liquityV1CCRE18 ≤",
        ),
        (
            "zero_vault_identity",
            "  positive : 0 < value.val",
            "  positive : 0 ≤ value.val",
        ),
        (
            "derived_request_target",
            "      if request.targetVaultIdentity = vault.identity then some vault else none",
            "      if True then some vault else none",
        ),
        (
            "remaining_debt_floor",
            "  liquityV1MinNetDebtAtoms + liquityV1GasReserveAtoms",
            "  liquityV1MinNetDebtAtoms",
        ),
        (
            "positive_active_count",
            "    0 < pre.activeVaultAndIndexCount.val ∧\n"
            "    (pre.activeVaultAndIndexCount.val - 1) *",
            "    True ∧\n    (pre.activeVaultAndIndexCount.val - 1) *",
        ),
        (
            "remaining_collateral_floor",
            "    pre.activeVaultAndIndexCount.val - 1 ≤\n"
            "      request.candidateSystemCollateral.val ∧\n"
            "    pre.totalZUSDSupply.val = pre.systemCompositeDebt.val ∧",
            "    True ∧\n"
            "    pre.totalZUSDSupply.val = pre.systemCompositeDebt.val ∧",
        ),
        (
            "donation_griefing_equality",
            "        pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms ≤\n          pre.gasPoolCustody.val))",
            "        pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms =\n          pre.gasPoolCustody.val))",
        ),
        (
            "aggregate_reserve_floor",
            "        pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms ≤\n          pre.gasPoolCustody.val))",
            "        vault.reserveDebt.val ≤ pre.gasPoolCustody.val))",
        ),
        (
            "reserve_target_identity",
            "  targetReserve pre = some (expectedTargetReserve vault) ∧",
            "  (targetReserve pre).map TargetReserveBinding.amount = "
            "some vault.reserveDebt ∧",
        ),
        (
            "reserve_target_amount",
            "    amount := vault.reserveDebt",
            "    amount := u256Zero",
        ),
        (
            "composite_burn",
            "    totalZUSDBurn := compositeDebt vault",
            "    totalZUSDBurn := vault.netDebt",
        ),
        (
            "effect_target_identity",
            "    vaultIdentity := vault.identity",
            "    vaultIdentity := vaultIdentityTwo",
        ),
        (
            "effect_close_occurrence",
            "    closeOccurrence := closeOccurrence",
            "    closeOccurrence := u256Zero",
        ),
        (
            "terminal_target_identity",
            "    lifecycle := .closedByOwner vault.identity closeOccurrence",
            "    lifecycle := .closedByOwner vaultIdentityTwo closeOccurrence",
        ),
        (
            "active_target_variant",
            "  | .active _ binding => some binding",
            "  | .active _ _binding => none",
        ),
        (
            "closed_target_association_clear",
            "def targetReserve (state : OwnerCloseState) : "
            "Option TargetReserveBinding :=\n"
            "  match state.lifecycle with\n"
            "  | .active _ binding => some binding\n"
            "  | .closedByOwner _ _ => none",
            "def targetReserve (state : OwnerCloseState) : "
            "Option TargetReserveBinding :=\n"
            "  match state.lifecycle with\n"
            "  | .active _ binding => some binding\n"
            "  | .closedByOwner _ _ => some {\n"
            "      targetVaultIdentity := vaultIdentityOne\n"
            "      amount := u256Zero\n"
            "    }",
        ),
        (
            "reject_order",
            "    .reserveCustodyMismatch,\n    .reserveCustodyInsufficient,",
            "    .reserveCustodyInsufficient,\n    .reserveCustodyMismatch,",
        ),
        (
            "guard_completeness",
            "  | .reserveCustodyMismatch =>\n"
            "      activeDependentPass pre request fun vault =>\n"
            "        decide (reserveProjectionMatches pre vault)",
            "  | .reserveCustodyMismatch =>\n"
            "      activeDependentPass pre request fun _vault => true",
        ),
        (
            "reject_noop",
            "  | .rejected _ => pre",
            "  | .rejected _ => { pre with transitionSequence := u256Zero }",
        ),
    ),
)
def test_owner_close_semantic_mutations_are_killed(
    tmp_path: Path, label: str, old: str, new: str
) -> None:
    lake, lean_dir, target = _lean_context()
    source = (lean_dir / target).read_text(encoding="utf-8")
    mutant = tmp_path / f"ZUSDOwnerClose_{label}_mutant.lean"
    mutant.write_text(_replace_once(source, old, new), encoding="utf-8")

    proc = _run_lean(lake, lean_dir, mutant)
    assert proc.returncode != 0, f"{label} mutation survived"


def test_lean_zusd_owner_close_is_bound_to_pinned_liquity_sources() -> None:
    checkout = Path("/tmp/liquity-v1-mainnet")
    if not checkout.exists():
        pytest.skip("pinned Liquity V1 checkout missing")

    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=checkout,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    assert commit == PINNED_LIQUITY_COMMIT

    for relative_path, expected_sha256 in PINNED_SOURCES.items():
        source = checkout / relative_path
        assert hashlib.sha256(source.read_bytes()).hexdigest() == expected_sha256

    borrower_operations = (
        checkout / "packages/contracts/contracts/BorrowerOperations.sol"
    ).read_text(encoding="utf-8")
    close_body = borrower_operations[borrower_operations.index("function closeTrove()") :]
    close_body = close_body[: close_body.index("function claimCollateral()")]
    for required in (
        "_requireNotInRecoveryMode(price);",
        "applyPendingRewards(msg.sender);",
        "_requireNewTCRisAboveCCR(newTCR);",
        "removeStake(msg.sender);",
        "closeTrove(msg.sender);",
        "gasPoolAddress, LUSD_GAS_COMPENSATION",
        "sendETH(msg.sender, coll);",
    ):
        assert required in close_body

    lusd_token = (
        checkout / "packages/contracts/contracts/LUSDToken.sol"
    ).read_text(encoding="utf-8")
    recipient_guard = lusd_token[lusd_token.index("function _requireValidRecipient") :]
    recipient_guard = recipient_guard[: recipient_guard.index("function _requireCaller")]
    assert "gasPoolAddress" not in recipient_guard
    assert "_transfer(msg.sender, recipient, amount);" in lusd_token
