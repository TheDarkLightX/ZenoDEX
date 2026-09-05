"""Bounded executable comparison of zUSD owner-close runtime and its Lean model.

``src/core/zusd_owner_close.py`` and ``lean-mathlib/Proofs/ZUSDOwnerClose.lean``
model the same unmounted Liquity V1 F04/F21 owner close, and both files record
Python-to-Lean refinement as an *external* obligation.
``tests/formal/test_lean_zusd_owner_close.py`` typechecks
the Lean file and kills Lean-internal mutants; ``tests/core/test_zusd_owner_close.py``
exercises the Python core alone.

This module supplies the missing executable link.  For each scenario it

1. builds the typed Python prestate/request and runs ``run_owner_close`` plus
   ``committed_state``;
2. projects the same scenario through an explicit abstraction map into the Lean
   model's request/state domain and evaluates the *actual* ``runOwnerClose`` and
   ``committedState`` definitions from ``Proofs/ZUSDOwnerClose.lean``;
3. re-derives the expected complete reject vector, committed state and effect
   plan from pinned Liquity V1 integer arithmetic, independently of both
   implementations.

All three renderings must agree.  The observation covers the accepted effect
plan, the committed poststate (including the debt-free terminal lifecycle and
the owner's collateral credit), the complete ordered reject vector, and the
rejected no-op.

## Abstraction map

The Lean request replaces runtime identity and root comparisons with booleans,
so the projection is

* ``authorityMatchesOwner`` = authenticated actor equals the active vault owner
  **and** the authenticated target equals the requested target;
* ``walletMatchesOwner``    = the wallet projection owner equals the vault owner;
* ``contextCurrent``        = every route/actual/authority/decision root and
  sequence binding agrees, **excluding** the two aggregate equalities the Lean
  model checks separately as ``modeProjectionMatches``;
* ``priceE18``              = the risk-mode decision price.

## Environment

``external/mathlib4`` is absent in this checkout, so the repository's existing
Lean gate for this file skips.  A built Mathlib is located through
``ZENODEX_MATHLIB4_PATH``, ``external/mathlib4`` or ``~/deps/mathlib4``.

Two host facts drive the probe's shape.  First, ``import Mathlib.Tactic``
crashes with SIGSEGV rather than reporting an error, because that umbrella
module transitively imports ``ProofWidgets`` and the local ProofWidgets build
has no top-level olean.  The probe therefore replaces that single import line
with three modules verified by import-graph search to lie inside the umbrella's
own transitive closure; a strict subset of the available tactics cannot make a
false theorem provable, and every definition, theorem and proof script below the
import line is byte-identical to the tracked file.  Second, ``lean`` on PATH is
a newer toolchain than the one Mathlib was built with, and the skew surfaces as
an unreadable olean header, so ``_lean_context`` asserts the executed compiler
version directly.

## Nonclaims

* The pinned Liquity V1 Solidity binding is absent on this host.
  ``test_lean_zusd_owner_close.py::test_lean_zusd_owner_close_is_bound_to_pinned_liquity_sources``
  skips because ``/tmp/liquity-v1-mainnet`` does not exist, so the four recorded
  source SHA-256 pins and the ``closeTrove`` body assertions are unexecuted, and
  no toolchain fix reaches that gap.  Everything below therefore compares this
  runtime against the Lean model, never either of them against Liquity V1: in
  this worktree the model is self-consistent, not source-bound.  A scenario
  agreeing across all three layers is evidence that runtime and model share one
  transition, not that the transition matches the pinned Solidity.
* The projection is undefined when the candidate-TCR decision carries a price
  different from the risk-mode decision, because the Lean request holds one
  price.  ``test_single_price_model_request_cannot_represent_a_split_price``
  records the exact resulting reject-vector divergence.
* The Lean effect record has no owner identity and no sorted-index removal
  target, so those two Python effect legs are outside the compared observation.
* The Lean state has no owner identity, no commitment roots and no gas-reserve
  custody variant beyond the lifecycle-indexed binding; those runtime dimensions
  are folded into booleans by the projection rather than refined.
* Nothing here mounts the transition, authenticates a caller, applies pending
  rewards, or establishes canonical serialization, F15/F16 commit or Rust parity.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from collections import deque
from dataclasses import dataclass, replace
from pathlib import Path

import pytest

from src.core.zusd_owner_close import (
    LIQUITY_V1_CCR_E18,
    LIQUITY_V1_GAS_RESERVE_ATOMS,
    LIQUITY_V1_MIN_NET_DEBT_ATOMS,
    PRICE_SCALE_E18,
    U256_MAX,
    U256_MODULUS,
    ZUSD_SCALE,
    AccountIdentity,
    ActiveVaultCount,
    ActiveWithCompositeDebt,
    AuthenticatedOwnerCapability,
    BoundTargetGasReserve,
    CandidateTCRAtOrAboveCCR,
    CandidateTCRBelowCCR,
    CandidateTCRDecision,
    ClosedByOwner,
    CloseVaultRequest,
    CollateralAtoms,
    CommitmentDigest,
    GasPoolCustodyWithoutTarget,
    OwnerCloseAccepted,
    OwnerCloseContext,
    OwnerCloseReject,
    OwnerCloseRejected,
    OwnerCloseResult,
    OwnerCloseState,
    OwnerWalletProjection,
    PriceE18,
    SequenceNumber,
    StakeAtoms,
    SupplyProjection,
    SystemAggregateProjection,
    VaultIdentity,
    ZUSDAtoms,
    committed_state,
    derive_risk_mode_decision,
    run_owner_close,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN_MODEL = ROOT / "lean-mathlib" / "Proofs" / "ZUSDOwnerClose.lean"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.27.0"
IMPORT_ANCHOR = "import Mathlib.Tactic\n"
IMPORT_SUBSET = (
    "Mathlib.Tactic.Common",
    "Mathlib.Tactic.NormNum",
    "Mathlib.Order.Basic",
)
NAMESPACE = "ZenoDEX.ZUSDOwnerClose"
AXIOM_BOUND = {"propext", "Quot.sound", "Classical.choice"}
CHECKED_THEOREMS = (
    "run_owner_close_accepts_iff_admissible",
    "run_owner_close_inadmissible_returns_exact_failures",
    "guardFailures_eq_nil_iff_admissible",
    "run_ordered_rejection_is_noop",
    "accepted_result_commits_exact_certificate_post",
    "closed_by_owner_is_terminal_for_owner_close",
    "accepted_burns_exact_net_plus_reserve",
    "accepted_returns_full_collateral",
    "accepted_constructs_closed_by_owner_terminal_status",
)

Q = ZUSD_SCALE
RESERVE = LIQUITY_V1_GAS_RESERVE_ATOMS
MIN_NET_DEBT = LIQUITY_V1_MIN_NET_DEBT_ATOMS
MIN_COMPOSITE_DEBT = MIN_NET_DEBT + RESERVE
CCR = LIQUITY_V1_CCR_E18


# --------------------------------------------------------------------------- #
# Lean toolchain access                                                        #
# --------------------------------------------------------------------------- #


def _mathlib_root() -> Path:
    configured = os.environ.get("ZENODEX_MATHLIB4_PATH")
    candidates = [Path(configured)] if configured else []
    candidates.append(ROOT / "external" / "mathlib4")
    candidates.append(Path.home() / "deps" / "mathlib4")
    for candidate in candidates:
        if (candidate / ".lake/build/lib/lean/Mathlib/Tactic.olean").exists():
            return candidate
    raise pytest.skip.Exception("no built mathlib4 checkout is available")


def _lean_context() -> Path:
    """Resolve the Mathlib package and pin the Lean actually used to elaborate.

    ``lean`` on PATH resolves to a newer toolchain than the one Mathlib was
    built with, and a version skew reports as an unreadable olean header rather
    than a clear error, so the executed compiler version is asserted directly.
    """

    if shutil.which("lake") is None:
        raise pytest.skip.Exception("lake executable missing")
    mathlib = _mathlib_root()
    pin = (ROOT / "lean-mathlib" / "lean-toolchain").read_text(encoding="utf-8").strip()
    assert pin == LEAN_TOOLCHAIN, pin
    assert (mathlib / "lean-toolchain").read_text(encoding="utf-8").strip() == pin
    version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=mathlib,
        capture_output=True,
        text=True,
        timeout=120,
        check=True,
    )
    assert "version 4.27.0," in version.stdout, version.stdout
    return mathlib


def _run_lean(source: str, target: Path) -> subprocess.CompletedProcess[str]:
    target.write_text(source, encoding="utf-8")
    return subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", str(target)],
        cwd=_lean_context(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=900,
        check=False,
    )


def _outcome_lines(stdout: str) -> tuple[str, ...]:
    """Keep only rendered transition observations, dropping Lean diagnostics."""

    return tuple(
        line for line in stdout.splitlines() if line.startswith(("ACCEPT|", "REJECT|"))
    )


def _replace_once(source: str, old: str, new: str) -> str:
    assert source.count(old) == 1, f"anchor count for {old!r} was not one"
    return source.replace(old, new)


def _model_source() -> str:
    source = LEAN_MODEL.read_text(encoding="utf-8")
    return _replace_once(
        source,
        IMPORT_ANCHOR,
        "".join(f"import {module}\n" for module in IMPORT_SUBSET),
    )


# --------------------------------------------------------------------------- #
# Shared model domain and the independent integer oracle                       #
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class ModelState:
    """The Lean model's state, as plain integers."""

    lifecycle: str
    vault_id: int
    collateral: int
    net_debt: int
    reserve_debt: int
    stake: int
    binding_target_id: int
    binding_amount: int
    close_occurrence: int
    sys_collateral: int
    sys_debt: int
    sys_stake: int
    active_count: int
    owner_zusd: int
    owner_collateral: int
    gas_pool: int
    supply: int
    sequence: int


@dataclass(frozen=True)
class ModelRequest:
    """The Lean model's request, as plain integers and booleans."""

    target_id: int
    authority_matches_owner: bool
    wallet_matches_owner: bool
    mode_collateral: int
    mode_debt: int
    candidate_collateral: int
    candidate_debt: int
    price: int
    context_current: bool


def _tcr_at_or_above_ccr(collateral: int, debt: int, price: int) -> bool:
    """Liquity's integer collateral ratio test, with the zero-debt convention."""

    if debt == 0:
        return True
    return collateral * price // debt >= CCR


def _oracle_guard_passes(state: ModelState, request: ModelRequest) -> tuple[bool, ...]:
    """Re-derive the fourteen guards from pinned source arithmetic.

    Blocked dependent guards count as passing, matching both layers' ABI.
    """

    active = state.lifecycle == "active" and state.vault_id == request.target_id
    composite = state.net_debt + state.reserve_debt

    underflow_ok = (
        state.collateral <= state.sys_collateral
        and composite <= state.sys_debt
        and state.stake <= state.sys_stake
        and composite <= state.supply
    )
    capacity_ok = (
        state.owner_collateral + state.collateral < U256_MODULUS
        and state.active_count * RESERVE < U256_MODULUS
    )
    remaining_collateral = state.sys_collateral - state.collateral
    remaining_debt = state.sys_debt - composite
    candidate_exact = (
        state.active_count > 0
        and request.candidate_collateral == remaining_collateral
        and request.candidate_debt == remaining_debt
        and remaining_collateral >= state.active_count - 1
        and remaining_debt >= (state.active_count - 1) * MIN_COMPOSITE_DEBT
        and state.supply == state.sys_debt
        and state.owner_zusd <= state.supply
        and state.gas_pool <= state.supply
        and state.owner_zusd + state.gas_pool <= state.supply
    )
    reserve_binding_ok = (
        state.binding_target_id == state.vault_id
        and state.binding_amount == state.reserve_debt
    )
    reserve_custody_ok = state.gas_pool < state.reserve_debt or (
        state.active_count * RESERVE < U256_MODULUS
        and state.active_count * RESERVE <= state.gas_pool
    )
    mode_projection_ok = (
        request.mode_collateral == state.sys_collateral
        and request.mode_debt == state.sys_debt
    )

    arithmetic_prerequisites = active and underflow_ok and capacity_ok
    return (
        active,
        not active or request.authority_matches_owner,
        not active or request.wallet_matches_owner,
        _tcr_at_or_above_ccr(request.mode_collateral, request.mode_debt, request.price),
        not (active and request.wallet_matches_owner)
        or state.net_debt <= state.owner_zusd,
        not active or state.active_count > 1,
        not active or underflow_ok,
        not active or capacity_ok,
        not arithmetic_prerequisites or candidate_exact,
        not (arithmetic_prerequisites and candidate_exact)
        or _tcr_at_or_above_ccr(
            request.candidate_collateral, request.candidate_debt, request.price
        ),
        not active or (reserve_binding_ok and reserve_custody_ok),
        not active or state.reserve_debt <= state.gas_pool,
        state.sequence < U256_MAX,
        request.context_current and mode_projection_ok,
    )


def _oracle_post_state(state: ModelState) -> ModelState:
    composite = state.net_debt + state.reserve_debt
    occurrence = state.sequence + 1
    return ModelState(
        lifecycle="closed",
        vault_id=state.vault_id,
        collateral=0,
        net_debt=0,
        reserve_debt=0,
        stake=0,
        binding_target_id=0,
        binding_amount=0,
        close_occurrence=occurrence,
        sys_collateral=state.sys_collateral - state.collateral,
        sys_debt=state.sys_debt - composite,
        sys_stake=state.sys_stake - state.stake,
        active_count=state.active_count - 1,
        owner_zusd=state.owner_zusd - state.net_debt,
        owner_collateral=state.owner_collateral + state.collateral,
        gas_pool=state.gas_pool - state.reserve_debt,
        supply=state.supply - composite,
        sequence=occurrence,
    )


def _render_model_state(state: ModelState) -> str:
    if state.lifecycle == "active":
        lifecycle = ";".join(
            str(value)
            for value in (
                "active",
                state.vault_id,
                state.collateral,
                state.net_debt,
                state.reserve_debt,
                state.stake,
                state.binding_target_id,
                state.binding_amount,
            )
        )
    else:
        lifecycle = ";".join(
            str(value) for value in ("closed", state.vault_id, state.close_occurrence)
        )
    return ";".join(
        str(value)
        for value in (
            lifecycle,
            state.sys_collateral,
            state.sys_debt,
            state.sys_stake,
            state.active_count,
            state.owner_zusd,
            state.owner_collateral,
            state.gas_pool,
            state.supply,
            state.sequence,
        )
    )


def _oracle_observation(state: ModelState, request: ModelRequest) -> str:
    passes = _oracle_guard_passes(state, request)
    reject_names = tuple(reason.value for reason in OwnerCloseReject)
    failures = tuple(
        name for name, passed in zip(reject_names, passes, strict=True) if not passed
    )
    if failures:
        return f"REJECT|{','.join(failures)}|{_render_model_state(state)}"
    post = _oracle_post_state(state)
    composite = state.net_debt + state.reserve_debt
    effects = ";".join(
        str(value)
        for value in (
            state.vault_id,
            post.sequence,
            state.net_debt,
            state.reserve_debt,
            composite,
            composite,
            state.collateral,
            state.collateral,
            state.stake,
            1,
        )
    )
    return f"ACCEPT|{effects}|{_render_model_state(post)}"


# --------------------------------------------------------------------------- #
# Runtime construction and the abstraction map                                 #
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class Case:
    """One scenario, expressed in runtime construction parameters."""

    name: str
    vault_id: int = 101
    owner_id: int = 11
    collateral: int = 12 * Q
    net_debt: int = 1_800 * Q
    stake: int = 12 * Q
    sys_collateral: int = 24 * Q
    sys_debt: int = 4_000 * Q
    sys_stake: int = 32 * Q
    active_count: int = 2
    wallet_owner_id: int = 11
    wallet_zusd: int = 1_800 * Q
    wallet_collateral: int = 0
    reserve_target_id: int = 101
    reserve_amount: int = RESERVE
    gas_pool: int = 400 * Q
    supply: int = 4_000 * Q
    sequence: int = 0
    request_target_id: int = 101
    authority_actor_id: int = 11
    authority_target_id: int = 101
    mode_collateral: int | None = None
    mode_debt: int | None = None
    price: int = 250 * PRICE_SCALE_E18
    candidate_collateral: int | None = None
    candidate_debt: int | None = None
    candidate_price: int | None = None
    binding: str = "current"
    replay_after_close: bool = False


def _digest(fill: int) -> CommitmentDigest:
    return CommitmentDigest(bytes([fill]) * 32)


def _context(fill: int, sequence: int) -> OwnerCloseContext:
    digest = _digest(fill)
    return OwnerCloseContext(
        vault_state_root=digest,
        asset_ledger_root=digest,
        gas_reserve_root=digest,
        risk_decision_root=digest,
        owner_close_sequence=SequenceNumber(sequence),
    )


def _candidate_decision(
    context: OwnerCloseContext, collateral: int, debt: int, price: int
) -> CandidateTCRDecision:
    """Select the typed candidate variant from independent integer arithmetic."""

    variant = (
        CandidateTCRAtOrAboveCCR
        if _tcr_at_or_above_ccr(collateral, debt, price)
        else CandidateTCRBelowCCR
    )
    return variant(
        source_context=context,
        candidate_system_collateral_atoms=CollateralAtoms(collateral),
        candidate_system_composite_debt_atoms=ZUSDAtoms(debt),
        price_e18=PriceE18(price),
    )


def _build_runtime(case: Case) -> tuple[OwnerCloseState, CloseVaultRequest]:
    vault = ActiveWithCompositeDebt(
        vault_identity=VaultIdentity(case.vault_id),
        owner_identity=AccountIdentity(case.owner_id),
        collateral_atoms=CollateralAtoms(case.collateral),
        net_debt_atoms=ZUSDAtoms(case.net_debt),
        reserve_debt_atoms=ZUSDAtoms(RESERVE),
        stake_atoms=StakeAtoms(case.stake),
    )
    state = OwnerCloseState(
        lifecycle=vault,
        system=SystemAggregateProjection(
            collateral_atoms=CollateralAtoms(case.sys_collateral),
            composite_debt_atoms=ZUSDAtoms(case.sys_debt),
            total_active_stake_atoms=StakeAtoms(case.sys_stake),
            active_vault_and_index_count=ActiveVaultCount(case.active_count),
        ),
        owner_wallet=OwnerWalletProjection(
            owner_identity=AccountIdentity(case.wallet_owner_id),
            zusd_balance_atoms=ZUSDAtoms(case.wallet_zusd),
            collateral_balance_atoms=CollateralAtoms(case.wallet_collateral),
        ),
        gas_reserve=BoundTargetGasReserve(
            target_vault_identity=VaultIdentity(case.reserve_target_id),
            target_reserve_atoms=ZUSDAtoms(case.reserve_amount),
            gas_pool_custody_atoms=ZUSDAtoms(case.gas_pool),
        ),
        supply=SupplyProjection(total_zusd_supply_atoms=ZUSDAtoms(case.supply)),
        transition_sequence=SequenceNumber(case.sequence),
    )

    actual = _context(1, case.sequence)
    route = actual
    authority_context = actual
    authority_sequence = case.sequence
    mode_context = actual
    candidate_context = actual
    if case.binding == "route_root":
        route = _context(2, case.sequence)
    elif case.binding == "actual_sequence":
        actual = _context(1, case.sequence + 1)
        route = actual
        authority_context = actual
        mode_context = actual
        candidate_context = actual
    elif case.binding == "authority_root":
        authority_context = _context(3, case.sequence)
    elif case.binding == "authority_sequence":
        authority_sequence = case.sequence + 1
    elif case.binding == "mode_root":
        mode_context = _context(4, case.sequence)
    elif case.binding == "candidate_root":
        candidate_context = _context(5, case.sequence)
    elif case.binding != "current":
        raise ValueError(f"unknown binding variant {case.binding!r}")

    composite = case.net_debt + RESERVE
    mode_collateral = (
        case.sys_collateral if case.mode_collateral is None else case.mode_collateral
    )
    mode_debt = case.sys_debt if case.mode_debt is None else case.mode_debt
    candidate_collateral = (
        case.sys_collateral - case.collateral
        if case.candidate_collateral is None
        else case.candidate_collateral
    )
    candidate_debt = (
        case.sys_debt - composite if case.candidate_debt is None else case.candidate_debt
    )
    candidate_price = case.price if case.candidate_price is None else case.candidate_price

    request = CloseVaultRequest(
        target_vault_identity=VaultIdentity(case.request_target_id),
        authority=AuthenticatedOwnerCapability(
            actor_identity=AccountIdentity(case.authority_actor_id),
            target_vault_identity=VaultIdentity(case.authority_target_id),
            authenticated_command_occurrence=SequenceNumber(7),
            expected_context=authority_context,
            expected_owner_close_sequence=SequenceNumber(authority_sequence),
        ),
        risk_mode=derive_risk_mode_decision(
            source_context=mode_context,
            system_collateral_atoms=CollateralAtoms(mode_collateral),
            system_composite_debt_atoms=ZUSDAtoms(mode_debt),
            price_e18=PriceE18(case.price),
        ),
        candidate_tcr=_candidate_decision(
            candidate_context, candidate_collateral, candidate_debt, candidate_price
        ),
        route_context=route,
        actual_context=actual,
    )
    return state, request


def _project(
    state: OwnerCloseState, request: CloseVaultRequest
) -> tuple[ModelState, ModelRequest]:
    """Abstraction map from the typed runtime domain into the Lean model domain."""

    mode = request.risk_mode
    candidate = request.candidate_tcr
    assert candidate.price_e18 == mode.price_e18, (
        "the Lean request carries one price; a split-price request has no image"
    )

    lifecycle = state.lifecycle
    if type(lifecycle) is ActiveWithCompositeDebt:
        reserve = state.gas_reserve
        assert type(reserve) is BoundTargetGasReserve
        model_state = ModelState(
            lifecycle="active",
            vault_id=lifecycle.vault_identity.value,
            collateral=lifecycle.collateral_atoms.value,
            net_debt=lifecycle.net_debt_atoms.value,
            reserve_debt=lifecycle.reserve_debt_atoms.value,
            stake=lifecycle.stake_atoms.value,
            binding_target_id=reserve.target_vault_identity.value,
            binding_amount=reserve.target_reserve_atoms.value,
            close_occurrence=0,
            sys_collateral=state.system.collateral_atoms.value,
            sys_debt=state.system.composite_debt_atoms.value,
            sys_stake=state.system.total_active_stake_atoms.value,
            active_count=state.system.active_vault_and_index_count.value,
            owner_zusd=state.owner_wallet.zusd_balance_atoms.value,
            owner_collateral=state.owner_wallet.collateral_balance_atoms.value,
            gas_pool=reserve.gas_pool_custody_atoms.value,
            supply=state.supply.total_zusd_supply_atoms.value,
            sequence=state.transition_sequence.value,
        )
        authority_matches_owner = (
            request.authority.actor_identity == lifecycle.owner_identity
            and request.authority.target_vault_identity == request.target_vault_identity
        )
        wallet_matches_owner = (
            state.owner_wallet.owner_identity == lifecycle.owner_identity
        )
    else:
        assert type(lifecycle) is ClosedByOwner
        reserve = state.gas_reserve
        assert type(reserve) is GasPoolCustodyWithoutTarget
        model_state = ModelState(
            lifecycle="closed",
            vault_id=lifecycle.vault_identity.value,
            collateral=0,
            net_debt=0,
            reserve_debt=0,
            stake=0,
            binding_target_id=0,
            binding_amount=0,
            close_occurrence=lifecycle.close_occurrence.value,
            sys_collateral=state.system.collateral_atoms.value,
            sys_debt=state.system.composite_debt_atoms.value,
            sys_stake=state.system.total_active_stake_atoms.value,
            active_count=state.system.active_vault_and_index_count.value,
            owner_zusd=state.owner_wallet.zusd_balance_atoms.value,
            owner_collateral=state.owner_wallet.collateral_balance_atoms.value,
            gas_pool=reserve.gas_pool_custody_atoms.value,
            supply=state.supply.total_zusd_supply_atoms.value,
            sequence=state.transition_sequence.value,
        )
        # A closed occurrence has no owner field, and the Lean model never reads
        # these two flags without an active target.
        authority_matches_owner = True
        wallet_matches_owner = True

    context_current = all(
        (
            request.route_context == request.actual_context,
            request.actual_context.owner_close_sequence == state.transition_sequence,
            request.authority.expected_context == request.actual_context,
            request.authority.expected_owner_close_sequence == state.transition_sequence,
            mode.source_context == request.actual_context,
            candidate.source_context == request.actual_context,
            candidate.price_e18 == mode.price_e18,
        )
    )
    model_request = ModelRequest(
        target_id=request.target_vault_identity.value,
        authority_matches_owner=authority_matches_owner,
        wallet_matches_owner=wallet_matches_owner,
        mode_collateral=mode.system_collateral_atoms.value,
        mode_debt=mode.system_composite_debt_atoms.value,
        candidate_collateral=candidate.candidate_system_collateral_atoms.value,
        candidate_debt=candidate.candidate_system_composite_debt_atoms.value,
        price=mode.price_e18.value,
        context_current=context_current,
    )
    return model_state, model_request


def _render_runtime_state(state: OwnerCloseState) -> str:
    lifecycle = state.lifecycle
    if type(lifecycle) is ActiveWithCompositeDebt:
        reserve = state.gas_reserve
        assert type(reserve) is BoundTargetGasReserve
        head = ";".join(
            str(value)
            for value in (
                "active",
                lifecycle.vault_identity.value,
                lifecycle.collateral_atoms.value,
                lifecycle.net_debt_atoms.value,
                lifecycle.reserve_debt_atoms.value,
                lifecycle.stake_atoms.value,
                reserve.target_vault_identity.value,
                reserve.target_reserve_atoms.value,
            )
        )
    else:
        assert type(lifecycle) is ClosedByOwner
        head = ";".join(
            str(value)
            for value in (
                "closed",
                lifecycle.vault_identity.value,
                lifecycle.close_occurrence.value,
            )
        )
    return ";".join(
        str(value)
        for value in (
            head,
            state.system.collateral_atoms.value,
            state.system.composite_debt_atoms.value,
            state.system.total_active_stake_atoms.value,
            state.system.active_vault_and_index_count.value,
            state.owner_wallet.zusd_balance_atoms.value,
            state.owner_wallet.collateral_balance_atoms.value,
            state.gas_reserve.gas_pool_custody_atoms.value,
            state.supply.total_zusd_supply_atoms.value,
            state.transition_sequence.value,
        )
    )


def _render_runtime_result(result: OwnerCloseResult) -> str:
    committed = _render_runtime_state(committed_state(result))
    if type(result) is OwnerCloseAccepted:
        effects = result.effects
        plan = ";".join(
            str(value)
            for value in (
                effects.vault_identity.value,
                effects.close_occurrence.value,
                effects.owner_net_debt_burn_atoms.value,
                effects.gas_reserve_burn_atoms.value,
                effects.total_zusd_burn_atoms.value,
                effects.system_composite_debt_decrease_atoms.value,
                effects.collateral_return_atoms.value,
                effects.system_collateral_decrease_atoms.value,
                effects.stake_removal_atoms.value,
                effects.active_vault_and_index_count_decrease.value,
            )
        )
        return f"ACCEPT|{plan}|{committed}"
    assert type(result) is OwnerCloseRejected
    return f"REJECT|{','.join(reason.value for reason in result.violations)}|{committed}"


# --------------------------------------------------------------------------- #
# Lean probe generation                                                        #
# --------------------------------------------------------------------------- #


def _camel_to_snake(name: str) -> str:
    return re.sub(
        r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])", "_", name
    ).lower()


def _lean_reject_order(source: str) -> tuple[str, ...]:
    body = source[source.index("def rejectOrder : List OwnerCloseReject :=") :]
    body = body[: body.index("\n\n")]
    return tuple(re.findall(r"\.([A-Za-z]+)[,\]]", body))


def _u256(value: int) -> str:
    return f"⟨{value}, (by norm_num [u256Modulus])⟩"


def _vault_identity(value: int) -> str:
    return f"⟨{_u256(value)}, (by norm_num)⟩"


def _lean_state(name: str, state: ModelState) -> str:
    if state.lifecycle == "active":
        lifecycle = (
            f"      .active\n"
            f"        {{ identity := {_vault_identity(state.vault_id)}\n"
            f"          collateral := {_u256(state.collateral)}\n"
            f"          netDebt := {_u256(state.net_debt)}\n"
            f"          reserveDebt := {_u256(state.reserve_debt)}\n"
            f"          stake := {_u256(state.stake)}\n"
            f"          collateralPositive := (by norm_num)\n"
            f"          netDebtAtLeastSourceMinimum :=\n"
            f"            (by norm_num [liquityV1MinNetDebtAtoms, atomsScale])\n"
            f"          reserveIsSourceConstant :=\n"
            f"            (by norm_num [liquityV1GasReserveAtoms, atomsScale])\n"
            f"          compositeDebtFits := (by norm_num [u256Modulus]) }}\n"
            f"        {{ targetVaultIdentity := "
            f"{_vault_identity(state.binding_target_id)}\n"
            f"          amount := {_u256(state.binding_amount)} }}"
        )
    else:
        lifecycle = (
            f"      .closedByOwner {_vault_identity(state.vault_id)} "
            f"{_u256(state.close_occurrence)}"
        )
    return (
        f"def {name} : OwnerCloseState :=\n"
        f"  {{ lifecycle :=\n{lifecycle}\n"
        f"    systemCollateral := {_u256(state.sys_collateral)}\n"
        f"    systemCompositeDebt := {_u256(state.sys_debt)}\n"
        f"    totalActiveStake := {_u256(state.sys_stake)}\n"
        f"    activeVaultAndIndexCount := {_u256(state.active_count)}\n"
        f"    ownerZUSDBalance := {_u256(state.owner_zusd)}\n"
        f"    ownerCollateralBalance := {_u256(state.owner_collateral)}\n"
        f"    gasPoolCustody := {_u256(state.gas_pool)}\n"
        f"    totalZUSDSupply := {_u256(state.supply)}\n"
        f"    transitionSequence := {_u256(state.sequence)} }}\n"
    )


def _lean_request(name: str, request: ModelRequest) -> str:
    return (
        f"def {name} : CloseVaultRequest :=\n"
        f"  {{ targetVaultIdentity := {_vault_identity(request.target_id)}\n"
        f"    authorityMatchesOwner := {str(request.authority_matches_owner).lower()}\n"
        f"    walletMatchesOwner := {str(request.wallet_matches_owner).lower()}\n"
        f"    modeSystemCollateral := {_u256(request.mode_collateral)}\n"
        f"    modeSystemCompositeDebt := {_u256(request.mode_debt)}\n"
        f"    candidateSystemCollateral := {_u256(request.candidate_collateral)}\n"
        f"    candidateSystemCompositeDebt := {_u256(request.candidate_debt)}\n"
        f"    priceE18 := {_u256(request.price)}\n"
        f"    pricePositive := (by norm_num)\n"
        f"    systemNumeratorFitsWhenDebtPositive :=\n"
        f"      (by intro _h; norm_num [u256Modulus])\n"
        f"    candidateNumeratorFitsWhenDebtPositive :=\n"
        f"      (by intro _h; norm_num [u256Modulus])\n"
        f"    contextCurrent := {str(request.context_current).lower()} }}\n"
    )


def _lean_probe_prelude(reject_order: tuple[str, ...]) -> str:
    arms = "\n".join(
        f"  | .{name} => \"{_camel_to_snake(name)}\"" for name in reject_order
    )
    return f"""
namespace ZenoDEXOwnerCloseRuntimeProbeV1

open {NAMESPACE}

def rejectName : OwnerCloseReject → String
{arms}

def renderLifecycle (state : OwnerCloseState) : String :=
  match state.lifecycle with
  | .active vault binding =>
      String.intercalate ";"
        ["active", toString vault.identity.value.val, toString vault.collateral.val,
          toString vault.netDebt.val, toString vault.reserveDebt.val,
          toString vault.stake.val,
          toString binding.targetVaultIdentity.value.val,
          toString binding.amount.val]
  | .closedByOwner identity occurrence =>
      String.intercalate ";"
        ["closed", toString identity.value.val, toString occurrence.val]

def renderState (state : OwnerCloseState) : String :=
  String.intercalate ";"
    [renderLifecycle state, toString state.systemCollateral.val,
      toString state.systemCompositeDebt.val, toString state.totalActiveStake.val,
      toString state.activeVaultAndIndexCount.val,
      toString state.ownerZUSDBalance.val, toString state.ownerCollateralBalance.val,
      toString state.gasPoolCustody.val, toString state.totalZUSDSupply.val,
      toString state.transitionSequence.val]

def renderEffects (effects : OwnerCloseEffects) : String :=
  String.intercalate ";"
    [toString effects.vaultIdentity.value.val, toString effects.closeOccurrence.val,
      toString effects.ownerNetDebtBurn.val, toString effects.gasReserveBurn.val,
      toString effects.totalZUSDBurn.val,
      toString effects.systemCompositeDebtDecrease.val,
      toString effects.collateralReturn.val,
      toString effects.systemCollateralDecrease.val,
      toString effects.stakeRemoval.val,
      toString effects.activeVaultAndIndexCountDecrease.val]

def renderOutcome (pre : OwnerCloseState) (request : CloseVaultRequest) : String :=
  let result := runOwnerClose pre request
  let committed := committedState pre request result
  match result with
  | .accepted certificate =>
      "ACCEPT|" ++ renderEffects certificate.effects ++ "|" ++ renderState committed
  | .rejected failures =>
      "REJECT|" ++ String.intercalate "," (failures.map rejectName) ++ "|"
        ++ renderState committed
"""


def _lean_probe(cases: tuple[Case, ...], model_source: str) -> str:
    reject_order = _lean_reject_order(model_source)
    blocks = [model_source, _lean_probe_prelude(reject_order)]
    for index, case in enumerate(cases):
        state, request = _build_runtime(case)
        model_state, model_request = _project(state, request)
        blocks.append(_lean_state(f"pre{index}", model_state))
        blocks.append(_lean_request(f"req{index}", model_request))
        blocks.append(f"#eval IO.println (renderOutcome pre{index} req{index})\n")
        if case.replay_after_close:
            blocks.append(
                f"def post{index} : OwnerCloseState :=\n"
                f"  committedState pre{index} req{index} "
                f"(runOwnerClose pre{index} req{index})\n"
                f"#eval IO.println (renderOutcome post{index} req{index})\n"
            )
    blocks.append("\nend ZenoDEXOwnerCloseRuntimeProbeV1\n")
    return "\n".join(blocks)


# --------------------------------------------------------------------------- #
# Scenario corpus                                                              #
# --------------------------------------------------------------------------- #

CASES: tuple[Case, ...] = (
    # Acceptance at the exact 150% candidate CCR boundary, replayed afterwards.
    Case(name="accept_exact_ccr_boundary", replay_after_close=True),
    # Acceptance with a strictly larger owner balance and prior collateral.
    Case(
        name="accept_surplus_balance_and_prior_collateral",
        wallet_zusd=1_900 * Q,
        wallet_collateral=7 * Q,
    ),
    # One donated Gas Pool atom must not grief the close.
    Case(name="accept_donated_gas_pool_atom", gas_pool=400 * Q + 1),
    # Three active vaults: floors and the reserve cardinality both scale.
    Case(
        name="accept_three_active_vaults",
        active_count=3,
        sys_collateral=36 * Q,
        sys_debt=6_000 * Q,
        sys_stake=48 * Q,
        supply=6_000 * Q,
        gas_pool=600 * Q,
    ),
    # Ordinal 0: the request names a vault that is not the active occurrence.
    Case(name="reject_wrong_request_target", request_target_id=102),
    # Ordinal 1: authenticated actor is not the vault owner.
    Case(name="reject_wrong_actor", authority_actor_id=12),
    # Ordinal 1: authenticated target is not the requested target.
    Case(name="reject_authority_target_drift", authority_target_id=102),
    # Ordinal 2: the wallet projection belongs to another account.
    Case(name="reject_wallet_owner_mismatch", wallet_owner_id=12),
    # Ordinals 2 and 4: a foreign wallet blocks the balance guard.
    Case(
        name="reject_wallet_mismatch_blocks_balance",
        wallet_owner_id=12,
        wallet_zusd=0,
    ),
    # Ordinal 3: system TCR one atom below the CCR is Recovery Mode.
    Case(
        name="reject_recovery_mode",
        sys_collateral=24 * Q - 1,
        candidate_collateral=12 * Q - 1,
    ),
    # Ordinal 4: owner balance one atom below the exact net debt.
    Case(name="reject_owner_balance_short", wallet_zusd=1_800 * Q - 1),
    # Ordinal 4 boundary: owner balance exactly equal to net debt accepts.
    Case(name="accept_owner_balance_exact", wallet_zusd=1_800 * Q),
    # Ordinal 5: the last active vault cannot close.
    Case(
        name="reject_final_active_vault",
        active_count=1,
        sys_collateral=12 * Q,
        sys_debt=2_000 * Q,
        sys_stake=12 * Q,
        supply=2_000 * Q,
        gas_pool=200 * Q,
    ),
    # Ordinal 0 with a foreign wallet: both identity guards stay blocked.
    Case(
        name="reject_wrong_target_with_foreign_wallet",
        request_target_id=102,
        wallet_owner_id=12,
    ),
    # Ordinal 6: aggregate stake below the source stake underflows.
    Case(name="reject_aggregate_stake_underflow", sys_stake=11 * Q),
    # Ordinal 6 blocks ordinal 8 even when the candidate aggregate is wrong.
    Case(
        name="reject_underflow_blocks_inexact_candidate",
        sys_stake=11 * Q,
        candidate_collateral=12 * Q + 5,
    ),
    # Ordinal 8: candidate aggregate does not equal the exact remainder.
    Case(name="reject_candidate_collateral_drift", candidate_collateral=12 * Q + 1),
    # Ordinal 8: supply must equal the aggregate composite debt.
    Case(name="reject_supply_debt_mismatch", supply=4_000 * Q + 1),
    # Ordinal 8: a remaining vault cannot be backed by reserve-only debt.
    Case(
        name="reject_remaining_debt_floor",
        sys_debt=2_200 * Q,
        supply=2_200 * Q,
        candidate_debt=200 * Q,
        mode_debt=2_200 * Q,
    ),
    # Ordinal 9: one extra source collateral atom pushes the candidate TCR
    # one atom below the CCR while the system aggregate stays in Normal Mode.
    Case(name="reject_candidate_tcr_below_ccr", collateral=12 * Q + 1),
    # Ordinal 10: reserve custody bound to a different vault identity.
    Case(name="reject_reserve_target_identity", reserve_target_id=102),
    # Ordinal 10: correct target but the aggregate reserve floor is one short.
    Case(name="reject_aggregate_reserve_shortfall", gas_pool=400 * Q - 1),
    # Ordinals 10 and 11: custody below one target reserve.
    Case(name="reject_target_reserve_insufficient", gas_pool=200 * Q - 1),
    # Ordinal 12 boundary: the maximum non-exhausted sequence still accepts.
    Case(name="accept_sequence_upper_boundary", sequence=U256_MAX - 1),
    # Ordinal 12: an exhausted sequence rejects.
    Case(name="reject_sequence_exhausted", sequence=U256_MAX),
    # Ordinal 13: each context binding substitution is stale.
    Case(name="reject_stale_route_root", binding="route_root"),
    Case(name="reject_stale_actual_sequence", binding="actual_sequence"),
    Case(name="reject_stale_authority_root", binding="authority_root"),
    Case(name="reject_stale_authority_sequence", binding="authority_sequence"),
    Case(name="reject_stale_mode_root", binding="mode_root"),
    Case(name="reject_stale_candidate_root", binding="candidate_root"),
    # Ordinal 13: the risk decision was taken on a different aggregate.
    Case(name="reject_stale_mode_aggregate", mode_collateral=25 * Q),
    # Multiple simultaneous failures keep the complete ordered vector.
    Case(
        name="reject_multiple_ordered_failures",
        authority_actor_id=12,
        wallet_owner_id=13,
        active_count=1,
        sys_collateral=12 * Q,
        sys_debt=2_000 * Q,
        sys_stake=12 * Q,
        supply=2_000 * Q,
        gas_pool=200 * Q,
        binding="route_root",
    ),
)

ACCEPTING = tuple(case.name for case in CASES if case.name.startswith("accept_"))
REJECTING = tuple(case.name for case in CASES if case.name.startswith("reject_"))


@pytest.fixture(scope="module")
def lean_outcomes(tmp_path_factory: pytest.TempPathFactory) -> tuple[str, ...]:
    """Evaluate every projected scenario against the actual Lean model once."""

    _lean_context()
    probe = _lean_probe(CASES, _model_source())
    target = tmp_path_factory.mktemp("owner_close_probe") / "ZUSDOwnerCloseProbe.lean"
    result = _run_lean(probe, target)
    assert result.returncode == 0, result.stdout + result.stderr
    lines = _outcome_lines(result.stdout)
    expected = len(CASES) + sum(1 for case in CASES if case.replay_after_close)
    assert len(lines) == expected, result.stdout
    return lines


def _lean_index(case_name: str) -> int:
    index = 0
    for case in CASES:
        if case.name == case_name:
            return index
        index += 2 if case.replay_after_close else 1
    raise KeyError(case_name)


# --------------------------------------------------------------------------- #
# Tests                                                                        #
# --------------------------------------------------------------------------- #


def test_probe_import_substitution_is_a_subset_of_the_tracked_import() -> None:
    """The probe may only weaken the tactic set, never extend it."""

    mathlib = _lean_context()
    pattern = re.compile(
        r"^(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)"
    )
    reached: set[str] = set()
    queue = deque(["Mathlib.Tactic"])
    while queue:
        module = queue.popleft()
        if module in reached:
            continue
        reached.add(module)
        path = mathlib / (module.replace(".", "/") + ".lean")
        if not path.exists():
            continue
        for line in path.read_text(encoding="utf-8").splitlines():
            match = pattern.match(line.strip())
            if match is not None and match.group(1) not in reached:
                queue.append(match.group(1))

    assert "Mathlib.Tactic" in reached
    for module in IMPORT_SUBSET:
        assert module in reached, module

    original = LEAN_MODEL.read_text(encoding="utf-8")
    head, anchor, tail = original.partition(IMPORT_ANCHOR)
    assert head == "" and anchor == IMPORT_ANCHOR
    substitution = "".join(f"import {module}\n" for module in IMPORT_SUBSET)
    # Everything below the import line is byte-identical to the tracked model.
    assert _model_source() == substitution + tail


def test_lean_owner_close_model_typechecks_and_stays_inside_the_axiom_bound(
    tmp_path: Path,
) -> None:
    """The tracked model elaborates here, so the differential runs real proofs."""

    source = LEAN_MODEL.read_text(encoding="utf-8")
    assert re.search(r"\b(sorry|admit|axiom|native_decide)\b", source) is None
    probe = _model_source() + "\n" + "\n".join(
        f"#print axioms {NAMESPACE}.{name}" for name in CHECKED_THEOREMS
    )
    result = _run_lean(probe, tmp_path / "ZUSDOwnerCloseAxioms.lean")
    assert result.returncode == 0, result.stdout + result.stderr
    for name in CHECKED_THEOREMS:
        assert f"'{NAMESPACE}.{name}'" in result.stdout
    axioms = {
        entry.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        for entry in group.split(",")
        if entry.strip()
    }
    assert axioms <= AXIOM_BOUND, axioms


def test_reject_abi_names_and_order_agree_between_runtime_and_model() -> None:
    """The fourteen-reason ABI is one contract shared by both layers."""

    lean_order = _lean_reject_order(LEAN_MODEL.read_text(encoding="utf-8"))
    assert len(lean_order) == 14
    assert tuple(_camel_to_snake(name) for name in lean_order) == tuple(
        reason.value for reason in OwnerCloseReject
    )


@pytest.mark.parametrize("case_name", [case.name for case in CASES])
def test_runtime_lean_and_independent_oracle_agree(
    lean_outcomes: tuple[str, ...], case_name: str
) -> None:
    """Runtime outcome, projected model outcome and integer oracle must coincide."""

    case = next(entry for entry in CASES if entry.name == case_name)
    state, request = _build_runtime(case)
    model_state, model_request = _project(state, request)

    runtime = _render_runtime_result(run_owner_close(state, request))
    oracle = _oracle_observation(model_state, model_request)
    lean = lean_outcomes[_lean_index(case_name)]

    assert runtime == oracle, f"runtime and oracle disagree for {case_name}"
    assert runtime == lean, f"runtime and Lean model disagree for {case_name}"


@pytest.mark.parametrize("case_name", ACCEPTING)
def test_accepted_close_is_debt_free_terminal_with_exact_owner_credit(
    case_name: str,
) -> None:
    """Acceptance retires the composite debt and hands the owner the collateral."""

    case = next(entry for entry in CASES if entry.name == case_name)
    state, request = _build_runtime(case)
    result = run_owner_close(state, request)
    assert type(result) is OwnerCloseAccepted

    committed = committed_state(result)
    composite = case.net_debt + RESERVE
    assert type(committed.lifecycle) is ClosedByOwner
    assert committed.lifecycle.vault_identity.value == case.vault_id
    assert committed.lifecycle.close_occurrence.value == case.sequence + 1
    assert type(committed.gas_reserve) is GasPoolCustodyWithoutTarget
    # Independent expectations, recomputed from the scenario parameters.
    assert committed.supply.total_zusd_supply_atoms.value == case.supply - composite
    assert committed.system.composite_debt_atoms.value == case.sys_debt - composite
    assert (
        committed.owner_wallet.zusd_balance_atoms.value
        == case.wallet_zusd - case.net_debt
    )
    assert (
        committed.owner_wallet.collateral_balance_atoms.value
        == case.wallet_collateral + case.collateral
    )
    assert (
        committed.system.collateral_atoms.value == case.sys_collateral - case.collateral
    )
    assert committed.gas_reserve.gas_pool_custody_atoms.value == case.gas_pool - RESERVE
    assert committed.system.active_vault_and_index_count.value == case.active_count - 1
    assert result.effects.total_zusd_burn_atoms.value == composite
    assert result.effects.owner_net_debt_burn_atoms.value == case.net_debt
    assert result.effects.gas_reserve_burn_atoms.value == RESERVE


@pytest.mark.parametrize("case_name", REJECTING)
def test_rejected_close_commits_the_unchanged_prestate(case_name: str) -> None:
    """Every rejection is an exact no-op with a nonempty ordered reject vector."""

    case = next(entry for entry in CASES if entry.name == case_name)
    state, request = _build_runtime(case)
    result = run_owner_close(state, request)
    assert type(result) is OwnerCloseRejected
    assert committed_state(result) == state
    ranks = [
        list(OwnerCloseReject).index(reason) for reason in result.violations
    ]
    assert ranks == sorted(set(ranks))


def test_replayed_close_after_acceptance_is_terminal_in_both_layers(
    lean_outcomes: tuple[str, ...],
) -> None:
    """Re-submitting the same authenticated close is a typed no-op in both layers."""

    case = next(entry for entry in CASES if entry.replay_after_close)
    state, request = _build_runtime(case)
    accepted = run_owner_close(state, request)
    assert type(accepted) is OwnerCloseAccepted
    post = committed_state(accepted)

    replay = run_owner_close(post, request)
    assert type(replay) is OwnerCloseRejected
    assert replay.violations == (
        OwnerCloseReject.TARGET_VAULT_INACTIVE,
        OwnerCloseReject.STALE_OWNER_CLOSE_CONTEXT,
    )
    assert committed_state(replay) == post

    model_state, model_request = _project(post, request)
    runtime = _render_runtime_result(replay)
    assert runtime == _oracle_observation(model_state, model_request)
    assert runtime == lean_outcomes[_lean_index(case.name) + 1]


def test_single_price_model_request_cannot_represent_a_split_price() -> None:
    """Named refinement gap: the Lean request holds one price, the runtime two.

    The runtime classifies the candidate TCR with the candidate decision's own
    price and rejects the split binding as stale.  No projection into the Lean
    request can preserve both prices, so the complete reject vector diverges at
    ordinal nine.  This is an abstraction gap, not a runtime value defect: the
    runtime still rejects and commits the prestate.
    """

    case = Case(name="split_price", candidate_price=249 * PRICE_SCALE_E18)
    state, request = _build_runtime(case)

    with pytest.raises(AssertionError):
        _project(state, request)

    result = run_owner_close(state, request)
    assert type(result) is OwnerCloseRejected
    assert result.violations == (
        OwnerCloseReject.POST_CLOSE_TCR_BELOW_CCR,
        OwnerCloseReject.STALE_OWNER_CLOSE_CONTEXT,
    )
    assert committed_state(result) == state

    # The mode price alone classifies the same candidate aggregate as passing,
    # so a single-price model image loses exactly the ordinal-nine failure.
    assert _tcr_at_or_above_ccr(12 * Q, 2_000 * Q, 250 * PRICE_SCALE_E18)
    assert not _tcr_at_or_above_ccr(12 * Q, 2_000 * Q, 249 * PRICE_SCALE_E18)


# Each projection mutant drops one dimension of the abstraction map.  The
# recorded value is the exact set of scenarios whose observation then stops
# matching the Lean model, so a silently widened corpus cannot weaken this gate.
PROJECTION_MUTANTS: dict[str, tuple[str, ...]] = {
    "always_context_current": (
        "reject_stale_route_root",
        "reject_stale_actual_sequence",
        "reject_stale_authority_root",
        "reject_stale_authority_sequence",
        "reject_stale_mode_root",
        "reject_stale_candidate_root",
        "reject_multiple_ordered_failures",
    ),
    "drop_authority_target_conjunct": ("reject_authority_target_drift",),
    "ignore_wallet_owner": (
        "reject_wallet_owner_mismatch",
        "reject_wallet_mismatch_blocks_balance",
        "reject_multiple_ordered_failures",
    ),
    "swap_mode_and_candidate_aggregate": tuple(
        case.name
        for case in CASES
        if not case.name.startswith("reject_stale_")
        and case.name != "reject_multiple_ordered_failures"
    ),
}


@pytest.mark.parametrize("mutant", sorted(PROJECTION_MUTANTS))
def test_projection_mutants_break_the_differential(
    lean_outcomes: tuple[str, ...], mutant: str
) -> None:
    """The differential is sensitive: a wrong abstraction map is detected."""

    divergences: list[str] = []
    for case in CASES:
        state, request = _build_runtime(case)
        model_state, model_request = _project(state, request)
        if mutant == "always_context_current":
            model_request = replace(model_request, context_current=True)
        elif mutant == "drop_authority_target_conjunct":
            lifecycle = state.lifecycle
            assert type(lifecycle) is ActiveWithCompositeDebt
            model_request = replace(
                model_request,
                authority_matches_owner=(
                    request.authority.actor_identity == lifecycle.owner_identity
                ),
            )
        elif mutant == "ignore_wallet_owner":
            model_request = replace(model_request, wallet_matches_owner=True)
        else:
            model_request = replace(
                model_request,
                mode_collateral=model_request.candidate_collateral,
                mode_debt=model_request.candidate_debt,
            )
        mutated = _oracle_observation(model_state, model_request)
        if mutated != lean_outcomes[_lean_index(case.name)]:
            divergences.append(case.name)
    assert tuple(divergences) == PROJECTION_MUTANTS[mutant]


# Each entry removes one blocked-dependent-guard interlock from the model.
# ``elaborates`` records the observed kill layer: three mutants keep the Lean
# acceptance domain and every proof script, so only the executable comparison
# against the runtime's complete reject vector detects them.  The fourth also
# breaks a proof script that case-splits on the wallet branch, so it is killed
# twice over.  ``killers`` pins the exact scenarios that observe the change.
MODEL_MUTANTS = (
    (
        "wrong_owner_guard_not_blocked",
        True,
        ("reject_wrong_request_target", "reject_wrong_target_with_foreign_wallet"),
        "  | .wrongVaultOwner =>\n"
        "      activeDependentPass pre request fun _ => request.authorityMatchesOwner",
        "  | .wrongVaultOwner => request.authorityMatchesOwner",
    ),
    (
        "wallet_guard_not_blocked",
        True,
        ("reject_wrong_target_with_foreign_wallet",),
        "  | .ownerWalletBindingMismatch =>\n"
        "      activeDependentPass pre request fun _ => request.walletMatchesOwner",
        "  | .ownerWalletBindingMismatch => request.walletMatchesOwner",
    ),
    (
        "candidate_guard_not_blocked_by_arithmetic",
        True,
        ("reject_underflow_blocks_inexact_candidate",),
        "        if aggregateUnderflowGuardsPass pre vault ∧\n"
        "            accountingCapacityGuardsPass pre vault then\n"
        "          decide (candidateAggregateIsExact pre request vault)\n"
        "        else\n"
        "          true",
        "        decide (candidateAggregateIsExact pre request vault)",
    ),
    (
        "balance_guard_not_blocked_by_wallet",
        False,
        ("reject_wallet_mismatch_blocks_balance",),
        "        if request.walletMatchesOwner = true then\n"
        "          decide (vault.netDebt.val ≤ pre.ownerZUSDBalance.val)\n"
        "        else\n"
        "          true",
        "        decide (vault.netDebt.val ≤ pre.ownerZUSDBalance.val)",
    ),
)


@pytest.mark.parametrize(("label", "elaborates", "killers", "old", "new"), MODEL_MUTANTS)
def test_model_guard_blocking_mutants_are_killed_by_the_runtime_differential(
    tmp_path: Path,
    label: str,
    elaborates: bool,
    killers: tuple[str, ...],
    old: str,
    new: str,
) -> None:
    """Blocked-guard semantics is load-bearing and executably checked."""

    mutated = _replace_once(_model_source(), old, new)
    probe = _lean_probe(CASES, mutated)
    result = _run_lean(probe, tmp_path / f"ZUSDOwnerCloseMutant_{label}.lean")
    if elaborates:
        assert result.returncode == 0, result.stdout + result.stderr
    else:
        assert result.returncode != 0, f"{label} was expected to break a proof script"
    lines = _outcome_lines(result.stdout)
    assert len(lines) == len(CASES) + sum(
        1 for case in CASES if case.replay_after_close
    ), result.stdout

    divergences = []
    for case in CASES:
        state, request = _build_runtime(case)
        runtime = _render_runtime_result(run_owner_close(state, request))
        if runtime != lines[_lean_index(case.name)]:
            divergences.append(case.name)
    assert tuple(divergences) == killers
