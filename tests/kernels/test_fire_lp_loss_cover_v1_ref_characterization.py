"""Characterization corpus for `src.fire.kernel.fire_lp_loss_cover_v1_ref`.

This corpus was captured against the UNMODIFIED auto-generated reference model
(IR hash below) BEFORE any refactoring, and pins the full observable behavior of:

* ``check_invariants`` -- (ok, first_failed_id) including first-failure ORDER,
* ``step`` -- accept/reject flag, exact error strings, reject-code precedence
  (pre-invariant -> param order -> guard), full post-state, and effects,
* ``replay_trace`` -- multi-step sequences including break-on-reject.

Reachability notes (derived by reading the source, locked by the coverage guard):

* 4 invariant ids can NEVER be the first failure on a real ``State``:
  - ``inv_compiled_lower_is_zero``: ``domain_artifact_lower`` (0..0) fires first
    and already forces ``artifact_lower == 0``.
  - ``inv_holder_solvent_after_accept``: ``holder_delta`` and ``holder_posted``
    domains force both >= 0, so their sum is always >= 0.
  - ``inv_settled_holder_delta_nonnegative``: ``domain_holder_delta`` forces >= 0.
  - ``inv_settled_writer_is_neg_holder``: over the integers it is equivalent to
    ``inv_delta_conservation`` which is checked first.
* ``post-invariant violated: ...`` rejects in ``step`` are unreachable for plain
  states/args: pre-invariants plus the action guards force every post-invariant
  (e.g. payoff <= artifact_upper <= writer_posted_in). The branch is kept as
  fail-closed defense; the corpus asserts it never fires on these inputs.
* The settle guard conjunct ``holder_posted_in >= s.artifact_lower`` cannot be
  violated in isolation: ``artifact_lower`` is domain-pinned to 0 and the param
  domain forces ``holder_posted_in >= 0``.

Regenerate (from the repo root, only after an intentional semantic change):

    PYTHONPATH=. python3 tests/kernels/test_fire_lp_loss_cover_v1_ref_characterization.py --regen

Check without writing:

    PYTHONPATH=. python3 tests/kernels/test_fire_lp_loss_cover_v1_ref_characterization.py
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

from src.fire.kernel import fire_lp_loss_cover_v1_ref as ref
from src.fire.kernel.fire_lp_loss_cover_v1_ref import (
    Command,
    State,
    check_invariants,
    init_state,
    replay_trace,
    step,
)

CORPUS_PATH = Path(__file__).resolve().parent / "fixtures" / "fire_lp_loss_cover_v1_ref_corpus.json"
CORPUS_SCHEMA = "zenodex.fire.lp_loss_cover_v1_ref.characterization_corpus.v1"
IR_HASH = "sha256:bf1509a7c86dfd9cd2d353133de9abf879f2fdf2279c4bd3114636233e8e7be4"

TAG_COMPILE = "compile_lp_loss_cover"
TAG_SETTLE = "firev_accept_and_settle"

STATE_FIELDS = (
    "artifact_lower",
    "artifact_upper",
    "cap_amount",
    "deductible",
    "hodl_lower",
    "hodl_upper",
    "holder_delta",
    "holder_posted",
    "lpv_lower",
    "lpv_upper",
    "n_notional",
    "phase",
    "witness_hodl_final",
    "witness_lpv_final",
    "writer_delta",
    "writer_posted",
)

# Invariant ids exactly as listed in check_invariants, in evaluation order.
ALL_INVARIANT_IDS_IN_CHECK_ORDER = (
    "domain_artifact_lower",
    "domain_artifact_upper",
    "domain_cap_amount",
    "domain_deductible",
    "domain_hodl_lower",
    "domain_hodl_upper",
    "domain_holder_delta",
    "domain_holder_posted",
    "domain_lpv_lower",
    "domain_lpv_upper",
    "domain_n_notional",
    "domain_phase",
    "domain_witness_hodl_final",
    "domain_witness_lpv_final",
    "domain_writer_delta",
    "domain_writer_posted",
    "inv_compiled_lower_is_zero",
    "inv_compiled_upper_matches_bound",
    "inv_delta_conservation",
    "inv_hodl_interval_well_formed",
    "inv_holder_solvent_after_accept",
    "inv_lpv_interval_well_formed",
    "inv_settled_holder_delta_bounded",
    "inv_settled_holder_delta_nonnegative",
    "inv_settled_writer_is_neg_holder",
    "inv_writer_solvent_after_accept",
)

# See module docstring for the per-id unreachability arguments.
UNREACHABLE_INVARIANT_IDS = frozenset(
    {
        "inv_compiled_lower_is_zero",
        "inv_holder_solvent_after_accept",
        "inv_settled_holder_delta_nonnegative",
        "inv_settled_writer_is_neg_holder",
    }
)

REACHABLE_INVARIANT_IDS = frozenset(ALL_INVARIANT_IDS_IN_CHECK_ORDER) - UNREACHABLE_INVARIANT_IDS

COMPILE_PARAM_NAMES = (
    "n_in",
    "deductible_in",
    "cap_in",
    "hodl_lower_in",
    "hodl_upper_in",
    "lpv_lower_in",
    "lpv_upper_in",
)

SETTLE_PARAM_NAMES = (
    "witness_hodl_final_in",
    "witness_lpv_final_in",
    "holder_posted_in",
    "writer_posted_in",
)

# Every reachable fixed-text reject string emitted by step (param + guard rejects).
EXPECTED_EXACT_STEP_ERRORS = frozenset(
    {f"invalid param {name}" for name in COMPILE_PARAM_NAMES}
    | {f"invalid param {name}" for name in SETTLE_PARAM_NAMES}
    | {
        "guard failed for compile_lp_loss_cover",
        "guard failed for firev_accept_and_settle",
    }
)


def _state_payload(**overrides: Any) -> dict[str, Any]:
    """Full 16-field state payload: init_state() with explicit overrides."""
    unknown = set(overrides) - set(STATE_FIELDS)
    if unknown:
        raise ValueError(f"unknown state fields: {sorted(unknown)}")
    payload: dict[str, Any] = dict(asdict(init_state()))
    payload.update(overrides)
    return payload


def _compile_args(**overrides: Any) -> dict[str, Any]:
    args: dict[str, Any] = {
        "n_in": 10,
        "deductible_in": 50,
        "cap_in": 100,
        "hodl_lower_in": 100,
        "hodl_upper_in": 500,
        "lpv_lower_in": 200,
        "lpv_upper_in": 400,
    }
    args.update(overrides)
    return args


def _settle_args(**overrides: Any) -> dict[str, Any]:
    args: dict[str, Any] = {
        "witness_hodl_final_in": 400,
        "witness_lpv_final_in": 300,
        "holder_posted_in": 7,
        "writer_posted_in": 1000,
    }
    args.update(overrides)
    return args


def _drop(args: dict[str, Any], name: str) -> dict[str, Any]:
    out = dict(args)
    del out[name]
    return out


# A consistent Compiled state (the post-state of the typical compile below).
COMPILED_STATE = _state_payload(
    artifact_upper=1000,
    cap_amount=100,
    deductible=50,
    hodl_lower=100,
    hodl_upper=500,
    lpv_lower=200,
    lpv_upper=400,
    n_notional=10,
    phase="Compiled",
)

# A consistent Settled state (the post-state of the uncapped settle below).
SETTLED_STATE = dict(
    COMPILED_STATE,
    holder_delta=500,
    holder_posted=7,
    phase="Settled",
    witness_hodl_final=400,
    witness_lpv_final=300,
    writer_delta=-500,
    writer_posted=1000,
)


def _ci(case_id: str, state: dict[str, Any], comment: str) -> dict[str, Any]:
    return {"case_id": case_id, "kind": "check_invariants", "comment": comment, "state": state}


def _st(case_id: str, state: dict[str, Any], tag: str, args: dict[str, Any], comment: str) -> dict[str, Any]:
    return {
        "case_id": case_id,
        "kind": "step",
        "comment": comment,
        "state": state,
        "command": {"tag": tag, "args": args},
    }


def _rp(case_id: str, commands: list[list[Any]], comment: str) -> dict[str, Any]:
    return {"case_id": case_id, "kind": "replay", "comment": comment, "commands": commands}


def build_cases() -> list[dict[str, Any]]:
    """Deterministic, hand-enumerated case inputs (no randomness)."""
    cases: list[dict[str, Any]] = []

    # ---- check_invariants: valid states -------------------------------------
    cases.append(_ci("ci_init_valid", _state_payload(), "init_state() satisfies all invariants"))
    cases.append(
        _ci(
            "ci_idle_max_bounds_valid",
            _state_payload(
                artifact_upper=1000000,
                cap_amount=1000,
                deductible=1000,
                hodl_lower=1000,
                hodl_upper=1000,
                holder_delta=1000000,
                holder_posted=1000000,
                lpv_lower=1000,
                lpv_upper=1000,
                n_notional=1000,
                witness_hodl_final=1000,
                witness_lpv_final=1000,
                writer_delta=-1000000,
                writer_posted=1000000,
            ),
            "every int field at its domain extreme; Idle makes phase-conditioned invariants vacuous",
        )
    )
    cases.append(
        _ci(
            "ci_idle_inconsistent_artifact_upper_valid",
            _state_payload(artifact_upper=12345),
            "inv_compiled_upper_matches_bound is vacuous while phase == Idle",
        )
    )
    cases.append(
        _ci(
            "ci_idle_nonzero_deltas_valid",
            _state_payload(holder_delta=5, holder_posted=1, writer_delta=-7, writer_posted=2),
            "Settled-only invariants (conservation/solvency) are vacuous while phase == Idle",
        )
    )
    cases.append(_ci("ci_compiled_valid", dict(COMPILED_STATE), "consistent Compiled state"))
    cases.append(_ci("ci_settled_valid", dict(SETTLED_STATE), "consistent Settled state"))
    cases.append(
        _ci(
            "ci_settled_zero_payoff_valid",
            dict(
                COMPILED_STATE,
                phase="Settled",
                witness_hodl_final=300,
                witness_lpv_final=300,
                writer_posted=1000,
            ),
            "Settled with zero deltas (zero payoff) is consistent",
        )
    )

    # ---- check_invariants: each reachable domain id violated singly ----------
    cases.append(_ci("ci_dom_artifact_lower_one", _state_payload(artifact_lower=1), "artifact_lower domain is 0..0"))
    cases.append(
        _ci(
            "ci_dom_artifact_lower_bool_true",
            _state_payload(artifact_lower=True),
            "bool is rejected even though True == 1",
        )
    )
    cases.append(_ci("ci_dom_artifact_upper_negative", _state_payload(artifact_upper=-1), "below 0"))
    cases.append(_ci("ci_dom_artifact_upper_overflow", _state_payload(artifact_upper=1000001), "above 1000000"))
    cases.append(_ci("ci_dom_artifact_upper_str", _state_payload(artifact_upper="1000"), "wrong type str"))
    cases.append(_ci("ci_dom_cap_amount_overflow", _state_payload(cap_amount=1001), "above 1000"))
    cases.append(_ci("ci_dom_deductible_negative", _state_payload(deductible=-1), "below 0"))
    cases.append(_ci("ci_dom_hodl_lower_bool_false", _state_payload(hodl_lower=False), "bool rejected"))
    cases.append(_ci("ci_dom_hodl_upper_float", _state_payload(hodl_upper=1.5), "wrong type float"))
    cases.append(_ci("ci_dom_holder_delta_overflow", _state_payload(holder_delta=1000001), "above 1000000"))
    cases.append(_ci("ci_dom_holder_posted_negative", _state_payload(holder_posted=-5), "below 0"))
    cases.append(_ci("ci_dom_lpv_lower_overflow", _state_payload(lpv_lower=2000), "domain fires before interval check"))
    cases.append(_ci("ci_dom_lpv_upper_negative", _state_payload(lpv_upper=-1), "below 0"))
    cases.append(_ci("ci_dom_n_notional_overflow", _state_payload(n_notional=1001), "above 1000"))
    cases.append(_ci("ci_dom_phase_unknown", _state_payload(phase="Bogus"), "not a PHASE_SYMBOLS member"))
    cases.append(_ci("ci_dom_phase_lowercase", _state_payload(phase="idle"), "phase matching is case-sensitive"))
    cases.append(_ci("ci_dom_phase_int", _state_payload(phase=3), "wrong type int"))
    cases.append(_ci("ci_dom_witness_hodl_final_negative", _state_payload(witness_hodl_final=-2), "below 0"))
    cases.append(_ci("ci_dom_witness_lpv_final_overflow", _state_payload(witness_lpv_final=1001), "above 1000"))
    cases.append(_ci("ci_dom_writer_delta_positive", _state_payload(writer_delta=1), "writer_delta domain is -1000000..0"))
    cases.append(_ci("ci_dom_writer_delta_underflow", _state_payload(writer_delta=-1000001), "below -1000000"))
    cases.append(_ci("ci_dom_writer_posted_str", _state_payload(writer_posted="x"), "wrong type str"))
    cases.append(_ci("ci_dom_writer_posted_none", _state_payload(writer_posted=None), "wrong type None"))

    # ---- check_invariants: each reachable semantic id violated singly --------
    cases.append(
        _ci(
            "ci_inv_compiled_upper_mismatch",
            _state_payload(phase="Compiled", artifact_upper=5),
            "Compiled with artifact_upper != recomputed bound (bound is 0 here)",
        )
    )
    cases.append(
        _ci(
            "ci_inv_compiled_upper_mismatch_settled",
            _state_payload(phase="Settled", artifact_upper=7),
            "inv_compiled_upper_matches_bound also applies in Settled (non-Idle)",
        )
    )
    cases.append(
        _ci(
            "ci_inv_delta_conservation",
            _state_payload(phase="Settled", writer_delta=-3, writer_posted=3),
            "Settled with holder_delta + writer_delta != 0 (only conservation broken)",
        )
    )
    cases.append(
        _ci(
            "ci_inv_hodl_interval",
            _state_payload(hodl_lower=5, hodl_upper=3),
            "hodl interval inverted",
        )
    )
    cases.append(
        _ci(
            "ci_inv_lpv_interval",
            _state_payload(lpv_lower=7, lpv_upper=2),
            "lpv interval inverted",
        )
    )
    cases.append(
        _ci(
            "ci_inv_settled_holder_delta_bounded",
            _state_payload(
                phase="Settled",
                cap_amount=3,
                hodl_upper=10,
                n_notional=1,
                artifact_upper=3,
                holder_delta=5,
                writer_delta=-5,
                writer_posted=10,
            ),
            "holder_delta exceeds artifact_upper while all earlier invariants pass",
        )
    )
    cases.append(
        _ci(
            "ci_inv_writer_solvent",
            _state_payload(
                phase="Settled",
                cap_amount=100,
                hodl_upper=200,
                n_notional=1,
                artifact_upper=100,
                holder_delta=100,
                writer_delta=-100,
                writer_posted=50,
            ),
            "writer_delta + writer_posted < 0 while all earlier invariants pass",
        )
    )

    # ---- check_invariants: multi-fault states pin first-failure order --------
    cases.append(
        _ci(
            "ci_multi_first_domain_field_wins",
            _state_payload(artifact_lower=1, phase="Nope"),
            "artifact_lower is checked before phase",
        )
    )
    cases.append(
        _ci(
            "ci_multi_phase_before_witness",
            _state_payload(phase="Nope", witness_hodl_final=-1),
            "phase is checked before witness_hodl_final",
        )
    )
    cases.append(
        _ci(
            "ci_multi_domain_before_semantic",
            _state_payload(writer_posted="x", hodl_lower=5, hodl_upper=3),
            "all domain checks run before any semantic invariant",
        )
    )
    cases.append(
        _ci(
            "ci_multi_hodl_before_lpv",
            _state_payload(hodl_lower=5, hodl_upper=3, lpv_lower=7, lpv_upper=2),
            "hodl interval is checked before lpv interval",
        )
    )
    cases.append(
        _ci(
            "ci_multi_delta_before_writer_solvency",
            _state_payload(phase="Settled", holder_delta=5, writer_delta=-3),
            "conservation is checked before settled bounds/solvency",
        )
    )
    cases.append(
        _ci(
            "ci_multi_compiled_upper_before_hodl",
            _state_payload(phase="Compiled", artifact_upper=9, hodl_lower=5, hodl_upper=3),
            "compiled-upper invariant is checked before the hodl interval invariant",
        )
    )

    # ---- step: accepted compile commands -------------------------------------
    cases.append(
        _st(
            "st_compile_typical",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(),
            "capped branch: excess 250 >= cap 100 -> artifact_upper = 100 * 10",
        )
    )
    cases.append(
        _st(
            "st_compile_all_zero",
            _state_payload(),
            TAG_COMPILE,
            {name: 0 for name in COMPILE_PARAM_NAMES},
            "all-zero terms compile to artifact_upper 0",
        )
    )
    cases.append(
        _st(
            "st_compile_zero_payoff_below_deductible",
            _state_payload(),
            TAG_COMPILE,
            {
                "n_in": 7,
                "deductible_in": 5,
                "cap_in": 9,
                "hodl_lower_in": 0,
                "hodl_upper_in": 10,
                "lpv_lower_in": 8,
                "lpv_upper_in": 9,
            },
            "hodl_upper 10 < deductible 5 + lpv_lower 8 -> zero branch",
        )
    )
    cases.append(
        _st(
            "st_compile_excess_below_cap",
            _state_payload(),
            TAG_COMPILE,
            {
                "n_in": 3,
                "deductible_in": 0,
                "cap_in": 1000,
                "hodl_lower_in": 0,
                "hodl_upper_in": 100,
                "lpv_lower_in": 0,
                "lpv_upper_in": 50,
            },
            "excess 100 < cap 1000 -> artifact_upper = 100 * 3",
        )
    )
    cases.append(
        _st(
            "st_compile_outer_boundary_excess_zero",
            _state_payload(),
            TAG_COMPILE,
            {
                "n_in": 4,
                "deductible_in": 40,
                "cap_in": 5,
                "hodl_lower_in": 0,
                "hodl_upper_in": 100,
                "lpv_lower_in": 60,
                "lpv_upper_in": 80,
            },
            "hodl_upper == deductible + lpv_lower exactly -> excess 0 below cap",
        )
    )
    cases.append(
        _st(
            "st_compile_excess_equals_cap",
            _state_payload(),
            TAG_COMPILE,
            {
                "n_in": 2,
                "deductible_in": 10,
                "cap_in": 90,
                "hodl_lower_in": 0,
                "hodl_upper_in": 200,
                "lpv_lower_in": 100,
                "lpv_upper_in": 150,
            },
            "excess 90 == cap 90 takes the cap branch",
        )
    )
    cases.append(
        _st(
            "st_compile_max_bounds",
            _state_payload(),
            TAG_COMPILE,
            {
                "n_in": 1000,
                "deductible_in": 0,
                "cap_in": 1000,
                "hodl_lower_in": 0,
                "hodl_upper_in": 1000,
                "lpv_lower_in": 0,
                "lpv_upper_in": 1000,
            },
            "artifact_upper reaches its domain maximum 1000000",
        )
    )
    cases.append(
        _st(
            "st_compile_from_dirty_idle_carries_fields",
            _state_payload(
                holder_delta=11,
                holder_posted=22,
                witness_hodl_final=44,
                witness_lpv_final=55,
                writer_delta=-11,
                writer_posted=33,
            ),
            TAG_COMPILE,
            _compile_args(),
            "compile carries holder/writer/witness fields through unchanged",
        )
    )
    cases.append(
        _st(
            "st_compile_extra_args_ignored",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(extra_junk=999),
            "unknown arg keys are ignored by the parameter validators",
        )
    )

    # ---- step: accepted settle commands ---------------------------------------
    cases.append(
        _st(
            "st_settle_uncapped",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(),
            "excess 50 below cap 100 -> payoff 50 * 10 = 500",
        )
    )
    cases.append(
        _st(
            "st_settle_capped",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_hodl_final_in=500, witness_lpv_final_in=200, holder_posted_in=0),
            "excess 250 >= cap 100 -> payoff equals artifact_upper 1000",
        )
    )
    cases.append(
        _st(
            "st_settle_zero_payoff",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_hodl_final_in=300, witness_lpv_final_in=300, holder_posted_in=0),
            "witness below deductible + lpv -> zero payoff branch",
        )
    )
    cases.append(
        _st(
            "st_settle_witness_at_guard_equalities",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_hodl_final_in=100, witness_lpv_final_in=400, holder_posted_in=0),
            "witnesses exactly on hodl_lower / lpv_upper guard boundaries",
        )
    )
    cases.append(
        _st(
            "st_settle_excess_equals_cap",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_hodl_final_in=500, witness_lpv_final_in=350, holder_posted_in=0),
            "witness excess 100 == cap 100 takes the cap branch",
        )
    )

    # ---- step: compile invalid-param rejects (validation order = source order)
    cases.append(
        _st(
            "st_compile_missing_n_in",
            _state_payload(),
            TAG_COMPILE,
            _drop(_compile_args(), "n_in"),
            "absent key",
        )
    )
    cases.append(_st("st_compile_n_in_str", _state_payload(), TAG_COMPILE, _compile_args(n_in="10"), "wrong type str"))
    cases.append(_st("st_compile_n_in_bool", _state_payload(), TAG_COMPILE, _compile_args(n_in=True), "bool rejected"))
    cases.append(_st("st_compile_n_in_negative", _state_payload(), TAG_COMPILE, _compile_args(n_in=-1), "below 0"))
    cases.append(_st("st_compile_n_in_overflow", _state_payload(), TAG_COMPILE, _compile_args(n_in=1001), "above 1000"))
    cases.append(_st("st_compile_n_in_float", _state_payload(), TAG_COMPILE, _compile_args(n_in=2.5), "wrong type float"))
    cases.append(_st("st_compile_n_in_none", _state_payload(), TAG_COMPILE, _compile_args(n_in=None), "wrong type None"))
    cases.append(
        _st(
            "st_compile_missing_deductible_in",
            _state_payload(),
            TAG_COMPILE,
            _drop(_compile_args(), "deductible_in"),
            "absent key",
        )
    )
    cases.append(
        _st(
            "st_compile_cap_in_bool_false",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(cap_in=False),
            "bool rejected",
        )
    )
    cases.append(
        _st(
            "st_compile_hodl_lower_in_negative",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(hodl_lower_in=-1),
            "below 0",
        )
    )
    cases.append(
        _st(
            "st_compile_hodl_upper_in_overflow",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(hodl_upper_in=1001),
            "above 1000",
        )
    )
    cases.append(
        _st(
            "st_compile_lpv_lower_in_str",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(lpv_lower_in="x"),
            "wrong type str",
        )
    )
    cases.append(
        _st(
            "st_compile_missing_lpv_upper_in",
            _state_payload(),
            TAG_COMPILE,
            _drop(_compile_args(), "lpv_upper_in"),
            "absent key",
        )
    )

    # ---- step: compile guard rejects ------------------------------------------
    cases.append(
        _st(
            "st_compile_guard_hodl_inverted",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(hodl_lower_in=5, hodl_upper_in=3),
            "hodl_lower_in > hodl_upper_in",
        )
    )
    cases.append(
        _st(
            "st_compile_guard_lpv_inverted",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(lpv_lower_in=7, lpv_upper_in=2),
            "lpv_lower_in > lpv_upper_in",
        )
    )
    cases.append(
        _st(
            "st_compile_guard_phase_compiled",
            dict(COMPILED_STATE),
            TAG_COMPILE,
            _compile_args(),
            "compile requires phase == Idle",
        )
    )
    cases.append(
        _st(
            "st_compile_guard_phase_settled",
            dict(SETTLED_STATE),
            TAG_COMPILE,
            _compile_args(),
            "compile requires phase == Idle",
        )
    )

    # ---- step: settle invalid-param rejects ------------------------------------
    cases.append(
        _st(
            "st_settle_missing_witness_hodl_final_in",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _drop(_settle_args(), "witness_hodl_final_in"),
            "absent key",
        )
    )
    cases.append(
        _st(
            "st_settle_witness_lpv_final_in_overflow",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_lpv_final_in=1001),
            "above 1000",
        )
    )
    cases.append(
        _st(
            "st_settle_holder_posted_in_str",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(holder_posted_in="p"),
            "wrong type str",
        )
    )
    cases.append(
        _st(
            "st_settle_writer_posted_in_negative",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(writer_posted_in=-3),
            "below 0",
        )
    )
    cases.append(
        _st(
            "st_settle_writer_posted_in_overflow",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(writer_posted_in=1000001),
            "above 1000000",
        )
    )

    # ---- step: settle guard rejects (one conjunct at a time where possible) ----
    cases.append(
        _st(
            "st_settle_guard_witness_hodl_above_upper",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_hodl_final_in=501),
            "witness_hodl_final_in > hodl_upper",
        )
    )
    cases.append(
        _st(
            "st_settle_guard_witness_lpv_above_upper",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_lpv_final_in=401),
            "witness_lpv_final_in > lpv_upper",
        )
    )
    cases.append(
        _st(
            "st_settle_guard_witness_hodl_below_lower",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_hodl_final_in=99),
            "witness_hodl_final_in < hodl_lower",
        )
    )
    cases.append(
        _st(
            "st_settle_guard_witness_lpv_below_lower",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_lpv_final_in=199),
            "witness_lpv_final_in < lpv_lower",
        )
    )
    cases.append(
        _st(
            "st_settle_guard_phase_idle",
            _state_payload(),
            TAG_SETTLE,
            {
                "witness_hodl_final_in": 0,
                "witness_lpv_final_in": 0,
                "holder_posted_in": 0,
                "writer_posted_in": 0,
            },
            "all other conjuncts hold on init state; only phase != Compiled fails",
        )
    )
    cases.append(
        _st(
            "st_settle_guard_phase_settled",
            dict(SETTLED_STATE),
            TAG_SETTLE,
            _settle_args(holder_posted_in=0),
            "settle requires phase == Compiled",
        )
    )
    cases.append(
        _st(
            "st_settle_guard_writer_posted_below_artifact_upper",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(holder_posted_in=0, writer_posted_in=999),
            "writer_posted_in 999 < artifact_upper 1000",
        )
    )

    # ---- step: unknown action ----------------------------------------------------
    cases.append(
        _st(
            "st_unknown_action",
            _state_payload(),
            "mint_pool",
            {},
            "tag dispatch falls through to the unknown-action reject",
        )
    )
    cases.append(
        _st(
            "st_unknown_action_empty_tag",
            _state_payload(),
            "",
            {"n_in": 1},
            "empty tag is still an unknown action",
        )
    )

    # ---- step: pre-invariant rejects ----------------------------------------------
    cases.append(
        _st(
            "st_pre_invariant_domain_phase",
            _state_payload(phase="Broken"),
            TAG_COMPILE,
            _compile_args(),
            "pre-state invariants are checked before anything else",
        )
    )
    cases.append(
        _st(
            "st_pre_invariant_domain_writer_delta",
            _state_payload(writer_delta=7),
            TAG_SETTLE,
            _settle_args(),
            "pre-state domain violation rejects the settle command",
        )
    )
    cases.append(
        _st(
            "st_pre_invariant_semantic_hodl_interval",
            _state_payload(hodl_lower=5),
            TAG_COMPILE,
            _compile_args(),
            "pre-state semantic violation (hodl 5 > 0) rejects before param checks",
        )
    )

    # ---- step: reject-precedence probes (>= 4 multi-fault inputs) -------------------
    cases.append(
        _st(
            "st_prec_pre_before_params",
            _state_payload(phase="Broken"),
            TAG_COMPILE,
            _drop(_compile_args(), "n_in"),
            "pre-invariant reject wins over invalid params",
        )
    )
    cases.append(
        _st(
            "st_prec_pre_before_unknown_tag",
            _state_payload(phase="Broken"),
            "bogus_action",
            {},
            "pre-invariant reject wins over unknown-action (pre-check precedes dispatch)",
        )
    )
    cases.append(
        _st(
            "st_prec_param_n_before_deductible",
            _state_payload(),
            TAG_COMPILE,
            _drop(_compile_args(deductible_in="x"), "n_in"),
            "n_in is validated before deductible_in",
        )
    )
    cases.append(
        _st(
            "st_prec_param_deductible_before_cap",
            _state_payload(),
            TAG_COMPILE,
            _drop(_compile_args(deductible_in=True), "cap_in"),
            "deductible_in is validated before cap_in",
        )
    )
    cases.append(
        _st(
            "st_prec_param_hodl_upper_before_lpv_lower",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(hodl_upper_in=-5, lpv_lower_in="z"),
            "hodl_upper_in is validated before lpv_lower_in",
        )
    )
    cases.append(
        _st(
            "st_prec_params_before_guard",
            _state_payload(),
            TAG_COMPILE,
            _compile_args(hodl_lower_in=5, hodl_upper_in=3, lpv_upper_in=2000),
            "param rejects win over guard violations",
        )
    )
    cases.append(
        _st(
            "st_prec_settle_param_order",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _drop(_settle_args(writer_posted_in="x"), "witness_hodl_final_in"),
            "witness_hodl_final_in is validated before writer_posted_in",
        )
    )
    cases.append(
        _st(
            "st_prec_settle_params_before_guard",
            _state_payload(),
            TAG_SETTLE,
            {
                "witness_hodl_final_in": 0,
                "witness_lpv_final_in": -1,
                "holder_posted_in": 0,
                "writer_posted_in": 0,
            },
            "invalid witness_lpv_final_in wins over the failing phase guard",
        )
    )
    cases.append(
        _st(
            "st_prec_settle_multi_guard_single_message",
            dict(COMPILED_STATE),
            TAG_SETTLE,
            _settle_args(witness_hodl_final_in=501, writer_posted_in=999),
            "multiple broken guard conjuncts still produce the single guard message",
        )
    )

    # ---- replay traces ---------------------------------------------------------------
    cases.append(
        _rp(
            "rp_full_lifecycle",
            [[TAG_COMPILE, _compile_args()], [TAG_SETTLE, _settle_args()]],
            "Idle -> Compiled -> Settled happy path",
        )
    )
    cases.append(
        _rp(
            "rp_compile_twice",
            [[TAG_COMPILE, _compile_args()], [TAG_COMPILE, _compile_args()]],
            "second compile fails the Idle-phase guard; replay stops",
        )
    )
    cases.append(
        _rp(
            "rp_settle_first",
            [
                [
                    TAG_SETTLE,
                    {
                        "witness_hodl_final_in": 0,
                        "witness_lpv_final_in": 0,
                        "holder_posted_in": 0,
                        "writer_posted_in": 0,
                    },
                ]
            ],
            "settle from init fails the Compiled-phase guard",
        )
    )
    cases.append(
        _rp(
            "rp_full_then_compile_again",
            [
                [TAG_COMPILE, _compile_args()],
                [TAG_SETTLE, _settle_args()],
                [TAG_COMPILE, _compile_args()],
            ],
            "compile after settlement fails the Idle-phase guard",
        )
    )
    cases.append(
        _rp(
            "rp_max_lifecycle",
            [
                [
                    TAG_COMPILE,
                    {
                        "n_in": 1000,
                        "deductible_in": 0,
                        "cap_in": 1000,
                        "hodl_lower_in": 0,
                        "hodl_upper_in": 1000,
                        "lpv_lower_in": 0,
                        "lpv_upper_in": 1000,
                    },
                ],
                [
                    TAG_SETTLE,
                    {
                        "witness_hodl_final_in": 1000,
                        "witness_lpv_final_in": 0,
                        "holder_posted_in": 1000000,
                        "writer_posted_in": 1000000,
                    },
                ],
            ],
            "extreme-bounds lifecycle: payoff and deltas reach the domain extremes",
        )
    )
    cases.append(
        _rp(
            "rp_zero_notional_lifecycle",
            [
                [TAG_COMPILE, {name: 0 for name in COMPILE_PARAM_NAMES}],
                [
                    TAG_SETTLE,
                    {
                        "witness_hodl_final_in": 0,
                        "witness_lpv_final_in": 0,
                        "holder_posted_in": 0,
                        "writer_posted_in": 0,
                    },
                ],
            ],
            "degenerate all-zero lifecycle settles with zero payoff",
        )
    )
    cases.append(
        _rp(
            "rp_break_on_invalid_param",
            [
                [TAG_COMPILE, _compile_args()],
                [TAG_SETTLE, _drop(_settle_args(), "witness_lpv_final_in")],
            ],
            "replay records the param reject and stops",
        )
    )
    cases.append(
        _rp(
            "rp_unknown_tag_only",
            [["not_an_action", {}]],
            "unknown tag is recorded and replay stops",
        )
    )
    cases.append(_rp("rp_empty", [], "empty trace produces no results"))

    case_ids = [case["case_id"] for case in cases]
    if len(set(case_ids)) != len(case_ids):
        raise ValueError("duplicate case ids in corpus builder")
    return cases


def _step_result_payload(result: Any) -> dict[str, Any]:
    return {
        "ok": result.ok,
        "error": result.error,
        "state": asdict(result.state) if result.state is not None else None,
        "effects": dict(result.effects) if result.effects is not None else None,
    }


def _evaluate_case(case: dict[str, Any]) -> dict[str, Any]:
    kind = case["kind"]
    if kind == "check_invariants":
        ok, failed = check_invariants(State(**case["state"]))
        return {"ok": ok, "failed": failed}
    if kind == "step":
        result = step(
            State(**case["state"]),
            Command(tag=case["command"]["tag"], args=case["command"]["args"]),
        )
        return _step_result_payload(result)
    if kind == "replay":
        results = replay_trace([(tag, args) for tag, args in case["commands"]])
        return {"results": [_step_result_payload(result) for result in results]}
    raise ValueError(f"unknown corpus case kind: {kind}")


def build_corpus() -> dict[str, Any]:
    entries = []
    for case in build_cases():
        entry = dict(case)
        entry["expect"] = _evaluate_case(case)
        entries.append(entry)
    return {
        "schema": CORPUS_SCHEMA,
        "ir_hash": IR_HASH,
        "case_count": len(entries),
        "cases": entries,
    }


def render_corpus(corpus: dict[str, Any]) -> str:
    return json.dumps(corpus, indent=2, sort_keys=True) + "\n"


def _load_corpus() -> dict[str, Any]:
    assert CORPUS_PATH.exists(), (
        f"missing corpus {CORPUS_PATH}; regenerate with: "
        "PYTHONPATH=. python3 tests/kernels/test_fire_lp_loss_cover_v1_ref_characterization.py --regen"
    )
    return json.loads(CORPUS_PATH.read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_ir_hash_is_pinned_to_module() -> None:
    """The corpus is only valid for the exact generated model it was captured from."""
    assert IR_HASH in (ref.__doc__ or ""), "ref model IR hash changed; corpus must be re-reviewed"


def test_corpus_regeneration_is_byte_identical() -> None:
    """Regenerating the corpus from live code reproduces the committed file exactly."""
    corpus = _load_corpus()
    assert render_corpus(build_corpus()) == CORPUS_PATH.read_text(encoding="utf-8")
    assert corpus["schema"] == CORPUS_SCHEMA
    assert corpus["ir_hash"] == IR_HASH
    assert corpus["case_count"] == len(corpus["cases"])


def test_every_corpus_case_reproduces_exactly() -> None:
    """Each pinned input still produces the byte-identical pinned output."""
    corpus = _load_corpus()
    assert corpus["cases"], "corpus must not be empty"
    for entry in corpus["cases"]:
        observed = _evaluate_case(entry)
        observed_text = json.dumps(observed, sort_keys=True)
        expected_text = json.dumps(entry["expect"], sort_keys=True)
        assert observed_text == expected_text, (
            f"case {entry['case_id']} diverged:\n  expected: {expected_text}\n  observed: {observed_text}"
        )


def test_step_rejects_are_noop_with_no_state_or_effects() -> None:
    """Rejects return ok=False with state=None/effects=None and never mutate the input."""
    corpus = _load_corpus()
    rejects = 0
    accepts = 0
    for entry in corpus["cases"]:
        if entry["kind"] != "step":
            continue
        pre_state = State(**entry["state"])
        snapshot = State(**entry["state"])
        result = step(pre_state, Command(tag=entry["command"]["tag"], args=entry["command"]["args"]))
        if result.ok:
            accepts += 1
            assert result.state is not None
            assert result.effects is not None
            assert result.error is None
        else:
            rejects += 1
            assert result.state is None, f"reject leaked a state in {entry['case_id']}"
            assert result.effects is None, f"reject leaked effects in {entry['case_id']}"
            assert isinstance(result.error, str) and result.error
        assert pre_state == snapshot, f"step mutated its input state in {entry['case_id']}"
    assert accepts >= 10
    assert rejects >= 25


def test_coverage_guard_every_reachable_code_is_pinned() -> None:
    """The corpus covers every reachable reject code and invariant id (and only those)."""
    corpus = _load_corpus()
    step_errors: set[str] = set()
    accepted_tags: set[str] = set()
    invariant_failures: set[str] = set()
    multi_fault_step = 0
    multi_fault_ci = 0
    lifecycle_replays = 0

    for entry in corpus["cases"]:
        kind = entry["kind"]
        if kind == "check_invariants":
            if entry["case_id"].startswith("ci_multi_"):
                multi_fault_ci += 1
            failed = entry["expect"]["failed"]
            if failed is not None:
                invariant_failures.add(failed)
            continue
        if kind == "step":
            if entry["case_id"].startswith("st_prec_"):
                multi_fault_step += 1
            results = [(entry["command"]["tag"], entry["expect"])]
        else:
            results = list(zip((tag for tag, _ in entry["commands"]), entry["expect"]["results"]))
            if len(entry["expect"]["results"]) >= 2 and all(r["ok"] for r in entry["expect"]["results"]):
                lifecycle_replays += 1
        for tag, result in results:
            if result["ok"]:
                accepted_tags.add(tag)
            else:
                step_errors.add(result["error"])

    # Both actions are exercised on their accept paths.
    assert accepted_tags == {TAG_COMPILE, TAG_SETTLE}
    assert lifecycle_replays >= 1, "need at least one fully-accepted multi-step replay"

    # Every fixed-text reject string appears verbatim.
    missing = EXPECTED_EXACT_STEP_ERRORS - step_errors
    assert not missing, f"corpus never produced: {sorted(missing)}"

    # Parameterized reject families appear.
    assert any(err.startswith("unknown action: ") for err in step_errors)
    pre_invariant_ids = {
        err[len("pre-invariant violated: "):]
        for err in step_errors
        if err.startswith("pre-invariant violated: ")
    }
    assert pre_invariant_ids, "corpus never produced a pre-invariant reject"

    # post-invariant rejects are unreachable for plain inputs (see module docstring);
    # the corpus locks that analysis by never containing one.
    assert not any(err.startswith("post-invariant violated") for err in step_errors)

    # Invariant-id coverage: exactly the reachable set, never the unreachable set.
    covered = invariant_failures | pre_invariant_ids
    assert covered.issuperset(REACHABLE_INVARIANT_IDS), (
        f"missing invariant ids: {sorted(REACHABLE_INVARIANT_IDS - covered)}"
    )
    assert not covered & UNREACHABLE_INVARIANT_IDS, (
        f"supposedly-unreachable invariant ids fired: {sorted(covered & UNREACHABLE_INVARIANT_IDS)}"
    )
    assert set(ALL_INVARIANT_IDS_IN_CHECK_ORDER) == (REACHABLE_INVARIANT_IDS | UNREACHABLE_INVARIANT_IDS)
    assert len(ALL_INVARIANT_IDS_IN_CHECK_ORDER) == 26

    # Reject-code precedence is pinned by dedicated multi-fault probes.
    assert multi_fault_step >= 4
    assert multi_fault_ci >= 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--regen",
        action="store_true",
        help="rewrite the committed corpus JSON from the live reference model",
    )
    args = parser.parse_args(argv)
    rendered = render_corpus(build_corpus())
    if args.regen:
        CORPUS_PATH.parent.mkdir(parents=True, exist_ok=True)
        CORPUS_PATH.write_text(rendered, encoding="utf-8")
        print(f"wrote {CORPUS_PATH}", file=sys.stderr)
        return 0
    if not CORPUS_PATH.exists():
        print(f"missing corpus: {CORPUS_PATH} (use --regen)", file=sys.stderr)
        return 1
    if CORPUS_PATH.read_text(encoding="utf-8") != rendered:
        print("corpus is STALE relative to the live model", file=sys.stderr)
        return 1
    print("corpus is up to date", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
