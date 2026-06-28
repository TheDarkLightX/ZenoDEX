#!/usr/bin/env python3
"""Sample and evaluate deterministic autonomous-governance Q policies."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.autonomous_governance_ebrm_evidence import (  # noqa: E402
    build_autonomous_governance_ebrm_corpus_v1,
    build_autonomous_governance_ebrm_evidence_report_v1,
    build_autonomous_governance_ebrm_training_report_v1,
)
from src.integration.autonomous_governance_ebrm_policy import (  # noqa: E402
    ebrm_policy_content_hash_v1,
    evaluate_autonomous_governance_ebrm_policy_step_v1,
    sample_autonomous_governance_ebrm_policy_v1,
)
from src.integration.autonomous_governance_live_apply import (  # noqa: E402
    admit_autonomous_governance_live_session_file_update_v1,
    autonomous_governance_live_session_file_context_hash_v1,
)
from src.integration.autonomous_governance_q_policy import (  # noqa: E402
    commit_autonomous_governance_surface_q_policy_v1,
    evaluate_autonomous_governance_q_policy_v1,
    evaluate_autonomous_governance_surface_q_policy_v1,
    governance_surface_context_hash_v1,
    sample_autonomous_governance_q_policy_v1,
    sample_autonomous_governance_surface_q_policy_v1,
)
from src.integration.autonomous_governance_session import (  # noqa: E402
    continue_autonomous_governance_surface_trajectory_v1,
    verify_autonomous_governance_surface_session_v1,
)
from src.integration.autonomous_governance_session_store import (  # noqa: E402
    admit_autonomous_governance_session_continuation_v1,
    current_session_store_head_v1,
    initialize_autonomous_governance_session_store_v1,
    verify_autonomous_governance_session_store_v1,
)
from src.integration.autonomous_governance_session_store_file import (  # noqa: E402
    admit_autonomous_governance_session_file_continuation_v1,
    current_session_store_file_head_v1,
    initialize_autonomous_governance_session_store_file_v1,
    verify_autonomous_governance_session_store_file_v1,
)
from src.integration.autonomous_governance_trajectory import (  # noqa: E402
    admit_verified_autonomous_governance_surface_trajectory_v1,
    run_autonomous_governance_surface_trajectory_v1,
    verify_autonomous_governance_surface_trajectory_v1,
)

MAX_INPUT_BYTES = 500_000


def _sample_bundle() -> dict[str, Any]:
    policy = sample_autonomous_governance_q_policy_v1()
    return {
        "schema": "zenodex.autonomous_governance.q_policy_eval_bundle.v1",
        "policy": policy,
        "expected_policy_hash": policy["policy_hash"],
        "parameters": {
            "fee": {"current": 30, "minimum": 0, "maximum": 100, "step": 10},
            "buyback": {"current": 20, "minimum": 0, "maximum": 100, "step": 10},
            "rebate": {"current": 10, "minimum": 0, "maximum": 100, "step": 10},
            "floor": {"current": 100_000, "minimum": 0, "maximum": 1_000_000, "step": 1_000},
            "unit": {"current": 10_000, "minimum": 1, "maximum": 10_000, "step": 0},
            "tier1": {"current": 30, "minimum": 1, "maximum": 365, "step": 10},
            "tier2": {"current": 90, "minimum": 2, "maximum": 730, "step": 10},
            "weight1": {"current": 100, "minimum": 0, "maximum": 1_000, "step": 25},
            "weight2": {"current": 200, "minimum": 0, "maximum": 1_000, "step": 25},
            "weight3": {"current": 300, "minimum": 0, "maximum": 1_000, "step": 25},
        },
        "observation": {
            "observed_price_bps": 10_500,
            "target_price_bps": 10_000,
            "volatility_bps": 250,
            "divergence_bps": 10,
            "freshness_lag_epochs": 0,
            "liquidity_depth_bps": 5_000,
        },
        "current_epoch": 12,
        "proposal_epoch": 10,
        "min_delay_epochs": 1,
        "last_update_epoch": 10,
    }


def _sample_surface_bundle() -> dict[str, Any]:
    policy = sample_autonomous_governance_surface_q_policy_v1()
    surface_state = {
        "fee_bps": 30,
        "buyburn_bps": 6_000,
        "stakers_bps": 0,
        "reserve_bps": 2_000,
        "hosts_bps": 2_000,
        "mcr_bps": 11_000,
        "ccr_bps": 15_000,
        "staker_bps": 5_000,
        "funding_cap_bps": 120,
    }
    current_epoch = 34
    proposal_epoch = 10
    last_update_epoch = 32
    return {
        "schema": "zenodex.autonomous_governance.q_surface_policy_eval_bundle.v1",
        "policy": policy,
        "expected_policy_hash": policy["policy_hash"],
        "expected_committed_context_hash": governance_surface_context_hash_v1(
            surface_state=surface_state,
            current_epoch=current_epoch,
            proposal_epoch=proposal_epoch,
            last_update_epoch=last_update_epoch,
        ),
        "surface_state": surface_state,
        "observation": {
            "observed_price_bps": 10_500,
            "target_price_bps": 10_000,
            "volatility_bps": 250,
            "divergence_bps": 10,
            "freshness_lag_epochs": 0,
            "liquidity_depth_bps": 5_000,
        },
        "current_epoch": current_epoch,
        "proposal_epoch": proposal_epoch,
        "last_update_epoch": last_update_epoch,
    }


def _sample_trajectory_bundle() -> dict[str, Any]:
    surface = _sample_surface_bundle()
    policy = surface["policy"]

    def step(observation: dict[str, Any], current_epoch: int) -> dict[str, Any]:
        return {
            "observation": observation,
            "current_epoch": current_epoch,
            "proposal_epoch": current_epoch - 24,
        }

    hot = dict(surface["observation"])
    calm = {**hot, "observed_price_bps": 10_000, "volatility_bps": 25, "divergence_bps": 5}
    return {
        "schema": "zenodex.autonomous_governance.q_surface_trajectory_bundle.v1",
        "policy": policy,
        "expected_policy_hash": surface["expected_policy_hash"],
        "initial_surface_state": dict(surface["surface_state"]),
        "steps": [step(hot, 100), step(calm, 125), step(hot, 150)],
        "trajectory_budget": {
            "fee_bps": 50,
            "funding_cap_bps": 25,
            "buyburn_bps": 200,
            "reserve_bps": 200,
        },
    }


def _sample_ebrm_bundle() -> dict[str, Any]:
    policy = sample_autonomous_governance_ebrm_policy_v1()
    surface_state = {
        "fee_bps": 30,
        "buyburn_bps": 6_000,
        "stakers_bps": 0,
        "reserve_bps": 2_000,
        "hosts_bps": 2_000,
        "mcr_bps": 11_000,
        "ccr_bps": 15_000,
        "staker_bps": 5_000,
        "funding_cap_bps": 120,
    }
    current_epoch = 34
    proposal_epoch = 10
    return {
        "schema": "zenodex.autonomous_governance.ebrm_policy_eval_bundle.v1",
        "policy": policy,
        "expected_policy_hash": ebrm_policy_content_hash_v1(policy),
        "expected_committed_context_hash": governance_surface_context_hash_v1(
            surface_state=surface_state,
            current_epoch=current_epoch,
            proposal_epoch=proposal_epoch,
        ),
        "committed_surface_state": surface_state,
        "observation": {
            "observed_price_bps": 10_500,
            "target_price_bps": 10_000,
            "deviation_bps": 500,
            "volatility_bps": 250,
            "divergence_bps": 10,
            "freshness_lag_epochs": 0,
            "liquidity_depth_bps": 5_000,
        },
        "approved": True,
        "current_epoch": current_epoch,
        "proposal_epoch": proposal_epoch,
    }


def _load_json(path: Path) -> dict[str, Any]:
    if path.stat().st_size > MAX_INPUT_BYTES:
        raise ValueError(f"input_file_too_large:{path.stat().st_size}>{MAX_INPUT_BYTES}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("input_must_be_json_object")
    return data


def _cmd_sample(args: argparse.Namespace) -> int:
    selected = sum(bool(value) for value in (args.surface, args.trajectory, args.ebrm))
    if selected > 1:
        sys.stderr.write("choose at most one of --surface / --trajectory / --ebrm\n")
        return 3
    if args.ebrm:
        bundle = _sample_ebrm_bundle()
    elif args.trajectory:
        bundle = _sample_trajectory_bundle()
    elif args.surface:
        bundle = _sample_surface_bundle()
    else:
        bundle = _sample_bundle()
    text = json.dumps(bundle, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def _cmd_evaluate(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "surface_state" in bundle:
            result = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=bundle.get("policy", {}),
                surface_state=bundle.get("surface_state", {}),
                observation=bundle.get("observation", {}),
                current_epoch=bundle.get("current_epoch"),
                proposal_epoch=bundle.get("proposal_epoch"),
                last_update_epoch=bundle.get("last_update_epoch"),
                expected_policy_hash=bundle.get("expected_policy_hash"),
                expected_committed_context_hash=bundle.get("expected_committed_context_hash"),
            )
        else:
            result = evaluate_autonomous_governance_q_policy_v1(
                policy=bundle.get("policy", {}),
                parameters=bundle.get("parameters", {}),
                observation=bundle.get("observation", {}),
                current_epoch=bundle.get("current_epoch"),
                proposal_epoch=bundle.get("proposal_epoch"),
                min_delay_epochs=bundle.get("min_delay_epochs"),
                last_update_epoch=bundle.get("last_update_epoch"),
                expected_policy_hash=bundle.get("expected_policy_hash"),
            )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"evaluate_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_step(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "surface_state" not in bundle:
            raise ValueError("step_requires_governance_surface_bundle")
        result = commit_autonomous_governance_surface_q_policy_v1(
            policy=bundle.get("policy", {}),
            surface_state=bundle.get("surface_state", {}),
            observation=bundle.get("observation", {}),
            current_epoch=bundle.get("current_epoch"),
            proposal_epoch=bundle.get("proposal_epoch"),
            last_update_epoch=bundle.get("last_update_epoch"),
            expected_policy_hash=bundle.get("expected_policy_hash"),
            expected_committed_context_hash=bundle.get("expected_committed_context_hash"),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"step_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_ebrm_step(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        result = evaluate_autonomous_governance_ebrm_policy_step_v1(
            policy=bundle.get("policy", {}),
            committed_surface_state=bundle.get(
                "committed_surface_state", bundle.get("surface_state", {})
            ),
            observation=bundle.get("observation", {}),
            approved=bundle.get("approved"),
            current_epoch=bundle.get("current_epoch"),
            proposal_epoch=bundle.get("proposal_epoch"),
            last_update_epoch=bundle.get("last_update_epoch"),
            expected_policy_hash=bundle.get("expected_policy_hash"),
            expected_committed_context_hash=bundle.get("expected_committed_context_hash"),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"ebrm_step_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _write_json_output(data: dict[str, Any], output: str | None) -> None:
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if output:
        Path(output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)


def _cmd_ebrm_evidence(args: argparse.Namespace) -> int:
    try:
        report = build_autonomous_governance_ebrm_evidence_report_v1(
            include_corpus=bool(args.include_corpus)
        )
        if args.corpus_output:
            corpus = build_autonomous_governance_ebrm_corpus_v1()
            Path(args.corpus_output).write_text(
                json.dumps(corpus, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"ebrm_evidence_failed:{exc}"],
        }
        _write_json_output(result, args.output)
        return 3

    _write_json_output(report, args.output)
    return 0 if report.get("ok") is True else 2


def _cmd_ebrm_train(args: argparse.Namespace) -> int:
    try:
        report = build_autonomous_governance_ebrm_training_report_v1(
            include_corpus=bool(args.include_corpus)
        )
        if args.model_output:
            model = report.get("trained_model")
            if not isinstance(model, dict):
                raise ValueError("ebrm_training_report_missing_trained_model")
            Path(args.model_output).write_text(
                json.dumps(model, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"ebrm_train_failed:{exc}"],
        }
        _write_json_output(result, args.output)
        return 3

    _write_json_output(report, args.output)
    return 0 if report.get("ok") is True else 2


def _cmd_trajectory(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        result = run_autonomous_governance_surface_trajectory_v1(
            policy=bundle.get("policy", {}),
            initial_surface_state=bundle.get("initial_surface_state", {}),
            steps=bundle.get("steps", []),
            expected_policy_hash=bundle.get("expected_policy_hash", ""),
            last_update_epoch=bundle.get("last_update_epoch"),
            trajectory_budget=bundle.get("trajectory_budget"),
            trajectory_used=bundle.get("trajectory_used"),
            previous_approved_deltas=bundle.get("previous_approved_deltas"),
            previous_chain_head=bundle.get("previous_chain_head"),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"trajectory_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_continue_trajectory(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "previous_receipt" not in bundle or "policy" not in bundle:
            raise ValueError("continue_trajectory_requires_policy_and_previous_receipt")
        result = continue_autonomous_governance_surface_trajectory_v1(
            policy=bundle.get("policy", {}),
            previous_receipt=bundle.get("previous_receipt", {}),
            steps=bundle.get("steps", []),
            expected_policy_hash=bundle.get("expected_policy_hash", ""),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"continue_trajectory_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_verify_trajectory(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "trajectory_receipt" not in bundle or "policy" not in bundle:
            raise ValueError("verify_trajectory_requires_policy_and_trajectory_receipt")
        result = verify_autonomous_governance_surface_trajectory_v1(
            receipt=bundle.get("trajectory_receipt", {}),
            policy=bundle.get("policy", {}),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"verify_trajectory_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_admit_trajectory(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "trajectory_receipt" not in bundle or "policy" not in bundle:
            raise ValueError("admit_trajectory_requires_policy_and_trajectory_receipt")
        result = admit_verified_autonomous_governance_surface_trajectory_v1(
            receipt=bundle.get("trajectory_receipt", {}),
            policy=bundle.get("policy", {}),
            expected_policy_hash=bundle.get("expected_policy_hash", ""),
            expected_initial_state=bundle.get("expected_initial_state"),
            expected_final_state=bundle.get("expected_final_state"),
            expected_previous_chain_head=bundle.get("expected_previous_chain_head"),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"admit_trajectory_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("accepted") is True else 2


def _cmd_verify_session(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "policy" not in bundle:
            raise ValueError("verify_session_requires_policy")
        receipts = bundle.get("trajectory_receipts", bundle.get("receipts"))
        result = verify_autonomous_governance_surface_session_v1(
            receipts=receipts,
            policy=bundle.get("policy", {}),
            expected_policy_hash=bundle.get("expected_policy_hash"),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"verify_session_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_init_session_store(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "policy" not in bundle:
            raise ValueError("init_session_store_requires_policy")
        result = initialize_autonomous_governance_session_store_v1(
            genesis_pin=bundle.get("genesis_pin", {}),
            genesis_receipt=bundle.get("genesis_receipt", {}),
            policy=bundle.get("policy", {}),
            policy_pin=bundle.get("policy_pin"),
            registry=bundle.get("registry"),
            signature_envelopes=bundle.get("signature_envelopes"),
            current_epoch=bundle.get("current_epoch"),
            proposal_epoch=bundle.get("proposal_epoch"),
            min_delay_epochs=bundle.get("min_delay_epochs"),
            tau_policy_receipt=bundle.get("tau_policy_receipt"),
            backend_descriptors=bundle.get("backend_descriptors"),
            evidence_claims=bundle.get("evidence_claims", ()),
            required_evidence_claims=bundle.get("required_evidence_claims", ()),
            production_mode=bool(bundle.get("production_mode", True)),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"init_session_store_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_admit_session_continuation(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "policy" not in bundle:
            raise ValueError("admit_session_continuation_requires_policy")
        receipt = bundle.get("trajectory_receipt", bundle.get("receipt", {}))
        result = admit_autonomous_governance_session_continuation_v1(
            store=bundle.get("store", {}),
            receipt=receipt,
            policy=bundle.get("policy", {}),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"admit_session_continuation_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("admitted") is True else 2


def _cmd_verify_session_store(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "policy" not in bundle:
            raise ValueError("verify_session_store_requires_policy")
        result = verify_autonomous_governance_session_store_v1(
            store=bundle.get("store", {}),
            policy=bundle.get("policy", {}),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"verify_session_store_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_session_store_head(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        result = current_session_store_head_v1(bundle.get("store", bundle))
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"session_store_head_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _store_file_path_from_bundle(bundle: dict[str, Any], *, command: str) -> str:
    value = bundle.get("path", bundle.get("store_path"))
    if not isinstance(value, str) or not value:
        raise ValueError(f"{command}_requires_path")
    return value


def _cmd_init_session_store_file(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "policy" not in bundle:
            raise ValueError("init_session_store_file_requires_policy")
        result = initialize_autonomous_governance_session_store_file_v1(
            path=_store_file_path_from_bundle(bundle, command="init_session_store_file"),
            genesis_pin=bundle.get("genesis_pin", {}),
            genesis_receipt=bundle.get("genesis_receipt", {}),
            policy=bundle.get("policy", {}),
            policy_pin=bundle.get("policy_pin"),
            registry=bundle.get("registry"),
            signature_envelopes=bundle.get("signature_envelopes"),
            current_epoch=bundle.get("current_epoch"),
            proposal_epoch=bundle.get("proposal_epoch"),
            min_delay_epochs=bundle.get("min_delay_epochs"),
            tau_policy_receipt=bundle.get("tau_policy_receipt"),
            backend_descriptors=bundle.get("backend_descriptors"),
            evidence_claims=bundle.get("evidence_claims", ()),
            required_evidence_claims=bundle.get("required_evidence_claims", ()),
            production_mode=bool(bundle.get("production_mode", True)),
            create_only=bundle.get("create_only", True),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"init_session_store_file_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_admit_session_file_continuation(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "policy" not in bundle:
            raise ValueError("admit_session_file_continuation_requires_policy")
        receipt = bundle.get("trajectory_receipt", bundle.get("receipt", {}))
        result = admit_autonomous_governance_session_file_continuation_v1(
            path=_store_file_path_from_bundle(
                bundle, command="admit_session_file_continuation"
            ),
            receipt=receipt,
            policy=bundle.get("policy", {}),
            expected_store_hash=bundle.get("expected_store_hash"),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"admit_session_file_continuation_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("admitted") is True else 2


def _cmd_verify_session_store_file(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "policy" not in bundle:
            raise ValueError("verify_session_store_file_requires_policy")
        result = verify_autonomous_governance_session_store_file_v1(
            path=_store_file_path_from_bundle(bundle, command="verify_session_store_file"),
            policy=bundle.get("policy", {}),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"verify_session_store_file_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_session_store_file_head(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        result = current_session_store_file_head_v1(
            path=_store_file_path_from_bundle(bundle, command="session_store_file_head")
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"session_store_file_head_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_live_session_file_context(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        path = _store_file_path_from_bundle(bundle, command="live_session_file_context")
        receipt = bundle.get("trajectory_receipt", bundle.get("receipt", {}))
        if not isinstance(receipt, dict):
            raise ValueError("live_session_file_context_requires_trajectory_receipt")
        surface = bundle.get("committed_surface_state", bundle.get("surface_state", {}))
        expected_policy_hash = bundle.get("expected_policy_hash", "")
        head = current_session_store_file_head_v1(path=path)
        if head.get("ok") is not True:
            result = {
                "schema": "zenodex.autonomous_governance.live_session_file_context_bundle.v1",
                "ok": False,
                "errors": tuple(head.get("errors", ())),
                "head": head,
                "live_context_hash": "",
            }
        else:
            result = {
                "schema": "zenodex.autonomous_governance.live_session_file_context_bundle.v1",
                "ok": True,
                "errors": (),
                "store_path": path,
                "store_hash": head.get("store_hash", ""),
                "head_pin_hash": dict(head.get("head_pin", {})).get("pin_hash", "")
                if isinstance(head.get("head_pin"), dict)
                else "",
                "trajectory_hash": receipt.get("trajectory_hash", ""),
                "expected_policy_hash": expected_policy_hash,
                "head": head,
                "live_context_hash": autonomous_governance_live_session_file_context_hash_v1(
                    store_hash=str(head.get("store_hash", "")),
                    head_pin_hash=str(
                        dict(head.get("head_pin", {})).get("pin_hash", "")
                        if isinstance(head.get("head_pin"), dict)
                        else ""
                    ),
                    committed_surface_state=surface,
                    trajectory_hash=str(receipt.get("trajectory_hash", "")),
                    expected_policy_hash=str(expected_policy_hash),
                ),
            }
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"live_session_file_context_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_admit_live_session_file_update(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "policy" not in bundle:
            raise ValueError("admit_live_session_file_update_requires_policy")
        receipt = bundle.get("trajectory_receipt", bundle.get("receipt", {}))
        surface = bundle.get("committed_surface_state", bundle.get("surface_state", {}))
        result = admit_autonomous_governance_live_session_file_update_v1(
            store_path=_store_file_path_from_bundle(
                bundle, command="admit_live_session_file_update"
            ),
            policy=bundle.get("policy", {}),
            trajectory_receipt=receipt,
            committed_surface_state=surface,
            expected_policy_hash=bundle.get("expected_policy_hash"),
            expected_store_hash=bundle.get("expected_store_hash"),
            expected_live_context_hash=bundle.get("expected_live_context_hash"),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"admit_live_session_file_update_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("admitted") is True else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    sample = sub.add_parser("sample", help="write a sample evaluation bundle")
    sample.add_argument("--output", help="path to write; stdout when omitted")
    sample.add_argument("--surface", action="store_true", help="sample the governance-surface bundle")
    sample.add_argument(
        "--trajectory", action="store_true", help="sample the multi-step trajectory bundle"
    )
    sample.add_argument("--ebrm", action="store_true", help="sample a frozen EBRM policy-step bundle")
    sample.set_defaults(func=_cmd_sample)

    evaluate = sub.add_parser("evaluate", help="evaluate a policy bundle")
    evaluate.add_argument("bundle", help="path to evaluation bundle JSON")
    evaluate.set_defaults(func=_cmd_evaluate)

    step = sub.add_parser("step", help="evaluate and apply one governance-surface policy step")
    step.add_argument("bundle", help="path to surface evaluation bundle JSON")
    step.set_defaults(func=_cmd_step)

    ebrm_step = sub.add_parser("ebrm-step", help="evaluate one frozen EBRM policy step")
    ebrm_step.add_argument("bundle", help="path to EBRM policy-step bundle JSON")
    ebrm_step.set_defaults(func=_cmd_ebrm_step)

    ebrm_evidence = sub.add_parser(
        "ebrm-evidence",
        help="emit deterministic verifier-labeled EBRM corpus metrics",
    )
    ebrm_evidence.add_argument("--output", help="path to write report; stdout when omitted")
    ebrm_evidence.add_argument(
        "--corpus-output",
        help="optional path to write the full verifier-labeled corpus JSON",
    )
    ebrm_evidence.add_argument(
        "--include-corpus",
        action="store_true",
        help="include full corpus rows inside the report JSON",
    )
    ebrm_evidence.set_defaults(func=_cmd_ebrm_evidence)

    ebrm_train = sub.add_parser(
        "ebrm-train",
        help="train and evaluate a deterministic verifier-labeled EBRM ranker",
    )
    ebrm_train.add_argument("--output", help="path to write report; stdout when omitted")
    ebrm_train.add_argument(
        "--model-output",
        help="optional path to write only the trained ranker artifact",
    )
    ebrm_train.add_argument(
        "--include-corpus",
        action="store_true",
        help="include full corpus rows inside the training report JSON",
    )
    ebrm_train.set_defaults(func=_cmd_ebrm_train)

    trajectory = sub.add_parser(
        "trajectory",
        help="run a multi-step autonomous governance trajectory (fail-closed)",
    )
    trajectory.add_argument("bundle", help="path to trajectory bundle JSON")
    trajectory.set_defaults(func=_cmd_trajectory)

    continue_trajectory = sub.add_parser(
        "continue-trajectory",
        help="run the next trajectory segment from a verified parent receipt",
    )
    continue_trajectory.add_argument(
        "bundle",
        help=(
            "path to JSON with policy, previous_receipt, steps, and "
            "expected_policy_hash"
        ),
    )
    continue_trajectory.set_defaults(func=_cmd_continue_trajectory)

    verify_trajectory = sub.add_parser(
        "verify-trajectory",
        help="independently re-verify a trajectory receipt against its policy",
    )
    verify_trajectory.add_argument(
        "bundle", help="path to JSON with {policy, trajectory_receipt}"
    )
    verify_trajectory.set_defaults(func=_cmd_verify_trajectory)

    admit_trajectory = sub.add_parser(
        "admit-trajectory",
        help="verify and run the client-side trajectory refuse-loop",
    )
    admit_trajectory.add_argument(
        "bundle",
        help=(
            "path to JSON with policy, trajectory_receipt, expected_policy_hash, "
            "and optional expected state anchors"
        ),
    )
    admit_trajectory.set_defaults(func=_cmd_admit_trajectory)

    verify_session = sub.add_parser(
        "verify-session",
        help="verify an ordered cross-trajectory autonomous governance session",
    )
    verify_session.add_argument(
        "bundle",
        help="path to JSON with policy and trajectory_receipts (or receipts)",
    )
    verify_session.set_defaults(func=_cmd_verify_session)

    init_session_store = sub.add_parser(
        "init-session-store",
        help="initialize a single-live-head session store from a genesis pin",
    )
    init_session_store.add_argument(
        "bundle",
        help="path to JSON with policy, genesis_pin, and genesis_receipt",
    )
    init_session_store.set_defaults(func=_cmd_init_session_store)

    admit_session_continuation = sub.add_parser(
        "admit-session-continuation",
        help="advance the session store head on a verified continuation",
    )
    admit_session_continuation.add_argument(
        "bundle",
        help="path to JSON with policy, store, and trajectory_receipt (or receipt)",
    )
    admit_session_continuation.set_defaults(func=_cmd_admit_session_continuation)

    verify_session_store = sub.add_parser(
        "verify-session-store",
        help="audit a session store with archived receipts replayed",
    )
    verify_session_store.add_argument(
        "bundle",
        help="path to JSON with policy and store",
    )
    verify_session_store.set_defaults(func=_cmd_verify_session_store)

    session_store_head = sub.add_parser(
        "session-store-head",
        help="read the current session-store head and surface state",
    )
    session_store_head.add_argument(
        "bundle",
        help="path to JSON store object or {store}",
    )
    session_store_head.set_defaults(func=_cmd_session_store_head)

    init_session_store_file = sub.add_parser(
        "init-session-store-file",
        help="initialize and persist a single-live-head session store file",
    )
    init_session_store_file.add_argument(
        "bundle",
        help="path to JSON with path, policy, genesis_pin, and genesis_receipt",
    )
    init_session_store_file.set_defaults(func=_cmd_init_session_store_file)

    admit_session_file_continuation = sub.add_parser(
        "admit-session-file-continuation",
        help="advance a persisted session store file on a verified continuation",
    )
    admit_session_file_continuation.add_argument(
        "bundle",
        help=(
            "path to JSON with path, policy, trajectory_receipt, and optional "
            "expected_store_hash"
        ),
    )
    admit_session_file_continuation.set_defaults(
        func=_cmd_admit_session_file_continuation
    )

    verify_session_store_file = sub.add_parser(
        "verify-session-store-file",
        help="audit a persisted session store file with archived receipts replayed",
    )
    verify_session_store_file.add_argument(
        "bundle",
        help="path to JSON with path and policy",
    )
    verify_session_store_file.set_defaults(func=_cmd_verify_session_store_file)

    session_store_file_head = sub.add_parser(
        "session-store-file-head",
        help="read the current persisted session-store head and surface state",
    )
    session_store_file_head.add_argument(
        "bundle",
        help="path to JSON with path",
    )
    session_store_file_head.set_defaults(func=_cmd_session_store_file_head)

    live_session_file_context = sub.add_parser(
        "live-session-file-context",
        help="compute the live context hash for a persisted session-store update",
    )
    live_session_file_context.add_argument(
        "bundle",
        help=(
            "path to JSON with path, trajectory_receipt, expected_policy_hash, "
            "and committed_surface_state"
        ),
    )
    live_session_file_context.set_defaults(func=_cmd_live_session_file_context)

    admit_live_session_file_update = sub.add_parser(
        "admit-live-session-file-update",
        help="admit a live autonomous-governance update through file-store custody",
    )
    admit_live_session_file_update.add_argument(
        "bundle",
        help=(
            "path to JSON with path, policy, trajectory_receipt, "
            "committed_surface_state, expected_policy_hash, expected_store_hash, "
            "and expected_live_context_hash"
        ),
    )
    admit_live_session_file_update.set_defaults(
        func=_cmd_admit_live_session_file_update
    )

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
