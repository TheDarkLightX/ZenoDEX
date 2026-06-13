#!/usr/bin/env python3
"""Validate the ZenoDEX consensus semantic BDD front door.

This checker is intentionally dependency-free. It treats the Gherkin feature
files as the human-readable front door, then verifies that the machine-readable
contract lists each scenario, preserves layer/status tags, and keeps known
overclaim phrases out of scoped differentials.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO = Path(__file__).resolve().parents[2]
DEFAULT_CONTRACT = REPO / "config" / "semantics" / "zenodex_consensus_contract_v1.json"

# --- v1 independent floor ------------------------------------------------------
# The contract JSON (required_scenarios) is mutable, so the self-consistency
# checks below would all still pass if a scenario were dropped from BOTH the JSON
# and the feature file. This hardcoded floor is the independent backstop: the v1
# contract MUST carry at least these scenario ids in its feature files. (Codex
# review 2026-06-06, finding #2.)
V1_REQUIRED_SCENARIO_IDS = frozenset(
    {
        "clob.place_limit_order.guest.claim_scoped_to_matching_core",
        "perps_np.deposit_collateral.core.zero_deposit_joins_account",
        "perps_np.deposit_collateral.core.deposit_does_not_consume_nonce",
        "perps_np.deposit_collateral.core.negative_rejects_without_mutation",
        "perps_np.deposit_collateral.guest.claim_scoped_to_live_replay_authority",
        "perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core",
    }
)

# The single tx-envelope replay obligation (P0-3b). Its scenario status, the
# envelope live_binding_status, and the guest live_equivalence_claim_level are
# ONE coupled obligation -- see _validate_obligation_coupling.
TX_ENVELOPE_REPLAY_SCENARIO_ID = (
    "perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core"
)


@dataclass(frozen=True)
class Scenario:
    scenario_id: str
    name: str
    layer: str
    status: str
    path: Path
    line: int


def _load_json(path: Path) -> Mapping[str, Any]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"{path}: invalid JSON: {exc}") from exc
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path}: top-level JSON must be an object")
    return obj


def _repo_path(raw: str) -> Path:
    path = Path(raw)
    return path if path.is_absolute() else REPO / path


def parse_feature(path: Path) -> list[Scenario]:
    text = path.read_text(encoding="utf-8")
    pending_tags: list[str] = []
    scenarios: list[Scenario] = []
    for line_no, raw in enumerate(text.splitlines(), start=1):
        stripped = raw.strip()
        if stripped.startswith("@"):
            pending_tags = re.findall(r"@[^\s]+", stripped)
            continue
        if not stripped.startswith("Scenario:"):
            continue
        tags: dict[str, str] = {}
        for tag in pending_tags:
            body = tag[1:]
            if ":" in body:
                key, value = body.split(":", 1)
                tags[key] = value
        pending_tags = []
        missing = [key for key in ("scenario", "layer", "status") if key not in tags]
        if missing:
            raise ValueError(f"{path}:{line_no}: scenario missing tags {missing}")
        name = stripped.split(":", 1)[1].strip()
        scenarios.append(
            Scenario(
                scenario_id=tags["scenario"],
                name=name,
                layer=tags["layer"],
                status=tags["status"],
                path=path,
                line=line_no,
            )
        )
    return scenarios


def _validate_contract_shape(contract: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if contract.get("schema") != "zenodex.consensus_semantic_contract.v1":
        errors.append("schema must be zenodex.consensus_semantic_contract.v1")
    for key in ("claim_levels", "authority_order", "operations", "bdd"):
        if key not in contract:
            errors.append(f"missing top-level key {key!r}")
    claim_levels = contract.get("claim_levels")
    if isinstance(claim_levels, Mapping):
        # REVIEW(Codex 2026-06-06, grade A after fix): the P0-3b contract added a
        # scoped replay-authority claim level, but the shape gate still required
        # only the older levels. That let the new level be removed while downstream
        # fields continued to cite it. Keep the claim vocabulary itself load-bearing.
        for required in (
            "core_equivalent",
            "modeled_envelope_equivalent",
            "live_replay_authority_equivalent",
            "live_equivalent",
        ):
            if required not in claim_levels:
                errors.append(f"claim_levels missing {required}")
    else:
        errors.append("claim_levels must be an object")
    return errors


def _validate_bdd(contract: Mapping[str, Any]) -> tuple[list[str], list[Scenario]]:
    errors: list[str] = []
    bdd = contract.get("bdd")
    if not isinstance(bdd, Mapping):
        return ["bdd must be an object"], []
    feature_files = bdd.get("feature_files")
    if not isinstance(feature_files, list) or not feature_files:
        return ["bdd.feature_files must be a non-empty list"], []
    scenarios: list[Scenario] = []
    for raw_path in feature_files:
        if not isinstance(raw_path, str):
            errors.append("bdd.feature_files entries must be strings")
            continue
        path = _repo_path(raw_path)
        if not path.is_file():
            errors.append(f"feature file missing: {raw_path}")
            continue
        try:
            scenarios.extend(parse_feature(path))
        except ValueError as exc:
            errors.append(str(exc))

    by_id: dict[str, Scenario] = {}
    for scenario in scenarios:
        if scenario.scenario_id in by_id:
            first = by_id[scenario.scenario_id]
            errors.append(
                f"duplicate scenario id {scenario.scenario_id}: "
                f"{first.path.relative_to(REPO)}:{first.line} and "
                f"{scenario.path.relative_to(REPO)}:{scenario.line}"
            )
        by_id[scenario.scenario_id] = scenario

    required = bdd.get("required_scenarios")
    if not isinstance(required, Mapping):
        errors.append("bdd.required_scenarios must be an object")
        return errors, scenarios
    for scenario_id, raw_meta in required.items():
        if not isinstance(raw_meta, Mapping):
            errors.append(f"required scenario {scenario_id} metadata must be an object")
            continue
        scenario = by_id.get(str(scenario_id))
        if scenario is None:
            errors.append(f"required scenario missing from feature files: {scenario_id}")
            continue
        expected_layer = raw_meta.get("layer")
        expected_status = raw_meta.get("status")
        if scenario.layer != expected_layer:
            errors.append(
                f"{scenario_id}: layer tag {scenario.layer!r} != contract {expected_layer!r}"
            )
        if scenario.status != expected_status:
            errors.append(
                f"{scenario_id}: status tag {scenario.status!r} != contract {expected_status!r}"
            )
    for scenario_id in by_id:
        if scenario_id not in required:
            errors.append(f"feature scenario not listed in contract: {scenario_id}")
    return errors, scenarios


def _validate_deposit_contract(contract: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    operations = contract.get("operations")
    if not isinstance(operations, Mapping):
        return ["operations must be an object"]
    op = operations.get("perps_np.deposit_collateral")
    if not isinstance(op, Mapping):
        return ["operations missing perps_np.deposit_collateral"]
    core = op.get("core")
    envelope = op.get("envelope")
    guest = op.get("guest")
    if not isinstance(core, Mapping):
        errors.append("perps_np.deposit_collateral.core must be an object")
    else:
        expectations = {
            "zero_amount_behavior": "account_join_no_collateral_delta",
            "negative_amount_behavior": "reject_no_mutation",
            "nonce_layer": "tx_envelope",
            "core_nonce_effect": "unchanged",
        }
        for key, expected in expectations.items():
            if core.get(key) != expected:
                errors.append(f"deposit core {key} must be {expected!r}")
    if not isinstance(envelope, Mapping):
        errors.append("perps_np.deposit_collateral.envelope must be an object")
    else:
        # P0-3b CLOSED (2026-06-06): the envelope is bound to the live replay
        # authority replay_guard.admit (strict-sequential). The chain_replay_layer
        # note must record where production replay actually lives (tau tx_sequence)
        # so the live_replay_authority_equivalent claim stays honestly scoped.
        if envelope.get("live_binding_status") != "bound_to_replay_guard":
            errors.append("deposit envelope live_binding_status must be bound_to_replay_guard")
        if envelope.get("closed_obligation_id") != "P0-3b":
            errors.append("deposit envelope closed_obligation_id must be P0-3b")
        chain = envelope.get("chain_replay_layer")
        if not isinstance(chain, Mapping):
            errors.append("deposit envelope must record chain_replay_layer provenance")
        else:
            if chain.get("enforced_at") != "tau_node_tx_sequence":
                errors.append("chain_replay_layer.enforced_at must be tau_node_tx_sequence")
            if chain.get("python_authority_model") != "src/core/replay_guard.py::admit":
                errors.append("chain_replay_layer.python_authority_model must be replay_guard.admit")
            if not chain.get("evidence"):
                errors.append("chain_replay_layer must cite evidence (file:line)")
    if not isinstance(guest, Mapping):
        errors.append("perps_np.deposit_collateral.guest must be an object")
    else:
        if guest.get("envelope_binding") != "live_replay_guard_admit_strict_sequential":
            errors.append("guest envelope_binding must be live_replay_guard_admit_strict_sequential")
        if guest.get("live_equivalence_claim_level") != "live_replay_authority_equivalent":
            errors.append(
                "guest live_equivalence_claim_level must be live_replay_authority_equivalent "
                "(scoped to the replay authority/model; NOT bare live_equivalent)"
            )
    return errors


def _validate_clob_contract(contract: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    operations = contract.get("operations")
    if not isinstance(operations, Mapping):
        return []  # shape error reported by _validate_deposit_contract
    op = operations.get("clob.place_limit_order")
    if not isinstance(op, Mapping):
        return ["operations missing clob.place_limit_order"]
    core = op.get("core")
    api = op.get("api")
    guest = op.get("guest")
    if not isinstance(core, Mapping):
        errors.append("clob.place_limit_order.core must be an object")
    else:
        if core.get("live_authority_ref") != "src/core/clob_matching.py::apply_order":
            errors.append("CLOB core live_authority_ref must be clob_matching.apply_order")
        if core.get("claim_level") != "core_equivalent":
            errors.append("CLOB core claim_level must be core_equivalent")
    if not isinstance(api, Mapping):
        errors.append("clob.place_limit_order.api must be an object")
    else:
        if api.get("live_authority_ref") != "src/integration/orderbook_api.py::handle_orderbook_request":
            errors.append("CLOB API live_authority_ref must be orderbook_api.handle_orderbook_request")
        if api.get("proof_invocation") != "none_stage0":
            errors.append("CLOB API proof_invocation must be none_stage0")
        if api.get("proof_status_on_accept") != "proof_pending":
            errors.append("CLOB API proof_status_on_accept must be proof_pending")
        if api.get("latest_proven_height_on_accept") is not None:
            errors.append("CLOB API latest_proven_height_on_accept must be null")
    if not isinstance(guest, Mapping):
        errors.append("clob.place_limit_order.guest must be an object")
    else:
        # REVIEW(Codex 2026-06-07, grade A after fix): the CLOB RISC0 guest is a
        # real matching-core proof surface, but the deployed Stage-0 API does not
        # invoke it. Keep the strongest claim at core_equivalent until the live
        # admission path is proof-gated.
        if guest.get("proof_type") != "risc0.zenodex_clob_transition.v1":
            errors.append("CLOB guest proof_type must be risc0.zenodex_clob_transition.v1")
        if guest.get("live_equivalence_claim_level") != "core_equivalent":
            errors.append("CLOB guest live_equivalence_claim_level must be core_equivalent")
        if guest.get("strongest_allowed_claim") != "core_equivalent":
            errors.append("CLOB guest strongest_allowed_claim must be core_equivalent")
        if (
            guest.get("deployed_api_admission_binding_status")
            != "not_bound_stage0_api_does_not_invoke_guest"
        ):
            errors.append("CLOB guest must record that Stage-0 API admission is not guest-bound")
    errors.extend(_validate_orderbook_api_stage0_proof_boundary())
    return errors


def _validate_orderbook_api_stage0_proof_boundary() -> list[str]:
    path = REPO / "src" / "integration" / "orderbook_api.py"
    text = path.read_text(encoding="utf-8")
    errors: list[str] = []
    forbidden_tokens = (
        "execute_clob_transition_v1",
        "ZenoProofInputV1",
        "tau-state-proof-risc0-cli",
        "default_prover",
        "ProofStatus.PROOF_VERIFIED.value",
    )
    for token in forbidden_tokens:
        if token in text:
            errors.append(f"orderbook_api Stage-0 proof boundary: forbidden token {token!r}")
    required_tokens = (
        "apply_order(book, built.order)",
        "proof_status=ProofStatus.PROOF_PENDING.value",
        '"latest_proven_height": None',
        '"proof_mode": "pending"',
        '"accepted_verifier_ids": []',
    )
    for token in required_tokens:
        if token not in text:
            errors.append(f"orderbook_api Stage-0 proof boundary missing {token!r}")
    return errors


def _validate_v1_floor(scenarios: Sequence[Scenario]) -> list[str]:
    """Independent backstop: every v1-required scenario id must be present in the
    parsed feature files. Unlike _validate_bdd (which compares the contract's own
    required_scenarios to the features), this reads NOTHING mutable -- a scenario
    silently dropped from both the JSON and the feature still fails here."""
    present = {scenario.scenario_id for scenario in scenarios}
    return [
        f"v1 floor: required scenario absent from feature files: {scenario_id}"
        for scenario_id in sorted(V1_REQUIRED_SCENARIO_IDS - present)
    ]


def _validate_obligation_coupling(
    contract: Mapping[str, Any], scenarios: Sequence[Scenario]
) -> list[str]:
    """P0-3b is ONE obligation expressed in three places. It cannot be silently
    'closed' by editing a single field. The tx-envelope replay scenario's status,
    the envelope live_binding_status, and the guest live_equivalence_claim_level
    must all be 'open_obligation' together, or all be closed (non-open) together.
    A desync -- e.g. the scenario flipped to 'executable' while the envelope still
    says 'open_obligation' -- is a contract-integrity failure, NOT a valid
    promotion: closing P0-3b means binding the envelope to the live replay path,
    which must move all three at once. (Codex review 2026-06-06, finding #3.)"""
    op = contract.get("operations")
    if not isinstance(op, Mapping):
        return []  # shape error reported by _validate_deposit_contract
    deposit = op.get("perps_np.deposit_collateral")
    if not isinstance(deposit, Mapping):
        return []
    envelope = deposit.get("envelope")
    guest = deposit.get("guest")
    binding = envelope.get("live_binding_status") if isinstance(envelope, Mapping) else None
    claim = guest.get("live_equivalence_claim_level") if isinstance(guest, Mapping) else None
    scenario = next(
        (s for s in scenarios if s.scenario_id == TX_ENVELOPE_REPLAY_SCENARIO_ID), None
    )
    scn_status = scenario.status if scenario is not None else None

    poles = {
        "tx-envelope scenario status": (scn_status, scn_status == "open_obligation"),
        "envelope.live_binding_status": (binding, binding == "open_obligation"),
        "guest.live_equivalence_claim_level": (claim, claim == "open_obligation"),
    }
    open_flags = {is_open for _, is_open in poles.values()}
    if len(open_flags) != 1:
        detail = ", ".join(f"{name}={value!r}" for name, (value, _) in poles.items())
        return [
            "P0-3b obligation desynchronized (all three must be 'open_obligation' "
            f"together or all closed together): {detail}"
        ]
    return []


def _module_docstring(text: str) -> str:
    try:
        return ast.get_docstring(ast.parse(text)) or ""
    except SyntaxError:
        return ""


def _validate_overclaim_guards(contract: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    guards = contract.get("overclaim_guards", [])
    if not isinstance(guards, list):
        return ["overclaim_guards must be a list"]
    for guard in guards:
        if not isinstance(guard, Mapping):
            errors.append("overclaim guard must be an object")
            continue
        raw_path = guard.get("path")
        if not isinstance(raw_path, str):
            errors.append("overclaim guard path must be a string")
            continue
        path = _repo_path(raw_path)
        if not path.is_file():
            errors.append(f"overclaim guard path missing: {raw_path}")
            continue
        text = path.read_text(encoding="utf-8")
        for token in guard.get("forbidden_tokens", []):
            if not isinstance(token, str):
                errors.append(f"{raw_path}: forbidden token must be a string")
                continue
            if token in text:
                errors.append(f"{raw_path}: forbidden overclaim token present: {token!r}")
        for token in guard.get("required_tokens", []):
            if not isinstance(token, str):
                errors.append(f"{raw_path}: required token must be a string")
                continue
            if token not in text:
                errors.append(f"{raw_path}: required scoping token missing: {token!r}")
        # File-level presence is not enough: the honesty caveat must live in the
        # MODULE DOCSTRING, not be buried in a comment elsewhere in the file.
        # (Codex review 2026-06-06, finding #6.)
        if raw_path.endswith(".py"):
            module_doc = _module_docstring(text)
            for token in guard.get("required_tokens", []):
                if isinstance(token, str) and token not in module_doc:
                    errors.append(
                        f"{raw_path}: required scoping token missing from module "
                        f"docstring: {token!r}"
                    )
    return errors


def _display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO))
    except ValueError:
        return str(path)


def validate(contract_path: Path = DEFAULT_CONTRACT) -> dict[str, Any]:
    contract = _load_json(contract_path)
    errors: list[str] = []
    errors.extend(_validate_contract_shape(contract))
    bdd_errors, scenarios = _validate_bdd(contract)
    errors.extend(bdd_errors)
    errors.extend(_validate_v1_floor(scenarios))
    errors.extend(_validate_deposit_contract(contract))
    errors.extend(_validate_clob_contract(contract))
    errors.extend(_validate_obligation_coupling(contract, scenarios))
    errors.extend(_validate_overclaim_guards(contract))
    return {
        "ok": not errors,
        "contract_path": _display_path(contract_path),
        "scenario_count": len(scenarios),
        "executable_scenarios": sum(1 for scenario in scenarios if scenario.status == "executable"),
        "open_obligations": [
            scenario.scenario_id for scenario in scenarios if scenario.status == "open_obligation"
        ],
        "errors": errors,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--json", action="store_true", help="emit JSON report")
    args = parser.parse_args(argv)
    report = validate(args.contract)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        if report["ok"]:
            print(
                f"ok: {report['scenario_count']} scenarios, "
                f"{report['executable_scenarios']} executable, "
                f"{len(report['open_obligations'])} open obligation(s)"
            )
        else:
            print("semantic contract check failed", file=sys.stderr)
            for error in report["errors"]:
                print(f"- {error}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
