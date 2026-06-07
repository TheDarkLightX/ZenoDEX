"""Characterization corpus for ``verify_fire_proof_tree_certificate``.

This is a behavior-LOCK for a fail-closed proof-tree certificate verifier whose
golden tests cover only a handful of its ~30 reject codes. Before the staged
refactor (queue #7) the CURRENT verifier was run over a valid fixture plus a
broad set of programmatic single-mutations, and every ``(ok, err)`` outcome --
including *which* failure wins (first-failure-wins ordering) -- was captured to
``fixtures/fire_proof_tree_cert_characterization_v1.json``.

The refactor must reproduce that JSON EXACTLY. This empirically catches any
untested-path behavior change OR ordering change across all cases, which is
strictly stronger than the golden tests + a couple of hand-picked mutations.

Regenerate (ONLY against known-good behavior, e.g. before a behavior-preserving
refactor) with::

    python3 tests/kernels/test_fire_proof_tree_cert_characterization.py --regen
"""

from __future__ import annotations

import copy
import json
import sys
from pathlib import Path
from typing import Any, Callable

from src.fire.verifier.proof_tree_cert_v1 import verify_fire_proof_tree_certificate

_FIXTURE = Path(__file__).parent / "fixtures" / "fire_proof_tree_cert_characterization_v1.json"

OBJECT_HASH = "sha256:" + ("1" * 64)
INSTANCE_HASH = "sha256:" + ("2" * 64)
CERTIFICATE_SHA256 = "sha256:" + ("4" * 64)
_OTHER_HASH = "sha256:" + ("9" * 64)


def _valid_payload() -> dict[str, Any]:
    # Mirrors tests/kernels/test_fire_proof_tree_cert_v1.py::_valid_payload.
    return {
        "version": "FIRE_CERT_RULES_v0.1",
        "object_hash": OBJECT_HASH,
        "instance_hash": INSTANCE_HASH,
        "certificate_sha256": CERTIFICATE_SHA256,
        "runtime_certificate_summary": {
            "root_rule": "min",
            "root_interval": {"lower": 0, "upper": 3},
            "node_count": 3,
            "exact_params": [{"name": "cap_index", "value": 3}],
            "source_bounds": [{"name": "burn_final", "lower": 0, "upper": 9}],
            "operator_tree": {
                "rule": "min",
                "lower": 0,
                "upper": 3,
                "children": [
                    {"rule": "source_bound", "name": "burn_final", "lower": 0, "upper": 9, "children": []},
                    {"rule": "exact_param", "name": "cap_index", "lower": 3, "upper": 3, "children": []},
                ],
            },
        },
        "dependency_hashes": [
            {"name": "burn_index_v1", "version": "1.0.0", "hash": "sha256:" + ("3" * 64)}
        ],
        "evidence_floor": "contract",
        "claims": {
            "BoundOK": {"evidence": "proved", "claim": "0 <= payoff <= cap", "root_node": "n_bound"},
            "CollateralOK": {"evidence": "contract", "claim": "writer collateral >= cap", "root_node": "n_collateral"},
        },
        "proof_tree": [
            {
                "id": "n_bound_expr_0",
                "rule": "source_bound",
                "claim": {"predicate": "BoundLeafSourceBound", "name": "burn_final", "lower": "0", "upper": "9"},
                "evidence": "proved",
            },
            {
                "id": "n_bound_expr_1",
                "rule": "exact_param",
                "claim": {"predicate": "BoundLeafExactParam", "name": "cap_index", "value": "3", "lower": "3", "upper": "3"},
                "evidence": "proved",
            },
            {
                "id": "n_bound_expr",
                "rule": "interval_min",
                "claim": {"predicate": "BoundExpr", "runtime_rule": "min", "lower": "0", "upper": "3"},
                "inputs": ["n_bound_expr_0", "n_bound_expr_1"],
                "evidence": "proved",
            },
            {
                "id": "n_bound",
                "rule": "witness_bound_intro",
                "claim": {"predicate": "BoundOK", "lower": "0", "upper": "3", "runtime_root_rule": "min", "runtime_node_count": "3"},
                "inputs": ["n_bound_expr"],
                "evidence": "proved",
            },
            {
                "id": "n_collateral",
                "rule": "collateral_one_sided_writer",
                "claim": {"predicate": "CollateralOK", "party": "writer", "asset": "zUSD"},
                "inputs": ["n_bound"],
                "evidence": "contract",
            },
        ],
    }


def _valid_kwargs() -> dict[str, Any]:
    return {
        "expected_object_hash": OBJECT_HASH,
        "expected_instance_hash": INSTANCE_HASH,
        "expected_certificate_sha256": CERTIFICATE_SHA256,
        "expected_claim_evidence": {"BoundOK": "proved", "CollateralOK": "contract"},
    }


def _mut(fn: Callable[[dict[str, Any], dict[str, Any]], None]) -> Callable[[], tuple[dict[str, Any], dict[str, Any]]]:
    def build() -> tuple[dict[str, Any], dict[str, Any]]:
        payload = _valid_payload()
        kwargs = _valid_kwargs()
        fn(payload, kwargs)
        return payload, kwargs

    return build


def characterization_cases() -> list[tuple[str, dict[str, Any], dict[str, Any]]]:
    """Deterministic ordered (case_id, payload, kwargs) corpus.

    Each case is the valid fixture with exactly one mutation, exercising every
    verification stage. Order is stable so first-failure-wins is locked.
    """
    cases: list[tuple[str, dict[str, Any], dict[str, Any]]] = []

    def add(case_id: str, fn: Callable[[dict[str, Any], dict[str, Any]], None]) -> None:
        payload, kwargs = _mut(fn)()
        cases.append((case_id, payload, kwargs))

    # valid (accept path)
    cases.append(("valid", _valid_payload(), _valid_kwargs()))
    cases.append(("valid_no_expectations", _valid_payload(), {}))

    # stage 1: schema
    add("schema_wrong_version", lambda p, k: p.__setitem__("version", "WRONG"))
    add("schema_missing_object_hash", lambda p, k: p.pop("object_hash"))
    add("schema_missing_claims", lambda p, k: p.pop("claims"))
    add("schema_missing_proof_tree", lambda p, k: p.pop("proof_tree"))

    # stage 2: header hash bindings
    add("header_object_hash_nonstring", lambda p, k: p.__setitem__("object_hash", 123))
    add("header_object_hash_mismatch", lambda p, k: k.__setitem__("expected_object_hash", _OTHER_HASH))
    add("header_instance_hash_mismatch", lambda p, k: k.__setitem__("expected_instance_hash", _OTHER_HASH))
    add("header_certificate_sha256_mismatch", lambda p, k: k.__setitem__("expected_certificate_sha256", _OTHER_HASH))
    add("header_certificate_sha256_invalid", lambda p, k: p.__setitem__("certificate_sha256", "notahash"))

    # stage 3: runtime certificate summary
    def _runtime_mismatch(p: dict[str, Any], k: dict[str, Any]) -> None:
        summary = copy.deepcopy(p["runtime_certificate_summary"])
        summary["root_interval"] = {"lower": 0, "upper": 99}
        k["expected_runtime_certificate_summary"] = summary

    add("runtime_summary_mismatch", _runtime_mismatch)

    # stage 4: dependency hashes
    add(
        "dependency_hashes_mismatch",
        lambda p, k: k.__setitem__(
            "expected_dependency_hashes", [{"name": "other", "version": "9.9.9", "hash": _OTHER_HASH}]
        ),
    )

    # stage 5: node table (drop each node; dup id; unknown rule)
    for i in range(5):
        add(f"drop_node_{i}", lambda p, k, i=i: p["proof_tree"].pop(i))
    add("duplicate_node_id", lambda p, k: p["proof_tree"][1].__setitem__("id", p["proof_tree"][0]["id"]))
    for i in range(5):
        add(f"unknown_rule_node_{i}", lambda p, k, i=i: p["proof_tree"][i].__setitem__("rule", "nonexistent_rule"))
    add("node_id_nonstring", lambda p, k: p["proof_tree"][0].__setitem__("id", 7))

    # stage 6: node inputs + predicate + rule shapes
    add("break_input_ref", lambda p, k: p["proof_tree"][2].__setitem__("inputs", ["does_not_exist"]))
    add("input_id_nonstring", lambda p, k: p["proof_tree"][2].__setitem__("inputs", [7]))
    add("predicate_mismatch", lambda p, k: p["proof_tree"][4]["claim"].__setitem__("predicate", "WrongPredicate"))

    # stage 7: claim roots + bound special-case
    add("missing_root_node", lambda p, k: p["claims"]["BoundOK"].__setitem__("root_node", "missing_node"))
    add("claim_root_nonstring", lambda p, k: p["claims"]["BoundOK"].__setitem__("root_node", 7))
    add("bound_lower_mismatch", lambda p, k: p["proof_tree"][3]["claim"].__setitem__("lower", "1"))
    add("bound_upper_mismatch", lambda p, k: p["proof_tree"][3]["claim"].__setitem__("upper", "99"))
    add("claim_evidence_mismatch", lambda p, k: p["claims"]["CollateralOK"].__setitem__("evidence", "proved"))

    # stage 8: expected claim evidence
    add("expected_claim_evidence_wrong", lambda p, k: k["expected_claim_evidence"].__setitem__("BoundOK", "contract"))
    add(
        "expected_claim_evidence_missing_claim",
        lambda p, k: k["expected_claim_evidence"].__setitem__("NotAClaim", "proved"),
    )

    # stage 9: evidence floor
    add("evidence_floor_mismatch", lambda p, k: p.__setitem__("evidence_floor", "proved"))
    add("evidence_floor_nonstring", lambda p, k: p.__setitem__("evidence_floor", 7))

    return cases


def _run(case: tuple[str, dict[str, Any], dict[str, Any]]) -> dict[str, Any]:
    case_id, payload, kwargs = case
    try:
        ok, err, _verification = verify_fire_proof_tree_certificate(
            copy.deepcopy(payload), **copy.deepcopy(kwargs)
        )
    except Exception as exc:  # noqa: BLE001 -- characterize raises warts-and-all
        return {"case": case_id, "ok": False, "err": None, "raised": type(exc).__name__}
    return {"case": case_id, "ok": bool(ok), "err": err}


def _capture() -> list[dict[str, Any]]:
    return [_run(case) for case in characterization_cases()]


def test_characterization_corpus_matches_locked_behavior() -> None:
    expected = json.loads(_FIXTURE.read_text())
    actual = _capture()
    assert actual == expected, (
        "verify_fire_proof_tree_certificate behavior drifted from the locked "
        "characterization corpus. If this change is intentional it is a "
        "version-bumped behavior change, NOT a refactor -- regenerate with --regen."
    )


def test_corpus_is_non_vacuous() -> None:
    # Sanity: the corpus must contain accepts AND a broad spread of distinct rejects.
    rows = _capture()
    assert any(r["ok"] for r in rows), "corpus has no accept case"
    rejects = {r["err"] for r in rows if not r["ok"]}
    assert len(rejects) >= 15, f"corpus exercises too few distinct reject codes: {len(rejects)}"


def test_claim_summary_reject_code_table_is_complete() -> None:
    # Locks the elif->table collapse (the 12 summary-bound claim names -> reject
    # codes). The corpus fixture has no IntegerEvalOK-style claims, so this is the
    # explicit guard that the table matches the original 12-branch ladder. BoundOK
    # is intentionally absent (it has a bespoke bound-operator-tree verification).
    from src.fire.verifier.proof_tree_cert_v1 import _CLAIM_SUMMARY_REJECT_CODES

    assert _CLAIM_SUMMARY_REJECT_CODES == {
        "IntegerEvalOK": "proof_tree_cert_integer_eval_summary_mismatch",
        "UnitOK": "proof_tree_cert_unit_summary_mismatch",
        "ReplayOK": "proof_tree_cert_replay_summary_mismatch",
        "ObjectHashBindOK": "proof_tree_cert_object_bind_summary_mismatch",
        "InstanceHashBindOK": "proof_tree_cert_instance_bind_summary_mismatch",
        "DependencyClosed": "proof_tree_cert_dependency_summary_mismatch",
        "WitnessOK": "proof_tree_cert_witness_policy_summary_mismatch",
        "ParamOK": "proof_tree_cert_param_summary_mismatch",
        "AuthorizationOK": "proof_tree_cert_authorization_summary_mismatch",
        "NonceOK": "proof_tree_cert_nonce_summary_mismatch",
        "MaturityOK": "proof_tree_cert_maturity_summary_mismatch",
        "WindowOK": "proof_tree_cert_window_summary_mismatch",
    }
    assert "BoundOK" not in _CLAIM_SUMMARY_REJECT_CODES


if __name__ == "__main__":
    if "--regen" in sys.argv:
        _FIXTURE.parent.mkdir(parents=True, exist_ok=True)
        _FIXTURE.write_text(json.dumps(_capture(), indent=2) + "\n")
        print(f"wrote {_FIXTURE} ({len(_capture())} cases)")
    else:
        print("pass --regen to (re)capture the corpus from the current verifier")
