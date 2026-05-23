from __future__ import annotations

"""State-feedback explorer for settlement attestation replay, staleness, and policy drift."""

import argparse
import copy
import hashlib
import importlib.util
import json
import sys
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Iterator, Literal, Sequence, cast

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

FULL_SUPPORTED = importlib.util.find_spec("py_ecc") is not None
AttestationMode = Literal["policy", "full"]

from src.integration import settlement_price_attestation as attestation_mod
from tools.stateful_feedback import (
    ExplorationTargetReport,
    FeedbackMode,
    Mutation,
    explore_bounded_frontier,
    load_dangerous_surface_manifest,
    report_to_json,
    stable_jsonable,
)
from tools.stateful_semantics import sequence_action_summary, settlement_attestation_semantic_state


ATTESTATION_FILE = (ROOT_DIR / "src/integration/settlement_price_attestation.py").resolve()
POLICY_ATTESTATION_PAYLOAD: dict[str, Any] = {
    "schema": "zenodex/settlement-spot-price-attestation/v1",
    "packet": {
        "schema": "zenodex/settlement-spot-price-packet/v1",
        "entries": [
            {
                "asset": "0x0101010101010101010101010101010101010101010101010101010101010101",
                "price": 100,
                "observed_epoch": 95,
                "age_epochs": 5,
                "source_id": "oracle:a",
            },
            {
                "asset": "0x0202020202020202020202020202020202020202020202020202020202020202",
                "price": 120,
                "observed_epoch": 97,
                "age_epochs": 3,
                "source_id": "oracle:b",
            },
        ],
        "now_epoch": 100,
        "max_staleness_epochs": 10,
        "cross_module_sync_required": False,
        "cross_module_sync_ok": False,
        "price_vector_sha256": "5a2787fd7dab3397947147fb050fb5bb7347be864ca650734128d4e08e66ff0e",
        "provenance_vector_sha256": "2851e3487e39e6a2f77c44d4efe0eff517818a046f1d21bb0bae8fe3de78ec29",
        "unique_assets": True,
        "all_positive": True,
        "all_fresh": True,
        "provenance_ok": True,
    },
    "signer_pubkey": "0xb928f3beb93519eecf0145da903b40a4c97dca00b21f12ac0df3be9116ef2ef27b2ae6bcd4c5bc2d54ef5a70627efcb7",
    "signed_at_epoch": 100,
    "packet_hash": "0x467af5f90af00f84ce7b065fa7752ed5b04acb32e6caac1fce429d9390d56805",
    "signature": "0xa36b7630385c370e04de314f28bb49158ea82a4d3addcebac84e0989e24d466443c9039786ae6c5e670595d4d28256cf178cdae6ad9e6c25d2b70c94fce6d651793a27e413191407c9235a0f29652dcf5fa1ea89674fd26d25a65a02a2b629ff",
}
_POLICY_UNSIGNED = {
    key: copy.deepcopy(value) for key, value in POLICY_ATTESTATION_PAYLOAD.items() if key != "signature"
}
_POLICY_MESSAGE_BYTES = attestation_mod._attestation_message_bytes(_POLICY_UNSIGNED)
_POLICY_PUBKEY_BYTES = bytes.fromhex(cast(str, POLICY_ATTESTATION_PAYLOAD["signer_pubkey"])[2:])
_POLICY_SIGNATURE_BYTES = bytes.fromhex(cast(str, POLICY_ATTESTATION_PAYLOAD["signature"])[2:])


@dataclass(frozen=True)
class MinimizedWitness:
    target: str
    derivation: str
    attestation_mode: AttestationMode
    outcome_label: str
    path_id: str
    path_length: int
    original_size: int
    minimized_size: int
    payload: object


class _PolicyG2Basic:
    @staticmethod
    def Verify(pubkey_bytes: bytes, message: bytes, sig_bytes: bytes) -> bool:
        return (
            pubkey_bytes == _POLICY_PUBKEY_BYTES
            and message == _POLICY_MESSAGE_BYTES
            and sig_bytes == _POLICY_SIGNATURE_BYTES
        )


@contextmanager
def _policy_verify_patch() -> Iterator[None]:
    original_available = getattr(attestation_mod, "_BLS_AVAILABLE", False)
    original_g2 = getattr(attestation_mod, "G2Basic", None)
    attestation_mod._BLS_AVAILABLE = True
    attestation_mod.G2Basic = _PolicyG2Basic
    try:
        yield
    finally:
        attestation_mod._BLS_AVAILABLE = original_available
        attestation_mod.G2Basic = original_g2


def _mode_supported(attestation_mode: AttestationMode) -> bool:
    return attestation_mode == "policy" or FULL_SUPPORTED


def _seed_payload() -> dict[str, Any]:
    return {
        "steps": [
            {
                "consumer_now_epoch": 103,
                "allowed_sources": ["oracle:a", "oracle:b"],
                "tamper_packet_hash": False,
                "tamper_signature": False,
            },
            {
                "consumer_now_epoch": 103,
                "allowed_sources": ["oracle:a", "oracle:b"],
                "tamper_packet_hash": False,
                "tamper_signature": False,
            },
        ]
    }


def _trace(payload: object, *, attestation_mode: AttestationMode) -> tuple[str, str, int, tuple[str, ...]]:
    try:
        steps = cast(list[dict[str, Any]], cast(dict[str, Any], payload)["steps"])
        outcome = _sequence_outcome(payload, attestation_mode=attestation_mode)
        path_summary = {
            "attestation_mode": attestation_mode,
            "steps": [
                {
                    "consumer_now_epoch": step.get("consumer_now_epoch"),
                    "allowed_sources": sorted(cast(list[str], step.get("allowed_sources", []))),
                    "tamper_packet_hash": step.get("tamper_packet_hash"),
                    "tamper_signature": step.get("tamper_signature"),
                }
                for step in steps
                if isinstance(step, dict)
            ],
            "outcome": outcome,
        }
        path_length = len(steps)
    except Exception as exc:  # pragma: no cover
        outcome = f"{type(exc).__name__}:{exc}"
        path_summary = {"payload": stable_jsonable(payload), "outcome": outcome}
        path_length = 0
    digest = hashlib.sha256(
        json.dumps(stable_jsonable(path_summary), sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode(
            "utf-8"
        )
    ).hexdigest()[:16]
    return outcome, digest, path_length, ()


def _verify_payload(
    *,
    attestation_payload: dict[str, Any],
    consumer_now_epoch: int,
    allowed_sources: list[str],
    attestation_mode: AttestationMode,
) -> tuple[bool, str | None]:
    verifier = attestation_mod.verify_settlement_spot_price_attestation_payload
    kwargs = {
        "payload": attestation_payload,
        "consumer_now_epoch": consumer_now_epoch,
        "max_attestation_age_epochs": 5,
        "allowed_signers": {cast(str, POLICY_ATTESTATION_PAYLOAD["signer_pubkey"]): allowed_sources},
    }
    if attestation_mode == "policy":
        with _policy_verify_patch():
            return verifier(**kwargs)
    return verifier(**kwargs)


def _sequence_outcome(payload: object, *, attestation_mode: AttestationMode) -> str:
    if not _mode_supported(attestation_mode):
        return "unsupported:py_ecc unavailable"
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    steps = payload.get("steps")
    if not isinstance(steps, list) or not steps:
        raise TypeError("steps must be a non-empty list")

    for idx, step in enumerate(steps):
        if not isinstance(step, dict):
            raise TypeError(f"step {idx} must be a dict")
        consumer_now_epoch = step.get("consumer_now_epoch")
        allowed_sources = step.get("allowed_sources")
        tamper_packet_hash = step.get("tamper_packet_hash")
        tamper_signature = step.get("tamper_signature")
        if not isinstance(consumer_now_epoch, int):
            raise TypeError(f"step {idx}.consumer_now_epoch must be an int")
        if not isinstance(allowed_sources, list) or not all(isinstance(item, str) for item in allowed_sources):
            raise TypeError(f"step {idx}.allowed_sources must be a list[str]")
        if not isinstance(tamper_packet_hash, bool):
            raise TypeError(f"step {idx}.tamper_packet_hash must be a bool")
        if not isinstance(tamper_signature, bool):
            raise TypeError(f"step {idx}.tamper_signature must be a bool")

        attestation_payload = copy.deepcopy(POLICY_ATTESTATION_PAYLOAD)
        if tamper_packet_hash:
            attestation_payload["packet_hash"] = "0x" + "00" * 32
        if tamper_signature:
            attestation_payload["signature"] = "0x" + "11" * 96
        ok, err = _verify_payload(
            attestation_payload=attestation_payload,
            consumer_now_epoch=consumer_now_epoch,
            allowed_sources=allowed_sources,
            attestation_mode=attestation_mode,
        )
        if not ok:
            return f"reject:step={idx}:{err}"
    return f"ok:steps={len(steps)}:{attestation_mode}"


def _expandable(payload: object) -> bool:
    return isinstance(payload, dict) and isinstance(payload.get("steps"), list)


def _payload_steps(payload: object) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    out = cast(dict[str, Any], copy.deepcopy(payload))
    steps = cast(list[dict[str, Any]], out["steps"])
    return out, steps


def _stale_second_step(payload: object) -> object:
    out, steps = _payload_steps(payload)
    steps[1]["consumer_now_epoch"] = 107
    return out


def _narrow_allowlist(payload: object) -> object:
    out, steps = _payload_steps(payload)
    steps[1]["allowed_sources"] = ["oracle:a"]
    return out


def _tamper_second_step_hash(payload: object) -> object:
    out, steps = _payload_steps(payload)
    steps[1]["tamper_packet_hash"] = True
    return out


def _tamper_second_step_signature(payload: object) -> object:
    out, steps = _payload_steps(payload)
    steps[1]["tamper_signature"] = True
    return out


def _future_second_step(payload: object) -> object:
    out, steps = _payload_steps(payload)
    steps[1]["consumer_now_epoch"] = 99
    return out


MUTATIONS: tuple[Mutation, ...] = (
    Mutation(name="stale_second_step", apply=_stale_second_step),
    Mutation(name="narrow_allowlist", apply=_narrow_allowlist),
    Mutation(name="tamper_second_step_hash", apply=_tamper_second_step_hash),
    Mutation(name="tamper_second_step_signature", apply=_tamper_second_step_signature),
    Mutation(name="future_second_step", apply=_future_second_step),
)
DERIVATION_BUILDERS: dict[str, Callable[[], object]] = {
    "valid_seed": _seed_payload,
    "stale_second_step": lambda: _stale_second_step(_seed_payload()),
    "narrow_allowlist": lambda: _narrow_allowlist(_seed_payload()),
    "tamper_second_step_hash": lambda: _tamper_second_step_hash(_seed_payload()),
    "tamper_second_step_signature": lambda: _tamper_second_step_signature(_seed_payload()),
    "future_second_step": lambda: _future_second_step(_seed_payload()),
}


def _payload_size(payload: object) -> int:
    return len(json.dumps(stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True))


def minimize_case(derivation: str, *, attestation_mode: AttestationMode = "policy") -> MinimizedWitness:
    if derivation not in DERIVATION_BUILDERS:
        raise KeyError(f"unknown derivation: {derivation}")
    if not _mode_supported(attestation_mode):
        raise RuntimeError("py_ecc unavailable")
    payload = DERIVATION_BUILDERS[derivation]()
    outcome_label, path_id, path_length, _ = _trace(payload, attestation_mode=attestation_mode)
    size = _payload_size(payload)
    return MinimizedWitness(
        target="settlement_attestation_sequence",
        derivation=derivation,
        attestation_mode=attestation_mode,
        outcome_label=outcome_label,
        path_id=path_id,
        path_length=path_length,
        original_size=size,
        minimized_size=size,
        payload=payload,
    )


def explore_target(
    name: str = "settlement_attestation_sequence",
    *,
    max_depth: int = 2,
    max_frontier: int = 64,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
    attestation_mode: AttestationMode = "policy",
):
    if name != "settlement_attestation_sequence":
        raise KeyError(f"unknown target: {name}")
    if not _mode_supported(attestation_mode):
        raise RuntimeError("py_ecc unavailable")
    dangerous_surfaces = load_dangerous_surface_manifest(target_manifest)
    semantic_state_fn = settlement_attestation_semantic_state(attestation_mode)
    return explore_bounded_frontier(
        harness_id="settlement_attestation_sequence:settlement_attestation_sequence",
        seed=_seed_payload(),
        mutations=MUTATIONS,
        trace_fn=lambda payload: _trace(payload, attestation_mode=attestation_mode),
        expandable=_expandable,
        max_depth=max_depth,
        max_frontier=max_frontier,
        feedback_mode=feedback_mode,
        dangerous_surfaces=dangerous_surfaces,
        target_id=target_id,
        semantic_state_fn=semantic_state_fn,
        action_summary_fn=lambda prev_payload, next_payload, mutation_name: sequence_action_summary(
            semantic_state_fn,
            prev_payload,
            next_payload,
            mutation_name,
        ),
    )


def explore_all_targets(
    *,
    max_depth: int = 2,
    max_frontier: int = 64,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
    attestation_mode: AttestationMode = "policy",
):
    if not _mode_supported(attestation_mode):
        return ()
    return (
        explore_target(
            max_depth=max_depth,
            max_frontier=max_frontier,
            target_manifest=target_manifest,
            target_id=target_id,
            feedback_mode=feedback_mode,
            attestation_mode=attestation_mode,
        ),
    )


def _reports_json(reports: Sequence[ExplorationTargetReport], *, attestation_mode: AttestationMode) -> dict[str, Any]:
    return {
        "schema": "zenodex/settlement-attestation-sequence-grammar-fuzz/v1",
        "attestation_mode": attestation_mode,
        "supported": _mode_supported(attestation_mode),
        "reports": [report_to_json(report) for report in reports],
    }


def _minimized_witness_json(witness: MinimizedWitness) -> dict[str, Any]:
    return {
        "schema": "zenodex/settlement-attestation-sequence-minimized-witness/v1",
        "witness": {
            **asdict(witness),
            "payload": stable_jsonable(witness.payload),
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default="settlement_attestation_sequence", choices=("settlement_attestation_sequence",))
    parser.add_argument("--format", default="json", choices=("json", "text"))
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--max-frontier", type=int, default=64)
    parser.add_argument("--target-manifest")
    parser.add_argument("--target-id")
    parser.add_argument("--feedback-mode", choices=("legacy", "stateful"), default="stateful")
    parser.add_argument("--attestation-mode", choices=("policy", "full"), default="policy")
    parser.add_argument("--minimize-derivation", choices=tuple(DERIVATION_BUILDERS))
    args = parser.parse_args(list(argv) if argv is not None else None)
    attestation_mode = cast(AttestationMode, args.attestation_mode)

    if not _mode_supported(attestation_mode):
        if args.format == "json":
            print(json.dumps(_reports_json((), attestation_mode=attestation_mode), indent=2, sort_keys=True))
            return 0
        print(f"[settlement_attestation_sequence] unsupported:{attestation_mode}")
        return 0

    if args.minimize_derivation is not None:
        witness = minimize_case(args.minimize_derivation, attestation_mode=attestation_mode)
        if args.format == "json":
            print(json.dumps(_minimized_witness_json(witness), indent=2, sort_keys=True))
            return 0
        print(
            f"[{witness.target}] {witness.derivation}:{witness.attestation_mode} "
            f"{witness.outcome_label} ({witness.path_id}, len={witness.path_length})"
        )
        return 0

    reports = explore_all_targets(
        max_depth=args.max_depth,
        max_frontier=args.max_frontier,
        target_manifest=args.target_manifest,
        target_id=args.target_id,
        feedback_mode=args.feedback_mode,
        attestation_mode=attestation_mode,
    )
    if args.format == "json":
        print(json.dumps(_reports_json(reports, attestation_mode=attestation_mode), indent=2, sort_keys=True))
        return 0
    for report in reports:
        print(
            f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} "
            f"paths={report.unique_path_count} states={report.unique_state_count} transitions={report.unique_transition_count}"
        )
        if report.reached_target_ids:
            print(f"  targets: {', '.join(report.reached_target_ids)}")
        for case in report.cases:
            print(f"  - depth={case.depth} {case.mutation}: {case.outcome_label} path={case.path_id} len={case.path_length}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
