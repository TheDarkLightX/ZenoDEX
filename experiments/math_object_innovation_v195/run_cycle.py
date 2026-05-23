#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated"

ATOMS: tuple[str, ...] = (
    "domain_ok",
    "surface_binding_ok",
    "cap_reference_ok",
    "assumption_nonce_fresh",
    "signer_threshold_ok",
    "registry_root_ok",
    "epoch_freshness_ok",
    "no_user_net_ack_ok",
)


def packet(packet_id: str, *, fail: tuple[str, ...] = ()) -> dict[str, object]:
    failed = set(fail)
    atoms = {atom: atom not in failed for atom in ATOMS}
    return {
        "packet_id": packet_id,
        **atoms,
        "expected_good": not failed,
        "failed_atoms": sorted(failed),
    }


PACKETS: tuple[dict[str, object], ...] = (
    packet("valid_route_override"),
    packet("valid_uncapped_surface_override"),
    packet("wrong_domain_bad", fail=("domain_ok",)),
    packet("surface_mismatch_bad", fail=("surface_binding_ok",)),
    packet("stale_cap_reference_bad", fail=("cap_reference_ok",)),
    packet("replayed_assumption_id_bad", fail=("assumption_nonce_fresh",)),
    packet("threshold_drift_bad", fail=("signer_threshold_ok",)),
    packet("registry_root_drift_bad", fail=("registry_root_ok",)),
    packet("expired_override_bad", fail=("epoch_freshness_ok",)),
    packet("missing_ack_bad", fail=("no_user_net_ack_ok",)),
    packet("text_right_but_no_authority_bad", fail=("signer_threshold_ok", "registry_root_ok")),
    packet("fresh_signature_wrong_cap_bad", fail=("cap_reference_ok",)),
    packet("fresh_cap_wrong_surface_bad", fail=("surface_binding_ok",)),
)

NAMED_LANGUAGES: dict[str, tuple[str, ...]] = {
    "text_only": ("domain_ok", "surface_binding_ok", "cap_reference_ok", "no_user_net_ack_ok"),
    "authority_only": ("signer_threshold_ok", "registry_root_ok"),
    "fresh_authority_only": ("assumption_nonce_fresh", "signer_threshold_ok", "registry_root_ok", "epoch_freshness_ok"),
    "cap_and_ack_only": ("surface_binding_ok", "cap_reference_ok", "no_user_net_ack_ok"),
    "full_override_packet_guard": ATOMS,
}


def accepts(row: dict[str, object], atoms: tuple[str, ...]) -> bool:
    return all(bool(row[atom]) for atom in atoms)


def language_stats(atoms: tuple[str, ...]) -> dict[str, object]:
    false_accepts = []
    false_rejects = []
    for row in PACKETS:
        accepted = accepts(row, atoms)
        expected = bool(row["expected_good"])
        if accepted and not expected:
            false_accepts.append(row["packet_id"])
        if expected and not accepted:
            false_rejects.append(row["packet_id"])
    return {
        "atoms": list(atoms),
        "atom_count": len(atoms),
        "false_accept_count": len(false_accepts),
        "false_reject_count": len(false_rejects),
        "false_accepts": false_accepts,
        "false_rejects": false_rejects,
        "exact": not false_accepts and not false_rejects,
    }


def private_witnesses() -> dict[str, str | None]:
    witnesses: dict[str, str | None] = {}
    for atom in ATOMS:
        witness = None
        for row in PACKETS:
            failed_atoms = row["failed_atoms"]
            if failed_atoms == [atom]:
                witness = str(row["packet_id"])
                break
        witnesses[atom] = witness
    return witnesses


def find_exact_languages() -> list[dict[str, object]]:
    exact: list[dict[str, object]] = []
    for size in range(len(ATOMS) + 1):
        for subset in itertools.combinations(ATOMS, size):
            stats = language_stats(tuple(subset))
            if stats["exact"]:
                exact.append(stats)
        if exact:
            break
    return exact


def run_cycle() -> dict[str, object]:
    GENERATED.mkdir(parents=True, exist_ok=True)
    exact_languages = find_exact_languages()
    witnesses = private_witnesses()
    named_language_stats = {
        name: language_stats(atoms)
        for name, atoms in NAMED_LANGUAGES.items()
    }
    forced_atoms = sorted(atom for atom, witness in witnesses.items() if witness is not None)
    total_invariant_failures = (
        sum(1 for atom in ATOMS if witnesses.get(atom) is None)
        + (0 if exact_languages else 1)
        + sum(1 for language in exact_languages if set(language["atoms"]) != set(ATOMS))
        + (0 if named_language_stats["full_override_packet_guard"]["exact"] else 1)
    )
    report = {
        "schema": "zenodex/math-object-innovation-v195-report/v1",
        "object": "assumption_change_override_packet_language_v1",
        "tier": "symbolic_state_compiler",
        "oracle_dependent": True,
        "discovery_domain": {
            "packet_count": len(PACKETS),
            "atom_count": len(ATOMS),
            "atoms": list(ATOMS),
        },
        "holdout_domain": "none; bounded adversarial override-packet corpus",
        "packet_count": len(PACKETS),
        "valid_packet_count": sum(1 for row in PACKETS if row["expected_good"]),
        "invalid_packet_count": sum(1 for row in PACKETS if not row["expected_good"]),
        "atom_count": len(ATOMS),
        "forced_atom_count": len(forced_atoms),
        "private_witnesses": witnesses,
        "minimal_exact_language_count": len(exact_languages),
        "minimal_exact_atom_count": exact_languages[0]["atom_count"] if exact_languages else None,
        "minimal_exact_languages": exact_languages,
        "named_language_stats": named_language_stats,
        "packets": list(PACKETS),
        "model_audit": {
            "missing_private_witness_count": sum(1 for atom in ATOMS if witnesses.get(atom) is None),
            "non_full_minimal_exact_language_count": sum(
                1 for language in exact_languages if set(language["atoms"]) != set(ATOMS)
            ),
            "full_guard_false_accept_count": named_language_stats["full_override_packet_guard"]["false_accept_count"],
            "full_guard_false_reject_count": named_language_stats["full_override_packet_guard"]["false_reject_count"],
            "total_override_language_invariant_failures": total_invariant_failures,
        },
        "strongest_claim": (
            "On the bounded adversarial override-packet corpus, every atom in the eight-field "
            "assumption-change language is forced by a private negative witness, and the unique "
            "minimal exact language is the full packet guard."
        ),
        "non_claims": [
            "This is a bounded witness-language result, not a cryptographic signature implementation.",
            "The corpus does not prove all governance override attacks are impossible.",
            "The language still depends on truthful upstream cap and registry roots.",
        ],
    }
    (GENERATED / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (GENERATED / "packets.json").write_text(json.dumps(list(PACKETS), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> int:
    report = run_cycle()
    print(
        json.dumps(
            {
                "packet_count": report["packet_count"],
                "atom_count": report["atom_count"],
                "forced_atom_count": report["forced_atom_count"],
                "minimal_exact_atom_count": report["minimal_exact_atom_count"],
                "minimal_exact_language_count": report["minimal_exact_language_count"],
                "invariant_failures": report["model_audit"]["total_override_language_invariant_failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["model_audit"]["total_override_language_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
