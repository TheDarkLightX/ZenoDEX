#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
OUT_PATH = ROOT / "generated" / "acceptance_tcb_mutation_harness.json"


@dataclass(frozen=True)
class TextMutant:
    mutant_id: str
    description: str
    target_rel_path: str
    needle: str
    replacement: str
    test_cmd: Sequence[str]


MUTANTS: tuple[TextMutant, ...] = (
    TextMutant(
        mutant_id="nonces_disable_mixed_presence_reject",
        description="Allow batches that mix nonce-bearing and nonce-free intents.",
        target_rel_path="src/state/nonces.py",
        needle='    if saw_nonce and saw_missing:\n        return False, "nonce presence must be consistent across batch", None\n',
        replacement='    if False and saw_nonce and saw_missing:\n        return False, "nonce presence must be consistent across batch", None\n',
        test_cmd=[
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "tests/integration/test_replay_protection.py",
            "tests/state/test_nonces.py",
        ],
    ),
    TextMutant(
        mutant_id="nonces_disable_missing_nonce_reject",
        description="Allow nonce-free intents through the strict replay-protection path.",
        target_rel_path="src/state/nonces.py",
        needle="            if require_all_nonces:\n                return False, \"Missing/invalid nonce\", None\n",
        replacement="            if False and require_all_nonces:\n                return False, \"Missing/invalid nonce\", None\n",
        test_cmd=[
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "tests/integration/test_replay_protection.py",
            "tests/state/test_nonces.py",
        ],
    ),
    TextMutant(
        mutant_id="dex_disable_missing_quote_witness_reject",
        description="Allow quote-bound intents with no attached quote receipt witness.",
        target_rel_path="src/integration/dex_engine.py",
        needle="        if quote_hash is not None and receipt is None:\n",
        replacement="        if False and quote_hash is not None and receipt is None:\n",
        test_cmd=[
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "tests/integration/test_dex_engine.py",
            "tests/integration/test_dex_engine_anomaly.py",
            "tests/integration/test_quote_receipt_intents.py",
        ],
    ),
    TextMutant(
        mutant_id="dex_disable_settlement_match_reject",
        description="Accept mismatched provided settlements instead of failing closed.",
        target_rel_path="src/integration/dex_engine.py",
        needle="                if got != expected:\n                    return DexTxResult(ok=False, error=\"settlement mismatch\")\n",
        replacement="                if False and got != expected:\n                    return DexTxResult(ok=False, error=\"settlement mismatch\")\n",
        test_cmd=[
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "tests/integration/test_dex_engine.py",
            "tests/integration/test_validation_uses_strong_settlement_gate.py",
        ],
    ),
    TextMutant(
        mutant_id="dex_disable_proof_pre_state_binding",
        description="Allow proofs whose pre_state_commitment does not match local state.",
        target_rel_path="src/integration/dex_engine.py",
        needle='    if proof_pre != pre_state_commitment:\n        return False, "proof pre_state_commitment mismatch"\n',
        replacement='    if False and proof_pre != pre_state_commitment:\n        return False, "proof pre_state_commitment mismatch"\n',
        test_cmd=[
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "tests/integration/test_proof_verifier.py",
            "tests/integration/test_dex_engine_helpers.py",
        ],
    ),
    TextMutant(
        mutant_id="strong_validator_allow_snapshot_binding_without_opt_in",
        description="Allow snapshot-bound quote bindings without the engine opt-in path.",
        target_rel_path="src/core/settlement_strong_validator.py",
        needle="        if quote_pool_fp is not None and not allow_snapshot_bound_quote_bindings:\n",
        replacement="        if False and quote_pool_fp is not None and not allow_snapshot_bound_quote_bindings:\n",
        test_cmd=[
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "tests/core/test_settlement_strong_validator.py",
            "tests/integration/test_validation_uses_strong_settlement_gate.py",
        ],
    ),
    TextMutant(
        mutant_id="strong_validator_allow_missing_pool",
        description="Proceed past a missing pool instead of failing closed.",
        target_rel_path="src/core/settlement_strong_validator.py",
        needle="        if pool_id not in pools:\n            return fail(f\"pool not found for intent_id={intent_id}: {pool_id}\")\n",
        replacement="        if False and pool_id not in pools:\n            return fail(f\"pool not found for intent_id={intent_id}: {pool_id}\")\n",
        test_cmd=[
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "tests/core/test_settlement_strong_validator.py",
        ],
    ),
)


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _run_tests(cmd: Sequence[str]) -> tuple[int, str, str, float]:
    t0 = time.time()
    proc = subprocess.run(cmd, cwd=str(ROOT), text=True, capture_output=True)
    return int(proc.returncode), str(proc.stdout), str(proc.stderr), float(time.time() - t0)


def main() -> int:
    originals: dict[Path, str] = {}
    rows: list[dict[str, Any]] = []
    try:
        for mutant in MUTANTS:
            target = ROOT / mutant.target_rel_path
            original = originals.setdefault(target, target.read_text(encoding="utf-8"))
            if mutant.needle not in original:
                rows.append(
                    {
                        "mutant_id": mutant.mutant_id,
                        "description": mutant.description,
                        "target": mutant.target_rel_path,
                        "status": "inconclusive",
                        "reason": "needle_not_found",
                    }
                )
                continue

            mutated = original.replace(mutant.needle, mutant.replacement, 1)
            target.write_text(mutated, encoding="utf-8")
            rc, stdout, stderr, duration_s = _run_tests(mutant.test_cmd)
            rows.append(
                {
                    "mutant_id": mutant.mutant_id,
                    "description": mutant.description,
                    "target": mutant.target_rel_path,
                    "test_cmd": list(mutant.test_cmd),
                    "status": "killed" if rc != 0 else "survived",
                    "duration_s": duration_s,
                    "rc": rc,
                    "stdout_tail": stdout[-2000:],
                    "stderr_tail": stderr[-2000:],
                }
            )
            target.write_text(original, encoding="utf-8")
    finally:
        for target, original in originals.items():
            target.write_text(original, encoding="utf-8")

    killed = sum(1 for row in rows if row.get("status") == "killed")
    survived = sum(1 for row in rows if row.get("status") == "survived")
    inconclusive = sum(1 for row in rows if row.get("status") == "inconclusive")
    out = {
        "schema": "zenodex/acceptance-tcb-mutation-harness/v1",
        "totals": {
            "killed": killed,
            "survived": survived,
            "inconclusive": inconclusive,
            "mutation_score": 0.0 if killed + survived == 0 else float(killed) / float(killed + survived),
        },
        "rows": rows,
    }
    _write_json(OUT_PATH, out)
    print(json.dumps({"ok": survived == 0, "out": str(OUT_PATH), "totals": out["totals"]}, sort_keys=True))
    return 0 if survived == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
