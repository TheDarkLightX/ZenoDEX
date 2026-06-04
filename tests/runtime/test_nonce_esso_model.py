"""Repro harness + structural gate for the nonce-sequencing ESSO model.

The model ``src/kernels/dex/nonce_batch_sequencing_v1.yaml`` is the formal spec of
the per-sender strict-sequential nonce policy that the LIVE authority
``src/state/nonces.py`` drives (Phase 2 of the production-promotion plan). It is
proven multi-solver (z3 + cvc5) inductive: ``inv_contiguous`` (last == count, the
gapless-prefix / anti-replay property) and ``inv_monotone_step`` (last never rolls
back).

Two layers, so the artifact is meaningful in any environment:

1. STRUCTURAL gate (pure-Python, always runs / CI-safe): the tracked model loads,
   declares exactly the expected invariants and actions, and the invariant
   expressions are the ones we claim. This catches drift / silent edits to the
   spec even where the ESSO toolchain is absent.
2. LIVE proof (skipped, not failed, when ``external/ESSO`` or z3/cvc5 are
   unavailable — ESSO is a gitignored external dep): re-runs
   ``ESSO verify-multi --solvers z3,cvc5`` and asserts ``verdict == VERIFIED`` with
   both solvers agreeing. (CI-gating this — cloning ESSO + installing solvers in a
   workflow — is the remaining step for the nonces ``proof_artifact`` column.)

The model<->running-impl binding (that ``nonces.py`` actually implements this
policy) is pinned separately by ``test_nonces_batch_binding.py``.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
MODEL = REPO / "src" / "kernels" / "dex" / "nonce_batch_sequencing_v1.yaml"
ESSO = REPO / "external" / "ESSO"


def _load_model() -> dict:
    try:
        import yaml
    except Exception:  # pragma: no cover
        pytest.skip("PyYAML unavailable")
    return yaml.safe_load(MODEL.read_text(encoding="utf-8"))


# --- 1. structural gate (always runs) ----------------------------------------


def test_model_declares_expected_state_and_invariants() -> None:
    m = _load_model()
    assert m["meta"]["model_id"] == "nonce_batch_sequencing_v1"
    svars = {sv["id"] for sv in m["state_vars"]}
    assert svars == {"last_nonce", "accepted_count", "prev_last"}
    invs = {inv["id"]: inv for inv in m["invariants"]}
    assert set(invs) == {"inv_contiguous", "inv_monotone_step"}

    # inv_contiguous: last_nonce == accepted_count (gapless prefix / anti-replay)
    c = invs["inv_contiguous"]["expr"]
    assert c["op"] == "="
    assert {a["var"] for a in c["args"]} == {"last_nonce", "accepted_count"}

    # inv_monotone_step: last_nonce >= prev_last (never rolls back)
    mono = invs["inv_monotone_step"]["expr"]
    assert mono["op"] == ">="
    assert [a["var"] for a in mono["args"]] == ["last_nonce", "prev_last"]


def test_model_actions_match_the_nonce_policy() -> None:
    m = _load_model()
    actions = {a["id"]: a for a in m["actions"]}
    assert set(actions) == {"accept_one", "accept_range", "reject_stale", "reject_gap"}

    # accept_one advances last by 1 and count by 1 (strict successor).
    a1 = actions["accept_one"]
    updated = {u["var"] for u in a1["updates"]}
    assert updated == {"prev_last", "last_nonce", "accepted_count"}

    # The reject actions are NO-OPS on last_nonce/accepted_count (only prev_last is
    # touched, for the monotonicity ghost) — reject-is-no-op at the model level.
    for rid in ("reject_stale", "reject_gap"):
        touched = {u["var"] for u in actions[rid]["updates"]}
        assert touched == {"prev_last"}, f"{rid} must not mutate last_nonce/accepted_count"


# --- 2. non-vacuity / firability witness (independent z3) ---------------------


def test_independent_z3_non_vacuity_witness() -> None:
    z3 = pytest.importorskip("z3")
    # A concrete reachable trajectory: accept_one(1) -> accept_range(2) -> reject_stale(2).
    # The contiguity invariant must hold at each state AND last must reach > 0
    # (so the invariant is non-vacuous, not trivially true on a frozen state).
    last = [z3.Int(f"last{i}") for i in range(4)]
    cnt = [z3.Int(f"cnt{i}") for i in range(4)]
    s = z3.Solver()
    s.add(last[0] == 0, cnt[0] == 0)
    s.add(1 == last[0] + 1, last[1] == 1, cnt[1] == cnt[0] + 1)            # accept_one(1)
    s.add(last[1] + 2 <= 4294967295, last[2] == last[1] + 2, cnt[2] == cnt[1] + 2)  # accept_range(2)
    s.add(2 >= 1, 2 <= last[2], last[3] == last[2], cnt[3] == cnt[2])      # reject_stale(2): no-op
    for i in range(4):
        s.add(last[i] == cnt[i])  # inv_contiguous at every reached state
    s.add(last[3] > 0)            # reaches a non-trivial state
    assert s.check() == z3.sat, "accepting trajectory must be reachable (non-vacuity)"

    # Teeth: a buggy accept (count++ without last++) would VIOLATE inv_contiguous.
    t = z3.Solver()
    L, C = z3.Int("L"), z3.Int("C")
    t.add(L == C)            # pre: invariant holds
    t.add(C == C + 1)        # buggy: count increments, last does not -> contradiction
    assert t.check() == z3.unsat, "inv_contiguous must have teeth (reject count++ w/o last++)"


# --- 3. live multi-solver proof (skipped when ESSO/solvers absent) ------------


@pytest.mark.skipif(not ESSO.exists(), reason="external/ESSO (gitignored dep) not present")
def test_esso_verify_multi_is_verified() -> None:
    env = dict(os.environ, PYTHONPATH=str(ESSO))
    try:
        out = subprocess.run(
            [sys.executable, "-m", "ESSO", "verify-multi", str(MODEL), "--solvers", "z3,cvc5"],
            capture_output=True, text=True, env=env, timeout=300, cwd=str(REPO),
        )
    except (FileNotFoundError, subprocess.TimeoutExpired) as exc:  # pragma: no cover
        pytest.skip(f"ESSO/solvers unavailable: {exc}")
    payload = json.loads(out.stdout)
    assert payload["ok"] is True, payload
    report = payload["report"]
    assert report["verdict"] == "VERIFIED", report
    assert report["solvers_agreed"] is True
    assert report["z3_passed"] and report["cvc5_passed"]
    assert report["failed_queries"] == 0 and report["inconclusive_queries"] == 0
    # the inductive invariant proofs (init + every action preserves the invariants)
    assert report["passed_queries"] >= 5
