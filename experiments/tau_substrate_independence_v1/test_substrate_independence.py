"""Conformance tests for ZenoDEX substrate independence (Tau-failure resilience).

Run: ``PYTHONPATH=<repo-root> pytest experiments/tau_substrate_independence_v1/``

Proves, with the REAL core, that validity is substrate-independent and that the
functional core's import graph is Tau-free (the anti-bitrot CI guard).
"""

from __future__ import annotations

import os
import subprocess
import sys

from substrate_independence import (
    LocalSequencerSubstrate,
    NaiveSubmissionSubstrate,
    Swap,
    TauCheckpointSubstrate,
    canonical_order,
    demo_pool,
    settle_root,
    settle_via,
)

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

# A batch whose submission order differs from the canonical order (so order is
# observable): canonical key is (amount_in, direction, trader).
BATCH = [Swap("z-trader", 0, 50_000), Swap("a-trader", 1, 9_000), Swap("m-trader", 0, 1_000)]


# --- The load-bearing guard: the functional core has ZERO Tau coupling --------

def test_core_import_graph_is_tau_free():
    """Importing the real settlement core must pull NO ZenoDEX Tau module.

    Run in a clean subprocess so the result is the core's true transitive import
    graph, not contaminated by this test session. This is the CI anti-bitrot
    guard for the 'validity is Tau-independent' resilience property.
    """
    code = (
        "import sys\n"
        "for m in ['src.core.batch_clearing','src.core.settlement_strong_validator',"
        "'src.core.cpmm','src.state.state_root','src.state.balances','src.state.pools']:\n"
        "    __import__(m)\n"
        "tau=[k for k in sys.modules if 'tau' in k.lower()]\n"
        "print('TAU:'+','.join(sorted(tau)))\n"
    )
    env = dict(os.environ, PYTHONPATH=REPO_ROOT)
    proc = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, cwd=REPO_ROOT, env=env
    )
    assert proc.returncode == 0, proc.stderr
    tau_line = next(l for l in proc.stdout.splitlines() if l.startswith("TAU:"))
    pulled = tau_line[len("TAU:"):].strip()
    assert pulled == "", f"functional core import graph pulled Tau modules: {pulled}"


def test_harness_does_not_load_zenodex_tau_shell():
    # Settling through the harness must not import the ZenoDEX Tau shell.
    settle_via(LocalSequencerSubstrate(), demo_pool(), BATCH)
    shell = [m for m in sys.modules if "integration.tau" in m or m.endswith("tau_gate") or m.endswith("tau_runner")]
    assert shell == [], f"settlement loaded the Tau shell: {shell}"


# --- Validity is a pure function of (pre_state, canonical batch) ---------------

def test_validity_is_substrate_independent_under_canonical_order():
    pool = demo_pool()
    local_root = settle_via(LocalSequencerSubstrate(), pool, BATCH)
    tau_root = settle_via(TauCheckpointSubstrate(), pool, BATCH)
    # Two distinct substrates, same canonical order → byte-identical validity root.
    assert local_root == tau_root
    assert local_root.startswith("0x") and len(local_root) == 66


def test_settlement_is_deterministic_replay():
    pool = demo_pool()
    runs = {settle_via(LocalSequencerSubstrate(), pool, BATCH) for _ in range(5)}
    assert len(runs) == 1  # pure function: identical every time


def test_substrate_independence_holds_under_input_reordering():
    # The substrate receiving the batch in a different submission order still
    # produces the same root, because it canonicalizes first.
    pool = demo_pool()
    r1 = settle_via(TauCheckpointSubstrate(), pool, BATCH)
    r2 = settle_via(TauCheckpointSubstrate(), pool, list(reversed(BATCH)))
    assert r1 == r2


# --- Why canonical ordering is required (the requirement is non-vacuous) -------

def test_canonical_order_is_required_for_portability():
    """A non-canonical (raw submission-order) substrate yields a DIFFERENT root,
    proving portability depends on the canonical order — which is exactly why a
    deterministic/grinding-resistant tie-break (neutral_tiebreak_v1) is load-bearing."""
    pool = demo_pool()
    canonical_root = settle_via(LocalSequencerSubstrate(), pool, BATCH)
    naive_root = settle_root(pool, NaiveSubmissionSubstrate().provide_order(BATCH))
    # Sanity: the chosen batch is genuinely non-canonical (submission != canonical).
    assert list(BATCH) != canonical_order(BATCH)
    assert naive_root != canonical_root
