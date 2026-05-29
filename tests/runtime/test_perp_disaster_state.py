"""Perps E2 fuzz + disaster-state differential gate (promotion criterion 4 + fuzz).

High-volume randomized differential across every shadowed isolated-perps op,
driving the REAL Python authority (`apply_perp_ops`) and comparing the Rust
shadow case-for-case (accept/reject + reject-code + post-state). The randomized
distributions straddle every parameter bound (zero, max-domain, off-by-one,
over-domain), so this doubles as the input-disaster-state evidence
(malformed/out-of-domain, overflow/underflow, no-op-on-reject — a rejected case
returns no Rust output and leaves the Python state untouched, which the diff
asserts via accept/reject agreement).

This is *evidence*, not promotion: every surface remains `python_authority`.
The selector fail-closed disaster rows (Rust-timeout / malformed-Rust-output)
require wiring the Rust core into the live authority selector and are tracked in
`RUST_AUTHORITY_MIGRATION_STATUS.md`, not here.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
for _p in (str(_REPO), str(_REPO / "tools" / "runtime")):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from tools.runtime import perp_account_ops_lib as acct  # noqa: E402
from tools.runtime import perp_advance_epoch_lib as adv  # noqa: E402
from tools.runtime import perp_funding_auto_lib as fund  # noqa: E402
from tools.runtime import perp_partial_liquidate_lib as plq  # noqa: E402
from tools.runtime import perp_publish_clearing_price_lib as pub  # noqa: E402
from tools.runtime import perp_set_market_params_lib as smp  # noqa: E402
from tools.runtime import perp_settle_epoch_lib as settle  # noqa: E402
from src.runtime.authority import AuthorityError, AuthorityMode, RustUnavailable, decide  # noqa: E402

# Each shadowed isolated-perps op: (label, lib, expect_rejects).
OP_LIBS = [
    ("advance_epoch", adv, True),
    ("publish_clearing_price", pub, True),
    ("apply_funding_auto", fund, False),
    ("settle_epoch", settle, False),
    ("partial_liquidate", plq, True),
    ("account_ops", acct, True),
    ("set_market_params", smp, True),
]

# Fuzz volume per op (4 seeds x 60 = 240 >= the gate's >=400 cumulative with the
# per-op conformance's 120; keep it bounded so the suite stays a few seconds).
_SEEDS = (101, 102, 103, 104)
_N = 60


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return adv.locate_or_build_cli()
    except adv.AdvanceEpochShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


@pytest.mark.parametrize(
    "label,lib,expect_rejects",
    OP_LIBS,
    ids=[label for label, _, _ in OP_LIBS],
)
def test_fuzz_differential(label, lib, expect_rejects, rust_bin):
    cases: list[dict] = []
    for seed in _SEEDS:
        cases.extend(lib.randomized_cases(seed=seed, n=_N))
    assert len(cases) >= 200, f"{label}: insufficient fuzz volume"

    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, py)
    problems = lib.diff_results(py, rs)
    assert not problems, (
        f"{label} fuzz/disaster mismatch ({len(problems)} of {len(cases)}):\n"
        + "\n".join(problems[:20])
    )

    # Non-vacuity: the op actually does something, and (where its domain spans
    # rejects) the disaster/over-bound inputs are exercised.
    assert any(p["ok"] for p in py), f"{label}: fuzz produced no accepts"
    if expect_rejects:
        assert any(not p["ok"] for p in py), f"{label}: fuzz produced no rejects"


def _selector_cases(label: str, lib) -> list[dict]:
    return lib.randomized_cases(seed=20260529 + len(label), n=8)


def _compare_with(lib):
    def compare(py_results, rust_results) -> bool:
        return not lib.diff_results(py_results, rust_results)

    return compare


@pytest.mark.parametrize("label,lib,_expect_rejects", OP_LIBS, ids=[label for label, _, _ in OP_LIBS])
def test_selector_rust_authority_with_python_shadow_agrees_for_perps(label, lib, _expect_rejects, rust_bin):
    """Test-only selector exercise: Rust decides, Python shadows, no production profile flips."""
    cases = _selector_cases(label, lib)
    py = lib.py_eval_all(cases)
    d = decide(
        f"perps_e2:{label}",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=lambda: py,
        rust_fn=lambda: lib.run_rust(rust_bin, py),
        compare=_compare_with(lib),
    )
    assert d.authority == "rust"
    assert d.shadow_checked is True
    assert d.agreed is True


@pytest.mark.parametrize("label,lib,_expect_rejects", OP_LIBS, ids=[label for label, _, _ in OP_LIBS])
def test_selector_fails_closed_on_injected_perps_disagreement(label, lib, _expect_rejects, rust_bin):
    cases = _selector_cases(label, lib)
    py = lib.py_eval_all(cases)

    def tampered_rust():
        out = lib.run_rust(rust_bin, py)
        out[0] = {**out[0], "ok": not bool(out[0].get("ok"))}
        return out

    with pytest.raises(AuthorityError):
        decide(
            f"perps_e2:{label}",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=lambda: py,
            rust_fn=tampered_rust,
            compare=_compare_with(lib),
        )


def test_selector_fails_closed_on_malformed_perps_rust_output(rust_bin):
    label, lib, _ = OP_LIBS[0]
    cases = _selector_cases(label, lib)
    py = lib.py_eval_all(cases)

    with pytest.raises(AuthorityError):
        decide(
            f"perps_e2:{label}",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=lambda: py,
            rust_fn=lambda: [],
            compare=_compare_with(lib),
        )


def test_selector_fails_closed_when_perps_rust_unavailable_under_authority():
    label, lib, _ = OP_LIBS[0]
    cases = _selector_cases(label, lib)
    py = lib.py_eval_all(cases)

    def rust_missing():
        raise RustUnavailable("perps runtime not built")

    with pytest.raises(AuthorityError):
        decide(
            f"perps_e2:{label}",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=lambda: py,
            rust_fn=rust_missing,
            compare=_compare_with(lib),
        )
