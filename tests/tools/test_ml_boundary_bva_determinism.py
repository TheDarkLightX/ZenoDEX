from __future__ import annotations

import pytest

from tools.esso_gpu_semantics import ensure_esso_on_path


def _esso_available() -> bool:
    try:
        ensure_esso_on_path()
        import ESSO.kernel.interpreter  # type: ignore  # noqa: F401
    except ModuleNotFoundError:
        return False
    return True


@pytest.mark.skipif(not _esso_available(), reason="ESSO interpreter is not installed")
def test_ml_bva_generation_is_deterministic_for_fixed_seed() -> None:
    from pathlib import Path

    from tools.ml_boundary_bva import generate_ml_bva_suite

    model = Path("src/kernels/dex/cpmm_swap_v8.yaml")
    kwargs = dict(
        model_path=model,
        cases_per_action=6,
        iterations_per_action=80,
        max_candidates_per_action=120,
        max_states=32,
        global_walk_steps=180,
        global_reset_prob=0.2,
        global_baseline_prob=0.4,
        global_top_k_candidates=40,
        refine_pairs_per_action=8,
        refine_max_steps=4,
        alpha=1.35,
        seed=0,
    )

    a = generate_ml_bva_suite(**kwargs)
    b = generate_ml_bva_suite(**kwargs)
    assert a == b

