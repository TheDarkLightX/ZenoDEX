from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parents[2]
ESSO_ROOT = ROOT / "external" / "ESSO"

CASES = [
    (
        Path("src/kernels/dex/perp_epoch_isolated_v3.yaml"),
        "src.kernels.python.perp_epoch_isolated_v3_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/perp_epoch_isolated_v4.yaml"),
        "src.kernels.python.perp_epoch_isolated_v4_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml"),
        "src.kernels.python.perp_epoch_clearinghouse_2p_v0_1_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml"),
        "src.kernels.python.perp_epoch_clearinghouse_3p_transfer_v0_1_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/dex_global_conservation_v1.yaml"),
        "src.kernels.python.dex_global_conservation_v1_adapter:make_adapter",
    ),
]


def _esso_env() -> dict[str, str]:
    env = os.environ.copy()
    if ESSO_ROOT.is_dir():
        pythonpath = env.get("PYTHONPATH", "")
        env["PYTHONPATH"] = str(ESSO_ROOT) if not pythonpath else f"{ESSO_ROOT}:{pythonpath}"
    return env


def _require_esso(env: dict[str, str]) -> None:
    proc = subprocess.run(
        [sys.executable, "-c", "import ESSO"],
        env=env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    if proc.returncode != 0:
        pytest.skip("ESSO is not available")


def _load_perp_v3_ir() -> Any:
    if ESSO_ROOT.is_dir() and str(ESSO_ROOT) not in sys.path:
        sys.path.insert(0, str(ESSO_ROOT))
    pytest.importorskip("ESSO")
    yaml = pytest.importorskip("yaml")
    from ESSO.ir.schema import CandidateIR

    obj = yaml.safe_load((ROOT / "src/kernels/dex/perp_epoch_isolated_v3.yaml").read_text(encoding="utf-8"))
    return CandidateIR.from_json_dict(obj).canonicalized()


def _perp_v3_initial_state(ir: Any) -> dict[str, Any]:
    from ESSO.kernel.interpreter import StepError, eval_expr

    state: dict[str, Any] = {}
    for assignment in ir.init:
        value = eval_expr(assignment.expr, state=state, params={}, ir=ir, expected=None)
        assert not isinstance(value, StepError)
        state[assignment.var] = value
    return state


@pytest.mark.parametrize(("model", "adapter"), CASES)
def test_runtime_shell_adapters_shell_lint_and_verify(
    tmp_path: Path,
    model: Path,
    adapter: str,
) -> None:
    env = _esso_env()
    _require_esso(env)
    lint_path = tmp_path / f"{model.stem}_shell_lint.json"
    verify_path = tmp_path / f"{model.stem}_verify_shell.json"

    subprocess.check_call(
        [
            sys.executable,
            "-m",
            "ESSO",
            "shell-lint",
            str(model),
            "--adapter",
            adapter,
            "--output",
            str(lint_path),
        ],
        env=env,
    )
    lint = json.loads(lint_path.read_text(encoding="utf-8"))
    assert lint.get("ok") is True

    subprocess.check_call(
        [
            sys.executable,
            "-m",
            "ESSO",
            "verify-shell",
            str(model),
            "--adapter",
            adapter,
            "--traces",
            "16",
            "--max-steps",
            "8",
            "--determinism-trials",
            "2",
            "--output",
            str(verify_path),
        ],
        env=env,
    )
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True


def test_perp_epoch_isolated_v3_settle_epoch_is_oracle_bound() -> None:
    ir = _load_perp_v3_ir()
    from ESSO.kernel.interpreter import Command, StepError, StepOk, prepare_step_context, step_ctx

    ctx = prepare_step_context(ir)
    assert not isinstance(ctx, StepError)
    base = _perp_v3_initial_state(ir)
    base.update(
        {
            "now_epoch": 5,
            "epoch_phase": 1,
            "clearing_price_seen": True,
            "clearing_price_e8": 100_000_000,
            "clearing_price_epoch": 5,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 100_000_000,
            "max_oracle_staleness_epochs": 10,
        }
    )

    accepted = step_ctx(base, Command("settle_epoch", {}), ctx)
    assert isinstance(accepted, StepOk)

    rejected_cases = {
        "missing_snapshot": {"oracle_seen": False},
        "zero_index": {"index_price_e8": 0},
        "stale_snapshot": {"oracle_last_update_epoch": 0, "max_oracle_staleness_epochs": 2},
        "same_epoch_snapshot": {"oracle_last_update_epoch": 5},
    }
    for patch in rejected_cases.values():
        state = dict(base)
        state.update(patch)
        rejected = step_ctx(state, Command("settle_epoch", {}), ctx)
        assert isinstance(rejected, StepError)
