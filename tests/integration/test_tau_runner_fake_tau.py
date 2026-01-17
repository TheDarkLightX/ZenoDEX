from __future__ import annotations

import stat
from pathlib import Path

from src.integration.tau_runner import run_tau_spec_steps
from src.integration.tau_witness import SWAP_EXACT_IN_V1, build_swap_exact_in_v1_step


def test_run_tau_spec_steps_with_fake_tau(tmp_path: Path) -> None:
    fake_tau = tmp_path / "tau"
    fake_tau.write_text(
        """#!/usr/bin/env python3
import re
import sys
from pathlib import Path

script = sys.stdin.read()
in_paths = re.findall(r'in file\\(\"([^\"]+)\"\\)', script)
out_paths = re.findall(r'out file\\(\"([^\"]+)\"\\)', script)
if not in_paths or not out_paths:
    sys.exit(2)

vals = [ln.strip() for ln in Path(in_paths[0]).read_text(encoding="utf-8").splitlines() if ln.strip()]
n = len(vals)

for p in out_paths:
    Path(p).write_text(\"\".join(\"1\\n\" for _ in range(n)), encoding=\"utf-8\")

sys.exit(0)
""",
        encoding="utf-8",
    )
    fake_tau.chmod(fake_tau.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)

    step = build_swap_exact_in_v1_step(
        reserve_in=100,
        reserve_out=200,
        amount_in=10,
        fee_bps=30,
        min_amount_out=0,
        amount_out=5,
        new_reserve_in=110,
        new_reserve_out=195,
    )

    outputs = run_tau_spec_steps(
        tau_bin=str(fake_tau),
        spec_path=SWAP_EXACT_IN_V1.path,
        steps=[step],
        timeout_s=1.0,
    )
    assert outputs == {0: {"o1": 1}}
