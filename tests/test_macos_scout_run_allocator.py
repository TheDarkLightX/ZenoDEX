from __future__ import annotations

import os
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def _allocate_once(run_root: Path) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["MACOS_SCOUT_RUN_ROOT"] = str(run_root)
    env["MACOS_SCOUT_ALLOCATE_ONLY"] = "1"
    return subprocess.run(
        ["bash", "tools/macos_scout/run_macos_scout.sh", "smoke"],
        cwd=ROOT,
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )


def test_run_macos_scout_allocates_unique_dirs_for_parallel_launches(tmp_path: Path) -> None:
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(lambda _: _allocate_once(tmp_path), range(2)))

    assert all(result.returncode == 0 for result in results), "\n".join(
        result.stdout + result.stderr for result in results
    )
    paths = [Path(result.stdout.strip()) for result in results]
    assert len(set(paths)) == 2
    assert all(path.exists() and path.is_dir() for path in paths)
