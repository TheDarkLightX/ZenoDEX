from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def test_wes_bridge_runner_invokes_wes_cli(tmp_path, monkeypatch) -> None:
    wes_root = tmp_path / "WitnessEnergySearch"
    wes_pkg = wes_root / "src" / "wes"
    wes_pkg.mkdir(parents=True)
    (wes_pkg / "__init__.py").write_text("", encoding="utf-8")
    argv_path = tmp_path / "argv.json"
    (wes_pkg / "cli.py").write_text(
        "\n".join(
            [
                "import json, os, sys",
                "from pathlib import Path",
                "def main(argv=None):",
                "    Path(os.environ['FAKE_WES_ARGV_OUT']).write_text(json.dumps(argv), encoding='utf-8')",
                "    return 0",
                "if __name__ == '__main__':",
                "    raise SystemExit(main(sys.argv[1:]))",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_WES_ARGV_OUT", str(argv_path))

    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "tools" / "wes" / "run_recompute_batch_v4_bridge.py"),
            "--wes-root",
            str(wes_root),
            "--out-dir",
            str(tmp_path / "out"),
            "--python",
            sys.executable,
            "--top-k",
            "7",
            "--allow-unhealthy",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    argv = json.loads(argv_path.read_text(encoding="utf-8"))
    assert argv[0] == "run-zenodex-recompute-batch-v4"
    assert argv[argv.index("--zenodex-root") + 1] == str(REPO_ROOT)
    assert argv[argv.index("--top-k") + 1] == "7"
    assert "--allow-unhealthy" in argv
