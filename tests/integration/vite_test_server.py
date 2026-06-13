from __future__ import annotations

from pathlib import Path


def vite_dev_command(dex_ui: Path, port: int) -> list[str]:
    """Start the real Vite server process, not an npm wrapper parent."""
    return [
        str(dex_ui / "node_modules" / ".bin" / "vite"),
        "--host",
        "127.0.0.1",
        "--port",
        str(port),
    ]
