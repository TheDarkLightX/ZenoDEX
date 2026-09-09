#!/usr/bin/env python3
"""Source script entry: seal installed bytes before importing the project CLI."""

import importlib.util
import io
import json
import runpy
import sys
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _load_local_package(name: str) -> None:
    package = ROOT / name
    if not (package / "__init__.py").is_file():
        return
    spec = importlib.util.spec_from_file_location(name, package / "__init__.py",
                                                submodule_search_locations=[str(package)])
    if spec is None or spec.loader is None or name in sys.modules:
        raise ValueError("unsealed package loader")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)

def main() -> int:
    try:
        # Loading this stdlib-only file directly avoids executing src package
        # initializers before their source bytes have entered the seal.
        bootstrap = runpy.run_path(str(ROOT / "src/zenolacuna/project_execution.py"))
        bootstrap["seal_before_import"](ROOT)
        # Expose only these sealed packages. Adding ROOT to sys.path would let
        # unpinned sibling files shadow stdlib or installed dependencies.
        _load_local_package("src")
        _load_local_package("tools")
        from src.zenolacuna.project_cli import main as project_main
        bootstrap["check_execution_seal"](ROOT)
        output = io.StringIO()
        with redirect_stdout(output):
            try:
                result = project_main(sys.argv[1:])
            except SystemExit as exit_request:
                result = exit_request.code if type(exit_request.code) is int else 2
        bootstrap["check_execution_seal"](ROOT)
        sys.stdout.write(output.getvalue())
        return result
    except (ImportError, OSError, ValueError) as exc:
        code = getattr(exc, "code", "SOURCE_EXECUTION_UNSEALED")
        print(json.dumps({"status": "REJECTED", "code": code, "authority": "NONE"}, sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
