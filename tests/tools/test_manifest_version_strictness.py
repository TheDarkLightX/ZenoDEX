from __future__ import annotations

import importlib
import json
from pathlib import Path

import pytest

CHECKER_MODULES = [
    "tools.check_runtime_shell_assurance_manifest",
    "tools.check_derivatives_evidence_manifest",
    "tools.check_batch_auction_ifql_vmo_manifest",
]


@pytest.mark.parametrize("module_name", CHECKER_MODULES)
@pytest.mark.parametrize("manifest_version", [True, "1"])
def test_manifest_checkers_reject_coerced_manifest_version(
    tmp_path: Path,
    module_name: str,
    manifest_version: object,
) -> None:
    module = importlib.import_module(module_name)
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps({"manifest_version": manifest_version}),
        encoding="utf-8",
    )

    with pytest.raises(module.ManifestError, match="manifest_version: expected int"):
        module.main(["--manifest", str(manifest_path)])
