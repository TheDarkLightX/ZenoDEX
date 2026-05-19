from __future__ import annotations

from pathlib import Path

from tools.check_release_external_toolchains import run_check


def test_release_external_toolchains_accepts_vendored_esso_and_tau(tmp_path: Path) -> None:
    esso_pkg = tmp_path / "external" / "ESSO" / "ESSO" / "verify"
    esso_pkg.mkdir(parents=True)
    (tmp_path / "external" / "ESSO" / "ESSO" / "__init__.py").write_text("", encoding="utf-8")
    (esso_pkg / "__init__.py").write_text("", encoding="utf-8")
    (esso_pkg / "ltlf_synth.py").write_text(
        "def synthesize_ltlf_multi_property():\n    pass\n",
        encoding="utf-8",
    )
    tau = tmp_path / "external" / "tau-lang" / "build-Release" / "tau"
    tau.parent.mkdir(parents=True)
    tau.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    tau.chmod(0o755)
    tla = tmp_path / "external" / "tla-tools" / "tla2tools.jar"
    tla.parent.mkdir(parents=True)
    tla.write_bytes(b"jar")
    (tmp_path / "external" / "mathlib4").mkdir(parents=True)

    result = run_check(root=tmp_path)

    assert result["schema"] == "zenodex.release_external_toolchains_check.v1"
    assert result["external_toolchains"]["ESSO"]["available"] is True
    assert result["external_toolchains"]["ESSO"]["source"] == "external/ESSO"
    assert result["external_toolchains"]["Tau"]["available"] is True
    assert result["external_toolchains"]["Tau"]["source"] == "external/tau-lang/build-Release/tau"
    assert result["external_toolchains"]["TLA"]["available"] is True
    assert result["external_toolchains"]["TLA"]["source"] == "external/tla-tools/tla2tools.jar"
    assert result["external_toolchains"]["mathlib4"]["available"] is True
    assert result["external_toolchains"]["mathlib4"]["source"] == "external/mathlib4"
    assert "missing_toolchain:ESSO" not in result["errors"]
    assert "missing_toolchain:Tau" not in result["errors"]
    assert "missing_toolchain:TLA" not in result["errors"]
    assert "missing_toolchain:mathlib4" not in result["errors"]


def test_release_external_toolchains_reports_missing_external_tools(tmp_path: Path) -> None:
    result = run_check(root=tmp_path)

    if result["external_toolchains"]["ESSO"]["source"] == "missing":
        assert result["ok"] is False
        assert "missing_toolchain:ESSO" in result["errors"]
    else:
        assert result["external_toolchains"]["ESSO"]["available"] is True
    if result["external_toolchains"]["Tau"]["source"] == "missing":
        assert result["ok"] is False
        assert "missing_toolchain:Tau" in result["errors"]
    else:
        assert result["external_toolchains"]["Tau"]["available"] is True
    if result["external_toolchains"]["TLA"]["source"] == "missing":
        assert result["ok"] is False
        assert "missing_toolchain:TLA" in result["errors"]
    else:
        assert result["external_toolchains"]["TLA"]["available"] is True
    assert result["external_toolchains"]["mathlib4"]["source"] == "missing"
    assert "missing_toolchain:mathlib4" in result["errors"]
