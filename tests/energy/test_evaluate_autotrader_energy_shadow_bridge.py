from __future__ import annotations

from tools import evaluate_autotrader_energy_shadow_bridge as bridge_tool


def test_shadow_bridge_cli_rejects_truthy_string_ok(monkeypatch, capsys) -> None:
    def fake_evaluate_shadow_bridge(**_kwargs):
        return {
            "schema": "zenodex/energy/autotrader_shadow_bridge_report/v1",
            "ok": "true",
        }

    monkeypatch.setattr(bridge_tool, "evaluate_shadow_bridge", fake_evaluate_shadow_bridge)
    monkeypatch.setattr(bridge_tool.sys, "argv", ["evaluate_autotrader_energy_shadow_bridge.py"])

    rc = bridge_tool.main()
    output = capsys.readouterr().out

    assert rc == 1
    assert '"ok": "true"' in output
