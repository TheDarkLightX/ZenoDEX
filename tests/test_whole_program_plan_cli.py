"""The established command must report current selection after plan replacement."""

import json

from tools import check_whole_program_plan_admission_v1 as cli
from tools.whole_program_plan_admission_v2 import TRUSTED_PLAN_COMMIT


def test_established_command_reports_current_selected_plan(capsys) -> None:
    assert cli.main([]) == 0
    report = json.loads(capsys.readouterr().out)
    assert report["schema"] == "zenodex/plan-admission-check/v2"
    assert report["active_plan_commit"] == TRUSTED_PLAN_COMMIT
    assert report["production_authority"] == "NONE"


def test_historical_command_labels_old_selection_as_history(capsys) -> None:
    assert cli.main(["--historical"]) == 0
    report = json.loads(capsys.readouterr().out)
    assert report["selection_scope"] == "HISTORICAL_REPLAY_ONLY"
    assert report["active_plan_commit"] == cli.PLAN_COMMIT
    assert report["production_authority"] == "NONE"
