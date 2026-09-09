"""Independent delivery-history and source-explicit product workflows."""

from dataclasses import replace
from itertools import permutations
from pathlib import Path

import pytest

from src.zenolacuna.model import (
    Decision,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Profile,
    Question,
    Requirement,
    Scope,
    digest,
)
from src.zenolacuna.shell import Store


def _scope() -> Scope:
    written = ((0,), (1, 2))
    return Scope("delivery history", ("protected", "disputed"), (
        Outcome("success", "positive required witness", OutcomeKind.ACCEPT),
        Outcome("legacy", "preserved wire compatibility", OutcomeKind.ACCEPT),
        Outcome("new", "changed wire compatibility", OutcomeKind.ACCEPT),
    ), (0, 1), written,
        (Requirement("positive remains", (0,), written, ((0,), ())),),
        (Hypothesis("legacy", ((0,), (1,))), Hypothesis("new", ((0,), (2,)))),
        (Question("compatibility", "Preserve the old wire mapping?", 1, ("yes", "no")),))


def test_s24_all_retry_and_already_stale_delivery_orders_have_one_accepted_history(tmp_path: Path) -> None:
    final_snapshots = []
    for i, order in enumerate(permutations(("valid", "retry", "stale"))):
        scope = _scope()
        run = tmp_path / str(i)
        store = Store.initialize(run, scope, source_root=tmp_path, profile=Profile.SIMULATED)
        before = store.status()
        witness = before.report.witness
        assert witness is not None
        valid = Decision("choose-compatibility", scope.root, before.revision, "compatibility", "yes",
                         digest(witness), Profile.SIMULATED, "simulated-owner")
        stale = replace(valid, command_id="already-stale", parent="0" * 64)
        for event in order:
            if event == "stale":
                old_revision = store.status().revision
                with pytest.raises(LacunaError, match="^STALE_ANSWER$"):
                    store.answer(stale)
                assert store.status().revision == old_revision
            else:
                assert store.answer(valid).code in {"ACCEPTED", "IDEMPOTENT_DUPLICATE"}
        reopened = Store(run, source_root=tmp_path, profile=Profile.SIMULATED).status()
        records = tuple((path.name, path.read_bytes()) for path in sorted((run / "records").glob("*.json")))
        assert len(records) == 2  # Genesis plus exactly one simulated decision.
        final_snapshots.append((reopened.revision, reopened.report, records))
    assert all(snapshot == final_snapshots[0] for snapshot in final_snapshots)
