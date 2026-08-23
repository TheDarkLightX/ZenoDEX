from __future__ import annotations

import multiprocessing
from pathlib import Path

from src.integration.autotrader_execution_journal import reserve_execution_id


def _reserve_same_execution_id(path: str, start, outcomes) -> None:
    start.wait()
    try:
        reserve_execution_id(
            path=path,
            execution_keys=set(),
            execution_id="cross-process-execution",
            surface="autotrader_live_execute_once",
        )
    except ValueError as exc:
        outcomes.put(str(exc))
    else:
        outcomes.put("reserved")


def test_execution_journal_atomic_reservation_allows_one_cross_process_winner(
    tmp_path: Path,
) -> None:
    context = multiprocessing.get_context("fork")
    start = context.Event()
    outcomes = context.Queue()
    journal = tmp_path / "execution-journal.jsonl"
    workers = [
        context.Process(
            target=_reserve_same_execution_id,
            args=(str(journal), start, outcomes),
        )
        for _index in range(4)
    ]

    for worker in workers:
        worker.start()
    start.set()
    observed = [outcomes.get(timeout=10) for _worker in workers]
    for worker in workers:
        worker.join(timeout=10)

    assert all(worker.exitcode == 0 for worker in workers)
    assert observed.count("reserved") == 1
    assert observed.count("execution_replay") == 3
    assert len(journal.read_text(encoding="utf-8").splitlines()) == 1
