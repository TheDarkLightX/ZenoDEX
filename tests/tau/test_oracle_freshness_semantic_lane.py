from __future__ import annotations


def _oracle_freshness_guard_ok(*, current_epoch: int, quote_epoch: int, max_staleness_epochs: int) -> bool:
    return quote_epoch <= current_epoch and (current_epoch - quote_epoch) <= max_staleness_epochs


def test_oracle_freshness_accepts_bounded_non_future_quote() -> None:
    assert _oracle_freshness_guard_ok(current_epoch=10, quote_epoch=8, max_staleness_epochs=2) is True


def test_oracle_freshness_rejects_future_quote() -> None:
    assert _oracle_freshness_guard_ok(current_epoch=8, quote_epoch=10, max_staleness_epochs=5) is False


def test_oracle_freshness_rejects_stale_quote() -> None:
    assert _oracle_freshness_guard_ok(current_epoch=10, quote_epoch=5, max_staleness_epochs=3) is False
