"""Stable sampled-retrievability rejection surface."""

from __future__ import annotations

from typing import NoReturn


class SampledRetrievabilityRejectV1(ValueError):
    """Stable rejection from the exact sampled-retrievability boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def reject(code: str, detail: str) -> NoReturn:
    raise SampledRetrievabilityRejectV1(code, detail)
