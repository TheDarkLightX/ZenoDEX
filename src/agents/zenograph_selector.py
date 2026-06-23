from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class ZGTemplateCandidate:
    template_id: str
    rank: int
    admissible: bool
    explain: tuple[str, ...] = field(default_factory=tuple)

    def __post_init__(self) -> None:
        if not isinstance(self.template_id, str) or not self.template_id.strip():
            raise ValueError("template_id must be a non-empty string")
        if not isinstance(self.rank, int) or isinstance(self.rank, bool):
            raise TypeError("rank must be an int")
        if self.rank < 0:
            raise ValueError("rank must be >= 0")
        if not isinstance(self.admissible, bool):
            raise TypeError("admissible must be a bool")


def select_best_template(candidates: tuple[ZGTemplateCandidate, ...]) -> ZGTemplateCandidate | None:
    admissible = tuple(candidate for candidate in candidates if candidate.admissible)
    if not admissible:
        return None
    return min(admissible, key=lambda candidate: (candidate.rank, candidate.template_id))
