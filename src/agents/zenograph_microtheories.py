from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Mapping

import yaml


@dataclass(frozen=True)
class ZGMicrotheorySpec:
    microtheory_id: str
    priority: int
    activation_all: tuple[str, ...] = field(default_factory=tuple)
    activation_any: tuple[str, ...] = field(default_factory=tuple)

    def __post_init__(self) -> None:
        if not isinstance(self.microtheory_id, str) or not self.microtheory_id.strip():
            raise ValueError("microtheory_id must be a non-empty string")
        if not isinstance(self.priority, int) or isinstance(self.priority, bool):
            raise TypeError("priority must be an int")
        if self.priority < 0:
            raise ValueError("priority must be >= 0")
        object.__setattr__(self, "microtheory_id", self.microtheory_id.strip())
        object.__setattr__(self, "activation_all", _normalize_flag_tuple(self.activation_all, name="activation_all"))
        object.__setattr__(self, "activation_any", _normalize_flag_tuple(self.activation_any, name="activation_any"))

    def is_active(self, flags: Mapping[str, bool]) -> bool:
        if self.activation_all and not all(bool(flags.get(flag, False)) for flag in self.activation_all):
            return False
        if self.activation_any and not any(bool(flags.get(flag, False)) for flag in self.activation_any):
            return False
        return True


def _normalize_flag_tuple(values: tuple[str, ...] | list[str], *, name: str) -> tuple[str, ...]:
    out: list[str] = []
    seen: set[str] = set()
    for idx, raw in enumerate(values):
        if not isinstance(raw, str) or not raw.strip():
            raise ValueError(f"{name}[{idx}] must be a non-empty string")
        value = raw.strip()
        if value in seen:
            continue
        seen.add(value)
        out.append(value)
    return tuple(out)


def load_microtheory_specs(path: str | Path) -> tuple[ZGMicrotheorySpec, ...]:
    raw = yaml.safe_load(Path(path).read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("microtheory config must be a mapping")
    items = raw.get("microtheories")
    if not isinstance(items, list) or not items:
        raise ValueError("microtheory config must define a non-empty microtheories list")
    specs = [
        ZGMicrotheorySpec(
            microtheory_id=item["id"],
            priority=item["priority"],
            activation_all=tuple(item.get("activation_all", ())),
            activation_any=tuple(item.get("activation_any", ())),
        )
        for item in items
    ]
    return tuple(sorted(specs, key=lambda spec: (-spec.priority, spec.microtheory_id)))


def resolve_active_microtheories(
    specs: tuple[ZGMicrotheorySpec, ...],
    flags: Mapping[str, bool],
) -> tuple[str, ...]:
    active = [spec.microtheory_id for spec in specs if spec.is_active(flags)]
    return tuple(active)
