from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from .zenograph_schema import ZGEntity, ZGFact, ZGFactStatus, zg_entity_from_dict, zg_fact_from_dict


@dataclass(frozen=True)
class ZGStorePaths:
    root: Path
    entities_path: Path
    accepted_path: Path
    proposed_path: Path
    rejected_path: Path
    derived_path: Path
    observed_path: Path
    inferred_path: Path


def _status_file_name(status: ZGFactStatus) -> str:
    return f"facts_{status.value}.jsonl"


def build_zenograph_store_paths(root: str | Path) -> ZGStorePaths:
    base = Path(root)
    return ZGStorePaths(
        root=base,
        entities_path=base / "entities.jsonl",
        accepted_path=base / _status_file_name(ZGFactStatus.ACCEPTED),
        proposed_path=base / _status_file_name(ZGFactStatus.PROPOSED),
        rejected_path=base / _status_file_name(ZGFactStatus.REJECTED),
        derived_path=base / _status_file_name(ZGFactStatus.DERIVED),
        observed_path=base / _status_file_name(ZGFactStatus.OBSERVED),
        inferred_path=base / _status_file_name(ZGFactStatus.INFERRED),
    )


class ZenoGraphStore:
    def __init__(self, root: str | Path) -> None:
        self.paths = build_zenograph_store_paths(root)
        self.paths.root.mkdir(parents=True, exist_ok=True)
        self._entity_ids = self._load_ids(self.paths.entities_path, key="entity_id")
        self._fact_ids = self._load_fact_ids()

    def append_entity(self, entity: ZGEntity) -> None:
        if entity.entity_id in self._entity_ids:
            raise ValueError(f"duplicate entity_id: {entity.entity_id}")
        self._append_jsonl(self.paths.entities_path, entity.to_dict())
        self._entity_ids.add(entity.entity_id)

    def append_fact(self, fact: ZGFact) -> None:
        if fact.fact_id in self._fact_ids:
            raise ValueError(f"duplicate fact_id: {fact.fact_id}")
        self._append_jsonl(self._path_for_status(fact.status), fact.to_dict())
        self._fact_ids.add(fact.fact_id)

    def iter_entities(self) -> Iterable[ZGEntity]:
        for obj in self._iter_jsonl(self.paths.entities_path):
            yield zg_entity_from_dict(obj)

    def iter_facts(self, status: ZGFactStatus | None = None) -> Iterable[ZGFact]:
        if status is None:
            for current in ZGFactStatus:
                yield from self.iter_facts(status=current)
            return
        for obj in self._iter_jsonl(self._path_for_status(status)):
            yield zg_fact_from_dict(obj)

    def has_entity(self, entity_id: str) -> bool:
        return entity_id in self._entity_ids

    def has_fact(self, fact_id: str) -> bool:
        return fact_id in self._fact_ids

    def _load_fact_ids(self) -> set[str]:
        fact_ids: set[str] = set()
        for status in ZGFactStatus:
            fact_ids.update(self._load_ids(self._path_for_status(status), key="fact_id"))
        return fact_ids

    def _load_ids(self, path: Path, *, key: str) -> set[str]:
        ids: set[str] = set()
        for obj in self._iter_jsonl(path):
            value = obj.get(key)
            if isinstance(value, str):
                ids.add(value)
        return ids

    def _path_for_status(self, status: ZGFactStatus) -> Path:
        if status is ZGFactStatus.ACCEPTED:
            return self.paths.accepted_path
        if status is ZGFactStatus.PROPOSED:
            return self.paths.proposed_path
        if status is ZGFactStatus.REJECTED:
            return self.paths.rejected_path
        if status is ZGFactStatus.DERIVED:
            return self.paths.derived_path
        if status is ZGFactStatus.OBSERVED:
            return self.paths.observed_path
        if status is ZGFactStatus.INFERRED:
            return self.paths.inferred_path
        raise AssertionError(f"unsupported status: {status!r}")

    @staticmethod
    def _append_jsonl(path: Path, obj: dict[str, object]) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(obj, sort_keys=True, separators=(",", ":")))
            handle.write("\n")

    @staticmethod
    def _iter_jsonl(path: Path) -> Iterable[dict[str, object]]:
        if not path.exists():
            return
        with path.open("r", encoding="utf-8") as handle:
            for line in handle:
                raw = line.strip()
                if not raw:
                    continue
                obj = json.loads(raw)
                if not isinstance(obj, dict):
                    raise ValueError(f"jsonl record must be an object: {path}")
                yield obj
