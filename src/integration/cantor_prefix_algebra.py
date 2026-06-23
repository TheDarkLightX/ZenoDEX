from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable, Iterator, Sequence


Prefix = tuple[int, ...]


def _coerce_bit(bit: int | bool) -> int:
    if isinstance(bit, bool):
        return int(bit)
    if isinstance(bit, int) and bit in (0, 1):
        return int(bit)
    raise ValueError("bits must be 0 or 1")


def parse_prefix(text: str) -> Prefix:
    token = str(text).strip()
    if token in ("", "*"):
        return ()
    if token.endswith("*"):
        token = token[:-1]
    if not token:
        return ()
    if any(ch not in "01" for ch in token):
        raise ValueError("prefix strings must contain only 0/1 and an optional trailing *")
    return tuple(int(ch) for ch in token)


def format_prefix(prefix: Sequence[int]) -> str:
    bits = tuple(_coerce_bit(bit) for bit in prefix)
    if not bits:
        return "*"
    return "".join(str(bit) for bit in bits) + "*"


def _normalize_prefixes(prefixes: Iterable[Prefix]) -> tuple[Prefix, ...]:
    normalized_input = tuple(tuple(_coerce_bit(bit) for bit in prefix) for prefix in prefixes)
    return _normalize_subtree(normalized_input)


def _normalize_subtree(prefixes: tuple[Prefix, ...]) -> tuple[Prefix, ...]:
    if not prefixes:
        return ()
    if () in prefixes:
        return ((),)

    left = tuple(prefix[1:] for prefix in prefixes if prefix and prefix[0] == 0)
    right = tuple(prefix[1:] for prefix in prefixes if prefix and prefix[0] == 1)
    left_norm = _normalize_subtree(left)
    right_norm = _normalize_subtree(right)

    if left_norm == ((),) and right_norm == ((),):
        return ((),)

    out: list[Prefix] = []
    out.extend((0,) + prefix for prefix in left_norm)
    out.extend((1,) + prefix for prefix in right_norm)
    return tuple(out)


def _is_prefix(prefix: Prefix, word: Prefix) -> bool:
    return len(prefix) <= len(word) and word[: len(prefix)] == prefix


def _meet_prefixes(left: tuple[Prefix, ...], right: tuple[Prefix, ...]) -> tuple[Prefix, ...]:
    intersections: list[Prefix] = []
    for left_prefix in left:
        for right_prefix in right:
            if _is_prefix(left_prefix, right_prefix):
                intersections.append(right_prefix)
            elif _is_prefix(right_prefix, left_prefix):
                intersections.append(left_prefix)
    return _normalize_prefixes(intersections)


def _complement_subtree(prefixes: tuple[Prefix, ...]) -> tuple[Prefix, ...]:
    if not prefixes:
        return ((),)
    if prefixes == ((),):
        return ()

    left = tuple(prefix[1:] for prefix in prefixes if prefix and prefix[0] == 0)
    right = tuple(prefix[1:] for prefix in prefixes if prefix and prefix[0] == 1)
    left_comp = _complement_subtree(left)
    right_comp = _complement_subtree(right)

    if left_comp == ((),) and right_comp == ((),):
        return ((),)

    out: list[Prefix] = []
    out.extend((0,) + prefix for prefix in left_comp)
    out.extend((1,) + prefix for prefix in right_comp)
    return tuple(out)


@dataclass(frozen=True)
class CantorPrefixRegion:
    prefixes: tuple[Prefix, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "prefixes", _normalize_prefixes(self.prefixes))

    @classmethod
    def empty(cls) -> "CantorPrefixRegion":
        return cls(())

    @classmethod
    def top(cls) -> "CantorPrefixRegion":
        return cls(((),))

    @classmethod
    def from_prefix(cls, prefix: Sequence[int | bool]) -> "CantorPrefixRegion":
        return cls((tuple(_coerce_bit(bit) for bit in prefix),))

    @classmethod
    def from_strings(cls, prefixes: Iterable[str]) -> "CantorPrefixRegion":
        return cls(tuple(parse_prefix(prefix) for prefix in prefixes))

    @classmethod
    def depth_partition(cls, depth: int) -> tuple["CantorPrefixRegion", ...]:
        if not isinstance(depth, int) or isinstance(depth, bool) or depth < 0:
            raise ValueError("depth must be a non-negative int")
        return tuple(cls.from_prefix(bits) for bits in product((0, 1), repeat=depth))

    @property
    def depth(self) -> int:
        if not self.prefixes:
            return 0
        return max(len(prefix) for prefix in self.prefixes)

    def is_empty(self) -> bool:
        return not self.prefixes

    def is_top(self) -> bool:
        return self.prefixes == ((),)

    def to_strings(self) -> tuple[str, ...]:
        return tuple(format_prefix(prefix) for prefix in self.prefixes)

    def refines(self, other: "CantorPrefixRegion") -> bool:
        return self <= other

    def covers_word(self, word: Sequence[int | bool]) -> bool:
        sample = tuple(_coerce_bit(bit) for bit in word)
        return any(_is_prefix(prefix, sample) for prefix in self.prefixes)

    def __or__(self, other: "CantorPrefixRegion") -> "CantorPrefixRegion":
        return CantorPrefixRegion(self.prefixes + other.prefixes)

    def __and__(self, other: "CantorPrefixRegion") -> "CantorPrefixRegion":
        return CantorPrefixRegion(_meet_prefixes(self.prefixes, other.prefixes))

    def __invert__(self) -> "CantorPrefixRegion":
        return CantorPrefixRegion(_complement_subtree(self.prefixes))

    def __le__(self, other: "CantorPrefixRegion") -> bool:
        other_prefixes = other.prefixes
        return all(any(_is_prefix(candidate, prefix) for candidate in other_prefixes) for prefix in self.prefixes)

    def __lt__(self, other: "CantorPrefixRegion") -> bool:
        return self <= other and self != other

    def iter_prefixes(self) -> Iterator[Prefix]:
        return iter(self.prefixes)


def partition_ok(parts: Sequence[CantorPrefixRegion]) -> bool:
    if not parts:
        return False

    seen = CantorPrefixRegion.empty()
    for part in parts:
        if not (seen & part).is_empty():
            return False
        seen = seen | part
    return seen.is_top()
