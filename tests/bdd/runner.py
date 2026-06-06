"""Minimal, dependency-free Gherkin runner for the ZenoDEX front door.

Deliberately tiny and line-oriented. CBC ethos: the behavior contract that the
core/guest/differential conform to must itself be auditable -- no magic
framework, no PyPI dependency on the authority path.

SUPPORTED (by design, the whole grammar):
  * ``Feature:``           one per file
  * ``Background:``        steps run before every scenario
  * ``@tag`` lines         attached to the next ``Scenario:`` (e.g. ``@pending``)
  * ``Scenario:``          a named list of steps
  * ``Given/When/Then/And/But <text>``  steps; the keyword is cosmetic -- steps
    are matched purely by text, so ``And``/``But`` just continue the prior clause
  * ``# ...`` comments and blank lines are ignored

NOT SUPPORTED (deliberately): Scenario Outline, Examples tables, doc strings.
If a scenario wants those, SPLIT the scenario -- do not grow this runner.

Step patterns use ``{name}`` placeholders, each captured as a non-greedy group
and passed to the step function as a keyword argument.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Callable

_STEP_RE = re.compile(r"^(Given|When|Then|And|But)\s+(.*\S)\s*$")
_TAG_RE = re.compile(r"^(@[\w-]+(?:\s+@[\w-]+)*)\s*$")


@dataclass
class Scenario:
    name: str
    steps: list[str] = field(default_factory=list)
    tags: tuple[str, ...] = ()


@dataclass
class Feature:
    name: str
    background: list[str] = field(default_factory=list)
    scenarios: list[Scenario] = field(default_factory=list)


def parse_feature(text: str) -> Feature:
    feat: Feature | None = None
    bucket: list[str] | None = None  # the step list currently being filled
    pending_tags: list[str] = []

    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("Feature:"):
            feat = Feature(name=line[len("Feature:"):].strip())
            bucket = None
            continue
        if line.startswith("Background:"):
            if feat is None:
                raise ValueError("Background before Feature")
            bucket = feat.background
            continue
        if line.startswith("Scenario:"):
            if feat is None:
                raise ValueError("Scenario before Feature")
            scn = Scenario(name=line[len("Scenario:"):].strip(), tags=tuple(pending_tags))
            pending_tags = []
            feat.scenarios.append(scn)
            bucket = scn.steps
            continue
        step_m = _STEP_RE.match(line)
        if step_m:
            if bucket is None:
                raise ValueError(f"step before Background/Scenario: {line!r}")
            bucket.append(step_m.group(2))  # store text WITHOUT the cosmetic keyword
            continue
        tag_m = _TAG_RE.match(line)
        if tag_m:
            pending_tags.extend(tag_m.group(1).split())
            continue
        raise ValueError(f"unparseable feature line: {raw!r}")

    if feat is None:
        raise ValueError("no Feature in file")
    return feat


class StepRegistry:
    """Holds ``(compiled_pattern, fn)`` and dispatches a step line to its fn."""

    def __init__(self) -> None:
        self._steps: list[tuple[re.Pattern[str], Callable[..., None]]] = []

    def step(self, pattern: str) -> Callable[[Callable[..., None]], Callable[..., None]]:
        regex = self._compile(pattern)

        def deco(fn: Callable[..., None]) -> Callable[..., None]:
            self._steps.append((regex, fn))
            return fn

        return deco

    @staticmethod
    def _compile(pattern: str) -> re.Pattern[str]:
        parts = []
        for chunk in re.split(r"(\{[A-Za-z_]\w*\})", pattern):
            if chunk.startswith("{") and chunk.endswith("}"):
                parts.append(f"(?P<{chunk[1:-1]}>.+?)")
            else:
                parts.append(re.escape(chunk))
        return re.compile("^" + "".join(parts) + "$")

    def run_step(self, text: str, ctx: object) -> None:
        for regex, fn in self._steps:
            m = regex.match(text)
            if m:
                fn(ctx, **m.groupdict())
                return
        raise AssertionError(f"no step definition matches: {text!r}")
