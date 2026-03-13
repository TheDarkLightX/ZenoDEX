from __future__ import annotations

import sys
from dataclasses import dataclass
from types import FrameType
from typing import Any, Callable, Iterable


@dataclass
class PathSignature:
    """A lightweight execution-path signature for boundary mining.

    We record executed (filename, lineno) pairs for frames under the configured roots.
    This is intentionally crude: it is a discriminator, not a proof artifact.
    """

    lines: set[tuple[str, int]]

    def frozen(self) -> tuple[tuple[str, int], ...]:
        return tuple(sorted(self.lines))


def trace_path_signature(
    fn: Callable[..., Any],
    *,
    kwargs: dict[str, Any],
    trace_paths: Iterable[str],
) -> tuple[Any, tuple[tuple[str, int], ...]]:
    """Run `fn(**kwargs)` while recording executed lines under `trace_paths`.

    Returns:
      (output, frozen_signature)
    """
    roots = tuple(str(p) for p in trace_paths)
    sig = PathSignature(lines=set())

    def _tracer(frame: FrameType, event: str, arg: object) -> Callable[..., Any] | None:
        if event != "line":
            return _tracer
        filename = frame.f_code.co_filename
        for r in roots:
            if filename.startswith(r):
                sig.lines.add((filename, int(frame.f_lineno)))
                break
        return _tracer

    prev = sys.gettrace()
    sys.settrace(_tracer)
    try:
        out = fn(**kwargs)
    finally:
        sys.settrace(prev)
    return out, sig.frozen()

