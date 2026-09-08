"""Compact native Tau source for the common-anchor polynomial construction."""

import re

from .anchor import AnchoredRepair


def export_anchor_tau(compiled: AnchoredRepair) -> str:
    """Share a uniquely determined same-step residual in the specification.

    The host evaluates the original proposal residual once and rechecks any
    repaired candidate. Source sharing does not establish native evaluation count.
    """
    contract = compiled.contract
    names = contract.environment + contract.controls
    symbols = {name: f"v{index}" for index, name in enumerate(names)}
    streams = {symbol: f"i{index + 1}[t]:sbf" for index, symbol in enumerate(symbols.values())}
    residual = contract.residual
    used = tuple(name for name in names if name in residual.variables()) or names[:1]
    args = ", ".join(symbols[name] for name in used)
    inputs = ", ".join(streams[symbols[name]] for name in used)
    lines = [
        "# Original common-anchor proposal controller; authority NONE.",
        "# Exact Boolean observations and proposed flags enter as data.",
        "# Every valid proposal is retained; other proposals use a checked anchor.",
        "# Generic local streams; this is not a Tau Net rule-offer payload.",
    ]
    lines.extend(f"# i{index + 1}: {name} (sbf)" for index, name in enumerate(names))
    lines.append(f"residual({args}):sbf := {residual.to_tau(symbols)}.")
    equations = [f"(r:sbf = residual({inputs}))"]
    for index, (name, term) in enumerate(compiled.anchor.assignments):
        lines.append(f"# o{index + 1}: proposed {name} (sbf)")
        anchor = re.sub(r"\bv[0-9]+\b", lambda match: streams[match[0]], term.to_tau(symbols))
        proposed = streams[symbols[name]]
        equations.append(f"(o{index + 1}[t]:sbf = (({proposed} & (r:sbf)') | ({anchor} & r:sbf)))")
    lines.append("always (ex r:sbf (" + " && ".join(equations) + ")).")
    return "\n".join(lines) + "\n"
