#!/usr/bin/env python3
"""Generate the language-neutral parity fixture consumed by the Rust gate kernel.

Single source of truth: gov_parity_cases.py (CASES + SIGNATURE_ORDER). This script
derives `tests/tau_specs/governance/fixtures/gov_gate_parity_cases.json`:

  * every boundary case as POSITIONAL args (signature order — no object-key-order
    ambiguity between json libraries);
  * canonical params-digest golden vectors, computed by gov_epoch.params_digest —
    the Rust `params_digest` must reproduce them byte-for-byte (the cross-language
    canonical-encoder obligation).

test_gov_parity.py::test_rust_fixture_in_sync re-derives these bytes and compares to
the committed file, so the fixture can never silently drift from the source table.
Regenerate with:  python3 src/tau_specs/governance/gen_rust_parity_fixture.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

_GOV = Path(__file__).resolve().parent
sys.path.insert(0, str(_GOV))

import gov_epoch  # noqa: E402
import gov_parity_cases as cases  # noqa: E402

FIXTURE = (_GOV.parents[2] / "tests" / "tau_specs" / "governance"
           / "fixtures" / "gov_gate_parity_cases.json")

_DIGEST_VECTOR_PARAMS = [
    {
        "fee_bps": 500, "funding_cap_bps": 100, "redeem_staker_bps": 6000,
        "buyburn_bps": 6000, "stakers_bps": 0, "reserve_bps": 2000, "hosts_bps": 2000,
        "mcr_bps": 11000, "ccr_bps": 15000,
    },
    {
        "fee_bps": 0, "funding_cap_bps": 200, "redeem_staker_bps": 7000,
        "buyburn_bps": 10000, "stakers_bps": 0, "reserve_bps": 0, "hosts_bps": 0,
        "mcr_bps": 10000, "ccr_bps": 30000,
    },
]


def fixture_bytes() -> bytes:
    """The canonical fixture serialization (deterministic; trailing newline)."""
    rows = []
    for surface, kwargs, expect in cases.CASES:
        order = cases.SIGNATURE_ORDER[surface]
        if set(kwargs) != set(order):
            raise ValueError(f"case kwargs do not match SIGNATURE_ORDER for {surface!r}")
        rows.append({"surface": surface, "args": [kwargs[k] for k in order],
                     "expect": expect})
    vectors = [{"params": dict(sorted(p.items())),
                "sha256_hex": gov_epoch.params_digest(p)}
               for p in _DIGEST_VECTOR_PARAMS]
    doc = {
        "comment": ("GENERATED from gov_parity_cases.py by gen_rust_parity_fixture.py —"
                    " do not edit by hand; test_gov_parity.py byte-pins this file."
                    " args are POSITIONAL per SIGNATURE_ORDER."),
        "cases": rows,
        "params_digest_vectors": vectors,
    }
    return (json.dumps(doc, indent=1, sort_keys=False) + "\n").encode("utf-8")


def main() -> int:
    FIXTURE.parent.mkdir(parents=True, exist_ok=True)
    data = fixture_bytes()
    FIXTURE.write_bytes(data)
    print(f"wrote {FIXTURE} ({len(data)} bytes, "
          f"{len(cases.CASES)} cases, {len(_DIGEST_VECTOR_PARAMS)} digest vectors)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
