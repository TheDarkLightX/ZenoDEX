#!/usr/bin/env python3
"""Generate a LOCAL-DEV WS2 client pinset from a locally built blessed CLI.

This is the pin BOOTSTRAP for development and the opt-in e2e only: it derives
the pins (binary sha256 + compiled-in guest image id) from the binary it is
pointed at, which is trust-on-first-use BY CONSTRUCTION. It is therefore
explicitly NOT a production pin-distribution channel — production pins must
arrive out-of-band (signed release / WS5 upgrade gating), never derived from
whatever binary happens to be on disk. The emitted file says so loudly.

Default posture is HONEST refuse-by-default: `admission_proof_gated_statuses`
is EMPTY, because no deployed admission path requires this proof yet (Stage 3).
A valid real proof therefore ACCEPTS nowhere by default; pass --demo-stage3 to
emit the clearly-labelled demo variant that allow-lists the contract's
`bound_to_replay_guard` status so the ACCEPT mechanics can be exercised.

Usage:
  python3 tools/gen_ws2_client_pinset_local.py --out /tmp/pinset.json [--demo-stage3]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DEFAULT_CLI = REPO / "zk" / "state_proof_risc0" / "target" / "release" / "tau-state-proof-risc0-cli"
PERPS_PT = "risc0.zenodex_perps_np_transition.v1"


def _fail(message: str) -> "NoReturn":  # type: ignore[name-defined]  # noqa: F821
    sys.stderr.write(f"error: {message}\n")
    raise SystemExit(2)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cli-bin", type=Path, default=DEFAULT_CLI)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--chain-id", default="zenodex-local-risc0-smoke-1")
    parser.add_argument(
        "--demo-stage3",
        action="store_true",
        help="allow-list bound_to_replay_guard (DEMO ONLY: deployed admission is not proof-gated yet)",
    )
    args = parser.parse_args()

    cli_bin = args.cli_bin.resolve()
    if not cli_bin.is_file():
        _fail(f"blessed CLI not built: {cli_bin}")
    sha256 = hashlib.sha256(cli_bin.read_bytes()).hexdigest()

    proc = subprocess.run(
        [str(cli_bin)],
        input=json.dumps({"schema": "tau_state_proof_verifier_identity", "schema_version": 1}),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=60,
        check=False,
    )
    if proc.returncode != 0:
        _fail(f"verifier identity probe exited {proc.returncode}: {proc.stderr[-200:]}")
    identity = json.loads(proc.stdout)
    if identity.get("ok") is not True:
        _fail(f"verifier identity probe rejected: {identity}")
    words = identity.get("verifier_image_id_words")
    if not isinstance(words, list) or len(words) != 8:
        _fail("verifier identity probe returned malformed image id words")

    pinset = {
        "schema": "zenodex/client-pinset/v1",
        "local_dev_pinset": True,
        "not_a_distribution_channel": (
            "pins below were derived from the LOCAL binary (trust-on-first-use); "
            "production pins must ship out-of-band"
        ),
        "demo_stage3_admission": bool(args.demo_stage3),
        "pins": [
            {
                "surface": "perps_np",
                "operation": "deposit_collateral",
                "proof_type": PERPS_PT,
                "chain_id": args.chain_id,
                "risc0_image_id_words": words,
                "blessed_verifier": {"binary_path": str(cli_bin), "sha256": sha256},
                "required_journal_fields": [
                    "collateral_binding_hash",
                    "oracle_binding_hash",
                ],
                "expected_static": {},
                "recomputed_fields": ["collateral_binding_hash", "oracle_binding_hash"],
                "cross_field_equal": [],
                "head_equal_fields": [],
                "claim_level": "live_replay_authority_equivalent",
                "ceiling_level": "live_replay_authority_equivalent",
                "admission_threshold_level": "live_replay_authority_equivalent",
                "admission_proof_gated_statuses": (
                    ["bound_to_replay_guard"] if args.demo_stage3 else []
                ),
            }
        ],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(pinset, indent=2) + "\n")
    print(
        json.dumps(
            {
                "ok": True,
                "out": str(args.out),
                "verifier_sha256": sha256,
                "verifier_image_id_words": words,
                "demo_stage3_admission": bool(args.demo_stage3),
            }
        )
    )


if __name__ == "__main__":
    main()
