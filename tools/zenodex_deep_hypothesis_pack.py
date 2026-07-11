#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]

VALID_TRANSFORMS = {"equiv", "reduce", "relax", "restrict", "heuristic"}


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _safe_token(text: str, *, max_len: int = 120) -> str:
    chars = []
    for ch in str(text):
        if ch.isalnum() or ch in "_.-":
            chars.append(ch)
        else:
            chars.append("_")
    token = "".join(chars).strip("._")
    if not token:
        token = "x"
    return token[:max_len]


def _slice_window(items: list[str], start: int, count: int) -> list[str]:
    if not items or count <= 0:
        return []
    n = len(items)
    out: list[str] = []
    for i in range(count):
        out.append(items[(start + i) % n])
    return out


def _discover_lean_files() -> list[str]:
    root = ROOT / "lean-mathlib" / "Proofs"
    if not root.exists():
        return []
    rows: list[str] = []
    for path in sorted(root.rglob("*.lean")):
        if path.is_file():
            rows.append(str(path.relative_to(ROOT)))
    return rows


def _discover_kernel_files() -> list[str]:
    root = ROOT / "src" / "kernels" / "dex"
    if not root.exists():
        return []
    rows: list[str] = []
    for path in sorted(root.rglob("*.yaml")):
        name = path.name
        low = name.lower()
        # Keep kernels that look like concrete specs, not hole/synth/debug corpora.
        if any(tok in low for tok in ("hole", "synth", "corpus", "spec_quality")):
            continue
        # Only include ESSO kernel IR files. This avoids pulling in system-spec
        # compose YAMLs that fail verify-multi for schema reasons (not mechanism reasons).
        try:
            head = path.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        if "ir_version:" not in head:
            continue
        if "esso-ir/" not in head:
            continue
        if path.is_file():
            rows.append(str(path.relative_to(ROOT)))
    return rows


def _base_specs() -> list[dict[str, Any]]:
    import sys

    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    from tools.zenodex_candidate_specs import _candidate_specs  # pylint: disable=import-outside-toplevel

    return _candidate_specs()


def _lean_transform(path: str) -> tuple[str, list[int]]:
    low = path.lower()
    if any(tok in low for tok in ("safety", "funding", "insurance", "protocol", "volatility", "tausafe")):
        return ("restrict", [2, 0, 1, -1, 1])
    return ("equiv", [1, 0, 1, -1, 2])


def _kernel_transform(path: str) -> tuple[str, list[int]]:
    low = path.lower()
    if any(tok in low for tok in ("safety", "guard", "insurance", "funding", "volatility", "conservation")):
        return ("restrict", [2, 0, 1, -1, 1])
    if any(tok in low for tok in ("router", "curve", "batch", "cpmm")):
        return ("reduce", [1, 1, 2, -1, 1])
    return ("equiv", [1, 0, 1, -1, 2])


def _deep_lean_specs(files: list[str]) -> list[dict[str, Any]]:
    specs: list[dict[str, Any]] = []
    for path in files:
        slug = _safe_token(path.replace("/", "_").replace(".lean", ""), max_len=80).lower()
        tr, delta = _lean_transform(path)

        specs.append(
            {
                "hypothesis_id": f"H_deep_lean_gate_{slug}_v1",
                "mechanism_change": f"Promote theorem-carrying gate: `{path}` must compile before approving related mechanism changes.",
                "representation_shift_used": tr,
                "expected_metric_delta": delta,
                "null_hypothesis": f"`{path}` does not compile reliably in local Mathlib toolchain.",
                "falsification_recipe": f"lean_pass::{path}",
                "support_recipe": f"lean_pass::{path}",
                "formal_obligations": [
                    f"`{path}` compiles under local lake/mathlib wiring",
                    "No UNKNOWN/TIMEOUT is treated as proof of correctness",
                    "Proof obligation remains deterministic under replay",
                ],
                "risk_modes": [
                    "Proof compiles but code invariant mapping is incomplete",
                    "Mathlib toolchain drift invalidates assumption",
                ],
                "status": "proposed",
                "timeout_s": 240,
            }
        )
        specs.append(
            {
                "hypothesis_id": f"H_deep_lean_counterclaim_{slug}_v1",
                "mechanism_change": f"Counterclaim: `{path}` is currently unprovable/unbuildable and cannot be used as a valid gate.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": f"`{path}` is buildable and proof-carrying in this toolchain.",
                "falsification_recipe": f"lean_fail::{path}",
                "support_recipe": f"lean_fail::{path}",
                "formal_obligations": [
                    f"Produce deterministic compile failure for `{path}`",
                    "Failure must be semantic/toolchain-relevant, not transient IO",
                ],
                "risk_modes": [
                    "False negative from temporary environment issue",
                    "Misclassifying setup errors as theorem failure",
                ],
                "status": "proposed",
                "timeout_s": 240,
            }
        )
        specs.append(
            {
                "hypothesis_id": f"H_deep_lean_replay3_{slug}_v1",
                "mechanism_change": f"Require 3x deterministic replay for `{path}` before claiming formal stability.",
                "representation_shift_used": "reduce",
                "expected_metric_delta": [1, 0, 1, -1, 2],
                "null_hypothesis": f"`{path}` is not stable across repeated formal replay.",
                "falsification_recipe": f"lean_repeat3::{path}",
                "support_recipe": f"lean_repeat3::{path}",
                "formal_obligations": [
                    "Three consecutive proof replays succeed",
                    "No replay uses UNKNOWN/TIMEOUT as support",
                ],
                "risk_modes": [
                    "Replay stability still under-approximates full proof ecosystem",
                    "Additional compute cost",
                ],
                "status": "proposed",
                "timeout_s": 360,
            }
        )
    return specs


def _deep_esso_specs(kernels: list[str]) -> list[dict[str, Any]]:
    specs: list[dict[str, Any]] = []
    for path in kernels:
        slug = _safe_token(path.replace("/", "_").replace(".yaml", ""), max_len=80).lower()
        tr, delta = _kernel_transform(path)

        specs.append(
            {
                "hypothesis_id": f"H_deep_esso_gate_{slug}_v1",
                "mechanism_change": f"Require ESSO verify-multi gate on `{path}` as a fail-closed formal acceptance condition.",
                "representation_shift_used": tr,
                "expected_metric_delta": delta,
                "null_hypothesis": f"`{path}` does not verify under deterministic ESSO posture.",
                "falsification_recipe": f"esso_verify::{path}",
                "support_recipe": f"esso_verify::{path}",
                "formal_obligations": [
                    "ESSO verify-multi returns VERIFIED",
                    "No UNKNOWN/TIMEOUT accepted as support",
                    "Determinism-trial posture remains consistent",
                ],
                "risk_modes": [
                    "Solver posture sensitivity",
                    "Kernel assumptions may be incomplete vs production composition",
                ],
                "status": "proposed",
                "timeout_s": 240,
            }
        )
        specs.append(
            {
                "hypothesis_id": f"H_deep_esso_counterclaim_{slug}_v1",
                "mechanism_change": f"Counterclaim: `{path}` cannot currently pass deterministic ESSO verification.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": f"`{path}` is ESSO-verifiable under deterministic posture.",
                "falsification_recipe": f"esso_fail::{path}",
                "support_recipe": f"esso_fail::{path}",
                "formal_obligations": [
                    "Deterministic ESSO failure witness exists",
                    "Failure is reproducible under fixed solver posture",
                ],
                "risk_modes": [
                    "False negatives from solver timeout posture",
                    "Misreading setup errors as model-level failures",
                ],
                "status": "proposed",
                "timeout_s": 240,
            }
        )
        specs.append(
            {
                "hypothesis_id": f"H_deep_esso_replay2_{slug}_v1",
                "mechanism_change": f"Require two successful ESSO replays on `{path}` before formal promotion.",
                "representation_shift_used": "reduce",
                "expected_metric_delta": [1, 0, 1, -1, 2],
                "null_hypothesis": f"`{path}` is unstable across repeated ESSO verification.",
                "falsification_recipe": f"esso_repeat2::{path}",
                "support_recipe": f"esso_repeat2::{path}",
                "formal_obligations": [
                    "Two consecutive ESSO verification passes",
                    "No inconclusive verdict admitted as support",
                ],
                "risk_modes": [
                    "Repeated verification still bounded",
                    "Additional runtime overhead",
                ],
                "status": "proposed",
                "timeout_s": 300,
            }
        )
    return specs


def _validate_specs(specs: list[dict[str, Any]]) -> None:
    required = {
        "hypothesis_id",
        "mechanism_change",
        "representation_shift_used",
        "expected_metric_delta",
        "null_hypothesis",
        "falsification_recipe",
        "support_recipe",
        "formal_obligations",
        "risk_modes",
        "status",
    }
    seen: set[str] = set()
    for row in specs:
        miss = [k for k in required if k not in row]
        if miss:
            raise ValueError(f"missing fields {miss} in {row.get('hypothesis_id')}")
        hid = str(row["hypothesis_id"])
        if hid in seen:
            raise ValueError(f"duplicate hypothesis_id: {hid}")
        seen.add(hid)
        tr = str(row["representation_shift_used"])
        if tr not in VALID_TRANSFORMS:
            raise ValueError(f"invalid transform {tr} ({hid})")


def main() -> int:
    ap = argparse.ArgumentParser(description="Generate a deep, formally-testable hypothesis pack for supervised ZenoDEX cycles.")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--target", type=int, default=100)
    ap.add_argument("--cycle-index", type=int, default=1)
    ap.add_argument("--lean-files", type=int, default=12)
    ap.add_argument("--kernel-files", type=int, default=8)
    args = ap.parse_args()

    target = max(1, int(args.target))
    cycle_index = max(1, int(args.cycle_index))
    lean_n = max(0, int(args.lean_files))
    kernel_n = max(0, int(args.kernel_files))

    base = _base_specs()
    lean_all = _discover_lean_files()
    kernels_all = _discover_kernel_files()

    lean_offset = 0 if not lean_all else ((cycle_index - 1) * max(1, lean_n)) % len(lean_all)
    kernel_offset = 0 if not kernels_all else ((cycle_index - 1) * max(1, kernel_n)) % len(kernels_all)
    lean_slice = _slice_window(lean_all, lean_offset, lean_n)
    kernel_slice = _slice_window(kernels_all, kernel_offset, kernel_n)

    deep = []
    deep.extend(_deep_lean_specs(lean_slice))
    deep.extend(_deep_esso_specs(kernel_slice))

    specs: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in base + deep:
        hid = str(row.get("hypothesis_id", ""))
        if not hid or hid in seen:
            continue
        seen.add(hid)
        specs.append(row)

    if len(specs) > target:
        specs = specs[:target]

    # If under target, round-robin duplicate deep families from remaining files with cycle-based shift.
    if len(specs) < target and (lean_all or kernels_all):
        need = target - len(specs)
        extra_lean = max(0, math.ceil(need / 6.0))
        extra_kernel = max(0, math.ceil(need / 6.0))
        lean_extra = _slice_window(lean_all, lean_offset + lean_n, extra_lean)
        kernel_extra = _slice_window(kernels_all, kernel_offset + kernel_n, extra_kernel)
        extras = _deep_lean_specs(lean_extra) + _deep_esso_specs(kernel_extra)
        for row in extras:
            hid = str(row.get("hypothesis_id", ""))
            if not hid or hid in seen:
                continue
            seen.add(hid)
            specs.append(row)
            if len(specs) >= target:
                break

    _validate_specs(specs)

    payload = {
        "schema": "zenodex/deep-hypothesis-pack/v1",
        "generated_at": _now_iso(),
        "cycle_index": cycle_index,
        "target": target,
        "base_count": len(base),
        "lean_pool": len(lean_all),
        "kernel_pool": len(kernels_all),
        "lean_selected": lean_slice,
        "kernel_selected": kernel_slice,
        "hypotheses": specs,
    }
    out_path = (ROOT / args.out).resolve() if not Path(args.out).is_absolute() else Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"ok": True, "out": str(out_path), "count": len(specs)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
