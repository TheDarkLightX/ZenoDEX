#!/usr/bin/env python3
"""Build the versioned v4 perps ESSO model and Python reference.

v4 is derived deterministically from v3. The only semantic transformation is
replacement of nested-floor initial/maintenance risk margins with one ceiling
division over the full scaled product. Fee, funding, PnL, bounty, and penalty
rounding are deliberately outside the matcher and remain unchanged.
"""

from __future__ import annotations

import argparse
import copy
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

import yaml  # type: ignore[import-untyped]

ROOT = Path(__file__).resolve().parents[1]
SOURCE_MODEL = ROOT / "src" / "kernels" / "dex" / "perp_epoch_isolated_v3.yaml"
TARGET_MODEL = ROOT / "src" / "kernels" / "dex" / "perp_epoch_isolated_v4.yaml"
TARGET_REF = ROOT / "generated" / "perp_python" / "perp_epoch_isolated_v4_ref.py"
EXPECTED_REPLACEMENTS = 43
PRICE_SCALE = 100_000_000
BPS_SCALE = 10_000
MARGIN_DENOMINATOR = PRICE_SCALE * BPS_SCALE


def _dealias(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: _dealias(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_dealias(item) for item in value]
    return copy.deepcopy(value)


def _is_var(value: Any, name: str) -> bool:
    return isinstance(value, dict) and value == {"var": name}


def _is_risk_rate(value: Any) -> bool:
    if _is_var(value, "initial_margin_bps"):
        return True
    return bool(
        isinstance(value, dict)
        and value.get("op") == "+"
        and value.get("args")
        == [
            {"var": "maintenance_margin_bps"},
            {"var": "depeg_buffer_bps"},
        ]
    )


def _match_nested_floor_margin(value: Any) -> tuple[Any, Any] | None:
    if not isinstance(value, dict) or value.get("op") != "div":
        return None
    outer_args = value.get("args")
    if not isinstance(outer_args, list) or len(outer_args) != 2:
        return None
    if outer_args[1] != {"const": BPS_SCALE}:
        return None
    product = outer_args[0]
    if not isinstance(product, dict) or product.get("op") != "*":
        return None
    product_args = product.get("args")
    if not isinstance(product_args, list) or len(product_args) != 2:
        return None
    notional_floor, rate = product_args
    if not _is_risk_rate(rate):
        return None
    if not isinstance(notional_floor, dict) or notional_floor.get("op") != "div":
        return None
    notional_args = notional_floor.get("args")
    if not isinstance(notional_args, list) or len(notional_args) != 2:
        return None
    if notional_args[1] != {"const": PRICE_SCALE}:
        return None
    return notional_args[0], rate


def _safe_ceil_margin(raw_notional_numerator: Any, rate: Any) -> dict[str, Any]:
    return {
        "op": "div",
        "args": [
            {
                "op": "+",
                "args": [
                    {
                        "op": "*",
                        "args": [raw_notional_numerator, rate],
                    },
                    {"const": MARGIN_DENOMINATOR - 1},
                ],
            },
            {"const": MARGIN_DENOMINATOR},
        ],
    }


def _count_matches(value: Any) -> int:
    matched = _match_nested_floor_margin(value)
    if matched is not None:
        return 1
    if isinstance(value, dict):
        return sum(_count_matches(item) for item in value.values())
    if isinstance(value, list):
        return sum(_count_matches(item) for item in value)
    return 0


def _transform_shared(value: Any, memo: dict[int, Any]) -> Any:
    if not isinstance(value, (dict, list)):
        return copy.deepcopy(value)
    identity = id(value)
    if identity in memo:
        return memo[identity]
    matched = _match_nested_floor_margin(value)
    if matched is not None:
        raw_notional_numerator, rate = matched
        result = _safe_ceil_margin(
            _transform_shared(raw_notional_numerator, memo),
            _transform_shared(rate, memo),
        )
        memo[identity] = result
        return result
    if isinstance(value, dict):
        result_dict: dict[str, Any] = {}
        memo[identity] = result_dict
        for key, item in value.items():
            result_dict[key] = _transform_shared(item, memo)
        return result_dict
    result_list: list[Any] = []
    memo[identity] = result_list
    result_list.extend(_transform_shared(item, memo) for item in value)
    return result_list


def render_v4_model() -> bytes:
    payload = yaml.safe_load(SOURCE_MODEL.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError("v3 model root must be a mapping")
    replacements = _count_matches(_dealias(payload))
    if replacements != EXPECTED_REPLACEMENTS:
        raise RuntimeError(
            f"risk-margin replacement count drifted: {replacements} != {EXPECTED_REPLACEMENTS}"
        )
    transformed = _transform_shared(payload, {})
    meta = transformed.get("meta")
    if not isinstance(meta, dict):
        raise TypeError("v3 model meta must be a mapping")
    meta["model_id"] = "perp_epoch_isolated_v4"
    meta["created_by"] = "zenodex-v4-margin-builder"
    meta["notes"] = (
        "Versioned successor to perp_epoch_isolated_v3. v4 uses a single ceiling "
        "division for initial and maintenance risk margins: "
        "ceil(abs(position_base) * price_e8 * margin_bps / 1e12). "
        "All other transition, fee, funding, PnL, bounty, and penalty semantics "
        "are inherited unchanged from v3."
    )
    header = (
        "# GENERATED by tools/build_perp_epoch_isolated_v4.py\n"
        "# Source: src/kernels/dex/perp_epoch_isolated_v3.yaml\n"
        "# Semantic delta: ceiling initial/maintenance risk margins only.\n"
    )
    body = yaml.safe_dump(
        transformed,
        allow_unicode=False,
        default_flow_style=False,
        sort_keys=False,
        width=120,
    )
    return (header + body).encode("utf-8")


def _export_reference(model_path: Path, output_dir: Path) -> Path:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH")
    esso_root = str(ROOT / "external" / "ESSO")
    env["PYTHONPATH"] = esso_root if not existing else f"{esso_root}:{existing}"
    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "ESSO",
            "export-python",
            str(model_path),
            "--output",
            str(output_dir),
        ],
        cwd=ROOT,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=180,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"ESSO export-python failed: {proc.stdout}{proc.stderr}")
    ref_path = output_dir / "perp_epoch_isolated_v4_ref.py"
    if not ref_path.is_file():
        raise FileNotFoundError(f"ESSO did not emit expected reference: {ref_path}")
    return ref_path


def build(*, check: bool) -> int:
    expected_model = render_v4_model()
    with tempfile.TemporaryDirectory(prefix="perp_v4_build_") as tmpdir:
        tmp_root = Path(tmpdir)
        tmp_model = tmp_root / TARGET_MODEL.name
        tmp_model.write_bytes(expected_model)
        tmp_ref = _export_reference(tmp_model, tmp_root / "python")
        expected_ref = tmp_ref.read_bytes()

    if check:
        errors = []
        if not TARGET_MODEL.is_file() or TARGET_MODEL.read_bytes() != expected_model:
            errors.append(f"stale model: {TARGET_MODEL}")
        if not TARGET_REF.is_file() or TARGET_REF.read_bytes() != expected_ref:
            errors.append(f"stale generated reference: {TARGET_REF}")
        if errors:
            for error in errors:
                print(f"ERROR: {error}", file=sys.stderr)
            return 1
        print("OK perp_epoch_isolated_v4 model and Python reference are current")
        return 0

    TARGET_MODEL.parent.mkdir(parents=True, exist_ok=True)
    TARGET_REF.parent.mkdir(parents=True, exist_ok=True)
    TARGET_MODEL.write_bytes(expected_model)
    TARGET_REF.write_bytes(expected_ref)
    print(f"wrote {TARGET_MODEL}")
    print(f"wrote {TARGET_REF}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build or check the versioned v4 perps model and Python reference."
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return build(check=args.check)


if __name__ == "__main__":
    raise SystemExit(main())
