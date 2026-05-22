from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.cantor_shapeforge_bridge_report import (  # noqa: E402
    DEFAULT_SHAPEFORGE_WORLD_MODEL_PATH,
    build_cantor_shapeforge_bridge_report,
)
from src.integration.cantor_shapeforge_bridge_verify import (  # noqa: E402
    verify_cantor_shapeforge_bridge_report_payload,
)
from tools.shapeforge_validate import validate_artifact  # noqa: E402


def check_cantor_shapeforge_promotion(
    *,
    world_model_path: Path = DEFAULT_SHAPEFORGE_WORLD_MODEL_PATH,
    output_report: Path | None = None,
) -> dict[str, Any]:
    errors = validate_artifact(world_model_path)
    if errors:
        raise ValueError("\n".join(errors))

    report = build_cantor_shapeforge_bridge_report(world_model_path=world_model_path)
    payload = report.to_dict()
    ok, err = verify_cantor_shapeforge_bridge_report_payload(payload, require_current=True)
    if not ok:
        raise ValueError(err or "bridge verification failed")

    if output_report is not None:
        output_report.parent.mkdir(parents=True, exist_ok=True)
        output_report.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return {
        "ok": True,
        "world_model_path": str(world_model_path),
        "world_model_id": payload["world_model_id"],
        "mapped_surface_count": payload["mapped_surface_count"],
        "unmapped_surface_count": payload["unmapped_surface_count"],
        "shared_bundle_sha256": payload["backend_invariance"]["shared_bundle_sha256"],
        "report_path": None if output_report is None else str(output_report),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Fail-closed validation for the promoted Cantor-to-ShapeForge evidence lane."
    )
    parser.add_argument(
        "--world-model",
        type=Path,
        default=DEFAULT_SHAPEFORGE_WORLD_MODEL_PATH,
        help="Path to the promoted ShapeForge world model JSON",
    )
    parser.add_argument(
        "--output-report",
        type=Path,
        help="Optional path to write the current deterministic bridge report JSON",
    )
    args = parser.parse_args(argv)

    try:
        result = check_cantor_shapeforge_promotion(
            world_model_path=args.world_model.resolve(),
            output_report=None if args.output_report is None else args.output_report.resolve(),
        )
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    print(
        "OK CantorShapeForgePromotion "
        f"world_model_id={result['world_model_id']} "
        f"mapped={result['mapped_surface_count']} "
        f"unmapped={result['unmapped_surface_count']} "
        f"bundle={result['shared_bundle_sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
