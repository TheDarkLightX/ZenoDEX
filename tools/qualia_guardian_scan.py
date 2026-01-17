#!/usr/bin/env python3

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


ROOT = Path(__file__).resolve().parents[1]


def _add_qualia_to_syspath() -> Optional[Path]:
    qualia_root = ROOT / "external" / "QualiaGuardian"
    if not qualia_root.is_dir():
        return None
    if str(qualia_root) not in sys.path:
        sys.path.insert(0, str(qualia_root))
    return qualia_root


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def _default_scan_paths() -> List[Path]:
    return [
        ROOT / "tools" / "tau_testnet_local_smoke.py",
        ROOT / "tools" / "tau_testnet_local_e2e.py",
        ROOT / "src" / "integration" / "tau_testnet_dex_plugin.py",
        ROOT / "src" / "integration" / "tau_net_client.py",
        ROOT / "external" / "tau-testnet" / "app_bridge.py",
        ROOT / "external" / "tau-testnet" / "state_proof.py",
    ]


def _run_static_analysis(
    *,
    file_path: Path,
    code: str,
    max_function_lines: int,
    max_class_methods: int,
) -> Dict[str, Any]:
    from guardian.analysis.static import (  # type: ignore[import-not-found]
        calculate_cyclomatic_complexity,
        find_large_classes,
        find_long_elements,
    )

    avg_cc = float(calculate_cyclomatic_complexity(code))
    long_elements = find_long_elements(code, max_lines=int(max_function_lines))
    large_classes = find_large_classes(code, max_methods=int(max_class_methods))
    return {
        "avg_cyclomatic_complexity": avg_cc,
        "long_elements": long_elements,
        "large_classes": large_classes,
    }


def _run_security_scan(*, code: str) -> Dict[str, Any]:
    from guardian.analysis.security import (  # type: ignore[import-not-found]
        check_for_eval_usage,
        check_for_hardcoded_secrets,
    )

    return {
        "eval_usage": check_for_eval_usage(code),
        "hardcoded_secrets": check_for_hardcoded_secrets(code),
    }


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="QualiaGuardian-assisted static quality scan (best-effort, no network).")
    parser.add_argument(
        "--paths",
        nargs="*",
        default=None,
        help="Optional explicit file paths to scan. Defaults to key Tau integration files.",
    )
    parser.add_argument("--max-function-lines", type=int, default=120)
    parser.add_argument("--max-class-methods", type=int, default=25)
    args = parser.parse_args(argv)

    qualia_root = _add_qualia_to_syspath()
    if qualia_root is None:
        print("[qualia] external/QualiaGuardian not found.")
        print("[qualia] Clone it with:")
        print("         git clone --depth 1 https://github.com/TheDarkLightX/QualiaGuardian.git external/QualiaGuardian")
        return 2

    scan_paths: List[Path]
    if args.paths:
        scan_paths = [Path(p).expanduser().resolve() for p in args.paths]
    else:
        scan_paths = _default_scan_paths()

    missing = [p for p in scan_paths if not p.is_file()]
    if missing:
        for p in missing:
            print(f"[qualia] missing file: {p}")
        return 2

    try:
        _ = __import__("guardian.analysis.static")
        static_ok = True
    except Exception as exc:
        static_ok = False
        print(f"[qualia] static analysis unavailable ({exc}).")
        print("[qualia] Hint: ensure `radon` is installed for the Python running this script.")

    try:
        _ = __import__("guardian.analysis.security")
        security_ok = True
    except Exception as exc:
        security_ok = False
        print(f"[qualia] security scan unavailable ({exc}).")

    findings = 0
    for path in scan_paths:
        code = _read_text(path)
        print(f"\n[qualia] file={path}")

        if static_ok:
            try:
                res = _run_static_analysis(
                    file_path=path,
                    code=code,
                    max_function_lines=int(args.max_function_lines),
                    max_class_methods=int(args.max_class_methods),
                )
            except Exception as exc:
                print(f"[qualia] static analysis error: {exc}")
            else:
                print(f"[qualia] avg_cc={res['avg_cyclomatic_complexity']:.2f}")
                if res["long_elements"]:
                    findings += len(res["long_elements"])
                    print(f"[qualia] long_elements>{args.max_function_lines} lines:")
                    for e in res["long_elements"]:
                        print(
                            f"         - {e.get('type')} {e.get('name')} lines={e.get('lines')} "
                            f"lineno={e.get('lineno')} endline={e.get('endline')}"
                        )
                if res["large_classes"]:
                    findings += len(res["large_classes"])
                    print(f"[qualia] large_classes>{args.max_class_methods} methods:")
                    for c in res["large_classes"]:
                        print(
                            f"         - class {c.get('name')} methods={c.get('methods')} "
                            f"lineno={c.get('lineno')} endline={c.get('endline')}"
                        )

        if security_ok:
            try:
                sec = _run_security_scan(code=code)
            except Exception as exc:
                print(f"[qualia] security scan error: {exc}")
            else:
                if sec["eval_usage"]:
                    findings += len(sec["eval_usage"])
                    print("[qualia] eval usage:")
                    for f in sec["eval_usage"]:
                        print(f"         - line {f.get('line_number')}: {f.get('line_content')}")
                if sec["hardcoded_secrets"]:
                    kept = []
                    for f in sec["hardcoded_secrets"]:
                        # Qualia's generic secret regex can flag SQL like: WHERE key='state_proof'
                        # Keep the report useful by filtering obvious false positives.
                        line = str(f.get("line_content") or "")
                        if f.get("pattern_name") == "GENERIC_KEY" and "chain_state WHERE key=" in line:
                            continue
                        kept.append(f)
                    if kept:
                        findings += len(kept)
                        print("[qualia] potential hardcoded secrets:")
                    for f in kept:
                        print(
                            f"         - line {f.get('line_number')}: {f.get('pattern_name')} "
                            f"{f.get('matched_value_preview')}"
                        )

    print(f"\n[qualia] done. findings={findings}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
