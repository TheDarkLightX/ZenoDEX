#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MODEL_DIR = ROOT / "formal" / "tla"
DEFAULT_LOG_DIR = ROOT / "runs" / "tla"
DEFAULT_JAR = ROOT / "external" / "tla-tools" / "tla2tools.jar"


class TlaModelError(RuntimeError):
    pass


def _find_java(explicit: str | None) -> str:
    if explicit:
        return explicit
    java = shutil.which("java")
    if java:
        return java
    raise TlaModelError("java not found; install a JRE/JDK before running TLC")


def _find_tla_jar(explicit: Path | None) -> Path:
    env_jar = os.environ.get("TLA_JAR")
    path = explicit or (Path(env_jar) if env_jar else DEFAULT_JAR)
    if path.is_file():
        return path
    raise TlaModelError(
        f"TLC jar not found at {path}. Run 'bash tools/install_tla_tools.sh', set TLA_JAR, or set --tla-jar."
    )


def _discover_models(model_dir: Path) -> list[tuple[str, Path, Path]]:
    out: list[tuple[str, Path, Path]] = []
    for cfg in sorted(model_dir.glob("*.cfg")):
        tla = cfg.with_suffix(".tla")
        if not tla.is_file():
            raise TlaModelError(f"missing TLA module for config {cfg}: expected {tla}")
        out.append((cfg.stem, cfg, tla))
    if not out:
        raise TlaModelError(f"no .cfg models found under {model_dir}")
    return out


def run_tla_models(
    *,
    model_dir: Path = DEFAULT_MODEL_DIR,
    log_dir: Path = DEFAULT_LOG_DIR,
    tla_jar: Path | None = None,
    java_bin: str | None = None,
    timeout_s: int = 120,
) -> dict[str, Any]:
    model_dir = model_dir.resolve()
    log_dir = log_dir.resolve()
    log_dir.mkdir(parents=True, exist_ok=True)

    jar = _find_tla_jar(tla_jar.resolve() if tla_jar else None)
    java = _find_java(java_bin)
    models = _discover_models(model_dir)

    results: list[dict[str, Any]] = []
    errors: list[str] = []
    for name, cfg, tla in models:
        log_path = log_dir / f"{name}.log"
        cmd = [
            java,
            "-XX:+UseParallelGC",
            "-cp",
            str(jar),
            "tlc2.TLC",
            "-cleanup",
            "-config",
            str(cfg),
            str(tla),
        ]
        start = time.monotonic()
        with log_path.open("w", encoding="utf-8") as fh:
            proc = subprocess.run(
                cmd,
                stdout=fh,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=timeout_s,
                cwd=ROOT,
                check=False,
            )
        duration_s = round(time.monotonic() - start, 3)
        result = {
            "name": name,
            "cfg": str(cfg.relative_to(ROOT)),
            "module": str(tla.relative_to(ROOT)),
            "log_path": str(log_path.relative_to(ROOT)),
            "duration_s": duration_s,
            "returncode": proc.returncode,
            "ok": proc.returncode == 0,
        }
        results.append(result)
        if proc.returncode != 0:
            errors.append(f"{name}: TLC exited with {proc.returncode} (see {result['log_path']})")

    return {
        "schema": "zenodex/tla-model-run/v1",
        "ok": not errors,
        "model_count": len(results),
        "model_dir": str(model_dir.relative_to(ROOT)),
        "log_dir": str(log_dir.relative_to(ROOT)),
        "tla_jar": str(jar.relative_to(ROOT) if jar.is_relative_to(ROOT) else jar),
        "results": results,
        "errors": errors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run all bounded TLA+/TLC models under formal/tla.")
    parser.add_argument("--model-dir", type=Path, default=DEFAULT_MODEL_DIR)
    parser.add_argument("--log-dir", type=Path, default=DEFAULT_LOG_DIR)
    parser.add_argument("--tla-jar", type=Path, default=None)
    parser.add_argument("--java-bin", default=None)
    parser.add_argument("--timeout-s", type=int, default=120)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    try:
        result = run_tla_models(
            model_dir=args.model_dir,
            log_dir=args.log_dir,
            tla_jar=args.tla_jar,
            java_bin=args.java_bin,
            timeout_s=args.timeout_s,
        )
    except TlaModelError as exc:
        if args.json:
            print(json.dumps({"schema": "zenodex/tla-model-run/v1", "ok": False, "errors": [str(exc)]}, indent=2))
        else:
            print(f"error: {exc}")
        return 1
    except subprocess.TimeoutExpired as exc:
        message = f"TLC timed out after {args.timeout_s}s while running {exc.cmd[-1]}"
        if args.json:
            print(json.dumps({"schema": "zenodex/tla-model-run/v1", "ok": False, "errors": [message]}, indent=2))
        else:
            print(f"error: {message}")
        return 1

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        for entry in result["results"]:
            status = "ok" if entry["ok"] else "failed"
            print(f"{entry['name']}: {status} ({entry['duration_s']}s)")
        if result["ok"]:
            print("ok")
        else:
            for error in result["errors"]:
                print(f"error: {error}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
