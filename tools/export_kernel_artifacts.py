#!/usr/bin/env python3
"""
Regenerate kernel artifacts derived from YAML state-machine specs.

This repo uses an optional private spec toolchain to validate/verify kernel specs
and export standalone reference implementations.
This script regenerates those checked-in artifacts (Python refs + optional Rust crates).

Goals:
- One deterministic command to refresh generated refs used in parity tests.
- Optional formatting when available:
  - Python: ruff or black (if installed)
  - Rust: cargo fmt (if cargo is installed)

This script does NOT read any signing keys; if you pass key paths through to the
toolchain, they are forwarded without opening the files here.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
ESSO_ROOT = REPO_ROOT / "external" / "ESSO"
KERNEL_DIR = REPO_ROOT / "src" / "kernels" / "dex"
GENERATED_DIR = REPO_ROOT / "generated"


@dataclass(frozen=True)
class KernelExport:
    model_path: Path
    python_out_dir: Path

    @property
    def model_id(self) -> str:
        return self.model_path.stem


DEFAULT_EXPORTS: tuple[KernelExport, ...] = (
    KernelExport(KERNEL_DIR / "cpmm_swap.yaml", GENERATED_DIR / "cpmm_python"),
    KernelExport(KERNEL_DIR / "liquidity_pool.yaml", GENERATED_DIR / "liquidity_python"),
    KernelExport(KERNEL_DIR / "cpmm_swap_v7.yaml", GENERATED_DIR / "dex_v7_python"),
    KernelExport(KERNEL_DIR / "fee_calculation_v7.yaml", GENERATED_DIR / "dex_v7_python"),
    KernelExport(KERNEL_DIR / "lp_mint_v7.yaml", GENERATED_DIR / "dex_v7_python"),
    KernelExport(KERNEL_DIR / "lp_ratio_calculator_v7.yaml", GENERATED_DIR / "dex_v7_python"),
    KernelExport(KERNEL_DIR / "circuit_breaker_v7.yaml", GENERATED_DIR / "dex_v7_python"),
    KernelExport(KERNEL_DIR / "cpmm_swap_v8.yaml", GENERATED_DIR / "dex_v8_python"),
    KernelExport(KERNEL_DIR / "vault_manager.yaml", GENERATED_DIR / "vault_python"),
    KernelExport(KERNEL_DIR / "perp_epoch_isolated_v2.yaml", GENERATED_DIR / "perp_python"),
    KernelExport(KERNEL_DIR / "perp_epoch_clearinghouse_2p_v0_1.yaml", GENERATED_DIR / "perp_python"),
    KernelExport(KERNEL_DIR / "perp_epoch_clearinghouse_3p_transfer_v0_1.yaml", GENERATED_DIR / "perp_python"),
    KernelExport(KERNEL_DIR / "funding_rate_market_v1.yaml", GENERATED_DIR / "derivatives_python"),
    KernelExport(KERNEL_DIR / "funding_rate_market_v1_1.yaml", GENERATED_DIR / "derivatives_python"),
    KernelExport(KERNEL_DIR / "il_futures_market_v1.yaml", GENERATED_DIR / "derivatives_python"),
    KernelExport(KERNEL_DIR / "curve_selection_market_v1.yaml", GENERATED_DIR / "derivatives_python"),
)


def _ensure_esso() -> None:
    if not ESSO_ROOT.exists():
        raise SystemExit(f"toolchain not found at {ESSO_ROOT}. Clone/update external/ESSO.")


def _env_with_esso() -> dict[str, str]:
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ESSO_ROOT) + (os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    # Reduce nondeterminism in codegen: some tooling may iterate over hash-based containers.
    env["PYTHONHASHSEED"] = "0"
    return env


def _run(cmd: Sequence[str], *, cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=True)


def _tool_available(cmd: Sequence[str]) -> bool:
    try:
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        return True
    except Exception:
        return False


def _format_python(paths: Iterable[Path]) -> None:
    # Prefer ruff (fast), then black.
    if _tool_available([sys.executable, "-m", "ruff", "--version"]):
        _run([sys.executable, "-m", "ruff", "format", *[str(p) for p in paths]])
        return
    if _tool_available([sys.executable, "-m", "black", "--version"]):
        _run([sys.executable, "-m", "black", *[str(p) for p in paths]])


def _format_rust(crate_dirs: Iterable[Path]) -> None:
    if not _tool_available(["cargo", "--version"]):
        return
    for d in crate_dirs:
        manifest = d / "Cargo.toml"
        if not manifest.exists():
            continue
        _run(["cargo", "fmt", "--manifest-path", str(manifest)])


def _patch_toolchain_header(python_out_dir: Path) -> None:
    generated_by_new = "Generated from the YAML kernel spec by the repo's optional private toolchain."
    standalone_new = "This file is standalone and has no runtime dependency on the generator/toolchain."
    for p in sorted(python_out_dir.glob("*.py")):
        try:
            data = p.read_text(encoding="utf-8")
        except OSError:
            continue
        new_data = data
        new_data = new_data.replace(
            "Generated from the YAML kernel spec by the repo's optional spec toolchain "
            "(ESSO: Evolutionary State Space Optimizer).",
            generated_by_new,
        )
        new_data = new_data.replace("Generated by ESSO (Evolutionary Spec Search Optimizer)", generated_by_new)
        new_data = new_data.replace("Generated by ESSO (Evolutionary State Space Optimizer)", generated_by_new)
        new_data = new_data.replace("Generated from the YAML kernel spec by the repo's optional spec toolchain.", generated_by_new)
        new_data = new_data.replace("This file is standalone and has no ESSO dependencies.", standalone_new)
        if new_data != data:
            p.write_text(new_data, encoding="utf-8")


def _select_exports(exports: Sequence[KernelExport], selected: Sequence[str] | None) -> list[KernelExport]:
    if not selected:
        return list(exports)
    want = {s.strip() for s in selected if s.strip()}
    out: list[KernelExport] = []
    for ex in exports:
        if ex.model_id in want or ex.model_path.name in want:
            out.append(ex)
    missing = sorted(want - {ex.model_id for ex in out} - {ex.model_path.name for ex in out})
    if missing:
        raise SystemExit(f"unknown model ids/paths: {', '.join(missing)}")
    return out


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", nargs="*", help="Subset by model_id or filename (e.g. cpmm_swap_v8)")
    parser.add_argument("--no-python", action="store_true", help="Skip export-python")
    parser.add_argument("--patch-headers", action="store_true", help="Patch toolchain-related headers in existing refs")
    parser.add_argument("--rust", action="store_true", help="Also run codegen-rust-kernel into generated/<model_id>/")
    parser.add_argument("--no-format", action="store_true", help="Skip formatter steps")
    args = parser.parse_args(argv)

    exports = _select_exports(DEFAULT_EXPORTS, args.models)

    python_out_dirs: set[Path] = set()
    rust_crates: list[Path] = []

    toolchain_needed = (not args.no_python) or bool(args.rust)
    if toolchain_needed:
        _ensure_esso()
        env = _env_with_esso()
    else:
        env = dict(os.environ)

    for ex in exports:
        if not ex.model_path.exists():
            raise SystemExit(f"missing model: {ex.model_path}")
        ex.python_out_dir.mkdir(parents=True, exist_ok=True)

        if not args.no_python:
            subprocess.run(
                [sys.executable, "-m", "ESSO", "export-python", str(ex.model_path), "--output", str(ex.python_out_dir)],
                cwd=str(REPO_ROOT),
                env=env,
                check=True,
            )
            _patch_toolchain_header(ex.python_out_dir)
            python_out_dirs.add(ex.python_out_dir)
        elif args.patch_headers:
            _patch_toolchain_header(ex.python_out_dir)
            python_out_dirs.add(ex.python_out_dir)

        if args.rust:
            subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "ESSO",
                    "codegen-rust-kernel",
                    str(ex.model_path),
                    "--output-root",
                    str(GENERATED_DIR),
                ],
                cwd=str(REPO_ROOT),
                env=env,
                check=True,
            )
            rust_crates.append(GENERATED_DIR / ex.model_id)

    if not args.no_format:
        _format_python(sorted(python_out_dirs))
        _format_rust(rust_crates)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
