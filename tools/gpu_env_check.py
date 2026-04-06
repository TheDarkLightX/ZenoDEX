#!/usr/bin/env python3
"""
GPU environment check (internal).

Purpose:
- Detect whether CUDA (NVIDIA) and/or Torch GPU backends are available.
- Print a short, actionable summary + suggested install commands.

This script is intentionally *non-consensus-critical* and must not be imported by `src/core/`.
"""

from __future__ import annotations

import os
import platform
import subprocess
import sys
from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class TorchInfo:
    version: str
    cuda_available: bool
    cuda_device: Optional[str]
    mps_available: bool


@dataclass(frozen=True)
class CupyInfo:
    version: str
    device_count: int
    device0: Optional[str]


def _run(cmd: list[str]) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, check=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        return int(p.returncode), str(p.stdout or "")
    except FileNotFoundError:
        return 127, ""


def _nvidia_smi_summary() -> Optional[str]:
    code, out = _run(["nvidia-smi", "-L"])
    if code != 0:
        return None
    out = out.strip()
    return out if out else None


def _nvcc_summary() -> Optional[str]:
    code, out = _run(["nvcc", "--version"])
    if code != 0:
        return None
    # Keep only the last few lines (version + build info).
    lines = [ln.rstrip() for ln in out.splitlines() if ln.strip()]
    if not lines:
        return None
    return "\n".join(lines[-6:])


def _torch_info() -> Optional[TorchInfo]:
    try:
        import torch  # type: ignore
    except Exception:
        return None

    cuda_ok = bool(getattr(torch, "cuda", None)) and bool(torch.cuda.is_available())
    cuda_device: Optional[str] = None
    if cuda_ok:
        try:
            cuda_device = str(torch.cuda.get_device_name(0))
        except Exception:
            cuda_device = None

    mps = getattr(getattr(torch, "backends", None), "mps", None)
    mps_ok = bool(mps) and bool(getattr(mps, "is_available", lambda: False)())

    return TorchInfo(
        version=str(getattr(torch, "__version__", "unknown")),
        cuda_available=bool(cuda_ok),
        cuda_device=cuda_device,
        mps_available=bool(mps_ok),
    )


def _cupy_info() -> Optional[CupyInfo]:
    try:
        import cupy  # type: ignore
    except Exception:
        return None

    n = 0
    try:
        n = int(cupy.cuda.runtime.getDeviceCount())
    except Exception:
        n = 0

    dev0: Optional[str] = None
    if n > 0:
        try:
            raw = cupy.cuda.runtime.getDeviceProperties(0).get("name")
            if isinstance(raw, (bytes, bytearray)):
                dev0 = raw.decode(errors="replace")
            elif raw is None:
                dev0 = None
            else:
                dev0 = str(raw)
        except Exception:
            dev0 = None

    return CupyInfo(version=str(getattr(cupy, "__version__", "unknown")), device_count=int(n), device0=dev0)


def main() -> int:
    sys.stdout.write("=== GPU Env Check (ZenoDEX) ===\n")
    sys.stdout.write(f"python={sys.version.split()[0]} platform={platform.system()} arch={platform.machine()}\n")
    sys.stdout.write(f"cwd={os.getcwd()}\n")

    smi = _nvidia_smi_summary()
    if smi is not None:
        sys.stdout.write("\n[nvidia-smi]\n")
        sys.stdout.write(smi + "\n")
    else:
        sys.stdout.write("\n[nvidia-smi]\nnot found or no NVIDIA GPU detected\n")

    nvcc = _nvcc_summary()
    if nvcc is not None:
        sys.stdout.write("\n[nvcc]\n")
        sys.stdout.write(nvcc + "\n")
    else:
        sys.stdout.write("\n[nvcc]\nnot found\n")

    ti = _torch_info()
    if ti is None:
        sys.stdout.write("\n[torch]\nnot installed\n")
    else:
        sys.stdout.write("\n[torch]\n")
        sys.stdout.write(f"version={ti.version}\n")
        sys.stdout.write(f"cuda_available={ti.cuda_available}\n")
        if ti.cuda_available:
            sys.stdout.write(f"cuda_device={ti.cuda_device or 'unknown'}\n")
        sys.stdout.write(f"mps_available={ti.mps_available}\n")

    ci = _cupy_info()
    if ci is None:
        sys.stdout.write("\n[cupy]\nnot installed\n")
    else:
        sys.stdout.write("\n[cupy]\n")
        sys.stdout.write(f"version={ci.version}\n")
        sys.stdout.write(f"device_count={ci.device_count}\n")
        if ci.device_count > 0:
            sys.stdout.write(f"device0={ci.device0 or 'unknown'}\n")

    sys.stdout.write("\n[recommended installs]\n")
    sys.stdout.write("- Linux + NVIDIA (CUDA):\n")
    sys.stdout.write("  1) Try CUDA wheels (PyTorch):\n")
    sys.stdout.write("     python3 -m pip install --upgrade torch --index-url https://download.pytorch.org/whl/cu124\n")
    sys.stdout.write("  2) If that fails, try cu121:\n")
    sys.stdout.write("     python3 -m pip install --upgrade torch --index-url https://download.pytorch.org/whl/cu121\n")
    sys.stdout.write("  3) Smaller alternative backend (CuPy):\n")
    sys.stdout.write("     python3 -m pip install --upgrade cupy-cuda12x\n")
    sys.stdout.write("- macOS (Apple Silicon):\n")
    sys.stdout.write("  python3 -m pip install --upgrade torch\n")

    ok = False
    if ti is not None and (ti.cuda_available or ti.mps_available):
        ok = True
    if ci is not None and ci.device_count > 0:
        ok = True

    # Treat torch/cupy as the primary backends for our GPU tools.
    sys.stdout.write(f"\nstatus={'OK' if ok else 'MISSING_GPU_BACKEND'}\n")
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
