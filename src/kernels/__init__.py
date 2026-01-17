"""
Kernel layer.

This package groups the *non-Tau* deterministic kernels used by the DEX.
- `src/kernels/dex/` contains kernel specs (.yaml) and CE corpora (.jsonl).
- `src/kernels/python/` contains production Python kernels (human-readable) that
  implement the same semantics and are parity-tested against generated reference
  code (bounded domains).
"""
