#!/usr/bin/env python3
"""Compose super_all_ok from component REPL outputs."""
from pathlib import Path

def read_bits(path: Path):
    if not path.exists():
        raise FileNotFoundError(path)
    bits = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        if line not in {"0", "1"}:
            raise ValueError(f"Non-binary value '{line}' in {path}")
        bits.append(int(line))
    return bits

def main():
    base = Path(__file__).resolve().parent
    outs = base / "outputs"
    batch = read_bits(outs / "batch_all_ok.out")
    stable = read_bits(outs / "price_stable.out")
    risk = read_bits(outs / "can_trade.out")

    n = min(len(batch), len(stable), len(risk))
    if n == 0:
        raise RuntimeError("No data to compose")

    super_ok = [1 if (batch[i] and stable[i] and risk[i]) else 0 for i in range(n)]

    out_path = outs / "super_all_ok.out"
    out_path.write_text("\n".join(str(v) for v in super_ok) + "\n")

    print(f"Wrote {out_path} ({n} rows)")

if __name__ == "__main__":
    main()
