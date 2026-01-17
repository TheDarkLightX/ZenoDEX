#!/usr/bin/env python3
from pathlib import Path

def read_ints(path: Path):
    return [line.strip() for line in path.read_text().splitlines() if line.strip() != ""]

base = Path("experiments/io/outputs")
auction = read_ints(base / "auction_ok.out")
twap = read_ints(base / "twap_ok.out")
fire = read_ints(base / "oracle_fire.out")
cpmm = read_ints(base / "cpmm8_valid.out")
risk = read_ints(base / "can_trade.out")

n = min(len(auction), len(twap), len(fire), len(cpmm), len(risk))

out_lines = []
for i in range(n):
    ok = (auction[i] == "1") and (twap[i] == "1") and (fire[i] == "1") and (cpmm[i] == "1") and (risk[i] == "1")
    out_lines.append("1" if ok else "0")

(base / "auction_twap_nonce_cpmm_risk_super.out").write_text("\n".join(out_lines) + "\n")
