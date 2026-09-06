# ASSET transfer custody successor specification subject

The adjacent `asset-transfer-custody-semantic-bundle-v1.json` defines a candidate
specification subject for the custody-complete transfer implementation. It
records the fixed transfer-step contract reviewed in
[the custody repair design](../research/ZENODEX_WHOLE_PROGRAM_V3_CUSTODY_REPAIR_DESIGN.md).
It does not select an active release or complete any lane lifecycle.

The physical equation is account total + custody total = supply. Transfer keeps
the custody table unchanged and derives both completed conservation scalars
from the exact pre/post projections. Claimant liabilities remain unchanged and
subject to the existing backing checks; they do not enter the physical supply
sum. The restricted global allocation relation requires empty reserves.

The bundle preserves the existing V1 wires, guards, flat-fee policy inputs,
alias aggregation, bounds and canonical rows. It does not choose custody
owners, claimant identities, control domains, initialization, deposit or
withdrawal policy, or migration. The existing sender-as-fee-owner global
fee-mirror refusal is retained.

## Canonical identity

The JSON file is exactly 3,333 canonical bytes with no trailing newline. Its
SHA-256 is
`4b16964671cd4e4f4585437ad632eb5aa13fee17a5f49c65a96b59335b43ba72`.
Its specification root is
`0x02e297f6d65affbae54509516e6c5816e60e994ef2c674495884072cd0939df1`.
Derive that root using `hash_global_v1` under the domain
`zenodex/asset-transfer-custody-semantic-bundle/v1` and the decoded canonical
JSON value. The root commits semantic text; it contains no source hash,
toolchain identity, measured image, release ID or activation status.

Replay from the repository root:

```bash
python3 -B - <<'PY'
import hashlib
import json
from pathlib import Path
from src.core.global_settlement_types_v1 import canonical_global_bytes_v1, hash_global_v1

path = Path("docs/specifications/asset-transfer-custody-semantic-bundle-v1.json")
raw = path.read_bytes()
value = json.loads(raw)
if raw != canonical_global_bytes_v1(value):
    raise ValueError("noncanonical specification bytes")
expected_sha = "4b16964671cd4e4f4585437ad632eb5aa13fee17a5f49c65a96b59335b43ba72"
expected_root = "0x02e297f6d65affbae54509516e6c5816e60e994ef2c674495884072cd0939df1"
if hashlib.sha256(raw).hexdigest() != expected_sha:
    raise ValueError("specification byte subject mismatch")
if hash_global_v1(value["schema"], value) != expected_root:
    raise ValueError("specification root mismatch")
print("canonical specification subject verified")
PY
```

## Selection and remaining work

The successor module, its ASSET coordinator and its single-ASSET route must
carry this same specification subject. Selection binds the occurrence's
governed route, its module release membership and the coordinator selected
from the profile-bound registry. Module admission remains module-level. The
native route additionally binds the coordinator context and checks lane/global
composition. No coordinator-release field is added to the route wire.

Unknown or mixed subjects must reject before transition recomputation or
receipt calls. Tests must rebuild changed release IDs, registry roots, profile
IDs and occurrences coherently to isolate semantic refusals. Legacy entry
points retain their existing behavior. New image/profile verification remains
necessary even when zero custody makes the projected movement equal.

This artifact received independent source-level review and canonical-root
replay. It is data, with no authority. The corresponding closed selectors,
receipt bindings and native route are implementation work. Measured guests,
genuine receipts, whole-runtime refinement, release qualification and any
activation or migration remain separate obligations.
