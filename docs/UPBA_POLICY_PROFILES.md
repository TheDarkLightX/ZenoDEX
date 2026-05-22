# UPBA Policy Profiles

UPBA production pools should advertise one of three policy profiles:

- `conservative`
- `balanced`
- `fast`

Each profile states the maximum relative loss budget, absolute loss budget,
fill quantum, candidate evaluation count, maximum trade fraction, proof
requirement, fallback requirement, and ZenoEnergy permissions.

The release rule is:

```text
ZenoEnergyAllowed -> OrderOnly or OmissionHasDeterministicCertificate
```

Current profiles use order-only ZenoEnergy. The model may rank candidates, but
the deterministic verifier and policy checker decide whether a settlement is
accepted.

Run:

```bash
python3 tools/check_upba_policy_profiles.py --json
```
