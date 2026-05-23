# UPBA v2 Gemini Comparison

- Dataset: `data/upba_energy/upba_v2_energy_holdout_seed20260518.jsonl`
- Rows: `39979`
- Winner-bearing batches: `1983`
- Dataset sha256: `sha256:bcf06a210d591f5ab02e05a105db4af6c26d02782f91080e517cb3fb4d634cb7`

| Mode | Top-1 recall | Top-10 recall | Mean verifier calls | Pairwise accuracy |
| --- | ---: | ---: | ---: | ---: |
| `hand` | `0.762985` | `1.000000` | `1.361573` | `0.980899` |
| `gap_weighted` | `0.983359` | `1.000000` | `1.016641` | `0.998546` |
| `gemini` | `0.978820` | `1.000000` | `1.021684` | `0.998187` |

- Preferred measured checkpoint on this dataset: `gap_weighted`
- Gemini beats gap-weighted on mean calls: `False`
- Gemini beats gap-weighted on top-1 recall: `False`
- Gemini beats gap-weighted on pairwise accuracy: `False`
