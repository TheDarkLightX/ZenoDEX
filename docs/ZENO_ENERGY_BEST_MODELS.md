# ZenoEnergy Best Model Registry

schema: `zenodex/energy/best_model_registry/v1`
scope: `advisory_ranking_only`

These files are retained research checkpoints. They rank candidate checks only.
Deterministic UPBA verification and AutoTrader policy guards remain authoritative.

| model | domain | parameters | retained path | primary metric | sha256 |
| --- | --- | ---: | --- | --- | --- |
| gemini_mlp_v6_seed20260519 | upba_v2_partial_fill_exact_in | 6273 | `data/upba_energy/best_models/upba_v2_gemini_mlp_v6_seed20260519.json` | cross-seed mean calls 1.0036, top-1 min 0.9839, top-10 min 1.0000 | `sha256:859035159df61ecd7eab548e628b971840bdc96995b41547176e4a8cf205cb64` |
| gemini_highwinner_seed20260517 | upba_v2_partial_fill_exact_in | 97 | `data/upba_energy/best_models/upba_v2_gemini_highwinner_seed20260517.json` | cross-seed mean calls 1.0076, top-1 min 0.9839, top-10 min 1.0000 | `sha256:8bb29ba3129fccfa763bec4f0582a10ddde05eb8c58b854dd645f299e2e4ac90` |
| upba_v2_gap_weighted_default_seed20260517 | upba_v2_partial_fill_exact_in | 97 | `data/upba_energy/best_models/upba_v2_linear_gap_weighted_seed20260517.json` | cross-seed mean calls 1.0175, top-1 min 0.9677, top-10 min 1.0000 | `sha256:1a665e8fc07c1b24dd1ae0110f4509b73c0d975805f0a7ac807fc1f0de157c0a` |
| autotrader_hard_train20260522_holdout20260523 | autotrader_policy_guard_ordering | 21 | `data/upba_energy/best_models/autotrader_linear_hard_train20260522_holdout20260523.json` | guard calls 1.0130, top-5 1.0000 | `sha256:0dab25247a956fc47ab0fabf4619fbc5d9fa00c182b4e2ccaf37639feae4ac4b` |
| autotrader_hard_train20260524_holdout20260525 | autotrader_policy_guard_ordering | 21 | `data/upba_energy/best_models/autotrader_linear_hard_train20260524_holdout20260525.json` | guard calls 1.0100, top-5 1.0000 | `sha256:3d0b31b5c45a190a99774f37f79ddb07c8d36e8effe833eb892a4bd1bdff9c0c` |
| autotrader_hard_train20260526_holdout20260527 | autotrader_policy_guard_ordering | 21 | `data/upba_energy/best_models/autotrader_linear_hard_train20260526_holdout20260527.json` | guard calls 1.0080, top-5 1.0000 | `sha256:29a450c56c0dc1a6f50b49579cbdd3b3829ee71be68929cc4c3cce207e2ccec3` |

## Promoted Research Defaults

UPBA v2: `gemini_mlp_v6_seed20260519`

AutoTrader hard synthetic best seed pair: `autotrader_hard_train20260526_holdout20260527`

## Boundaries

- A retained model is an advisory search-order artifact with no consensus or policy authority.
- The AutoTrader retained models are still synthetic cross-seed artifacts until real shadow evidence promotes them.
- The UPBA retained model remains bounded synthetic research evidence until real replay and production-gate evidence pass.
