# ZenoEnergy PopperPad

Date initialized: 2026-05-17

This append-only pad stores ZenoEnergy hypotheses, evidence, and negative
knowledge.

## Current Refs

### Set-Aware Linear Comparison

```text
domain_ref:                 sha256:491ffd61981b5fa5b0ca2e54afc3fea3b80bb75ac5d923176dae8063ddd9d82b
context_ref:                sha256:1ef45b750735a7c69c8c60de46065dca43e60935405692f903986615c658e8ed
report_artifact_ref:        sha256:0e7b79069af9d8b319fe877c8a7f0deb96db35a8dc2a56826872eec0cc6f78bd
negative_artifact_ref:      sha256:b56a3bdbcb41292230ee5bfc3fb52b1d569199a97b59e113cfd22a388137f897
safety_hypothesis_ref:      sha256:0bce1eec24d7cad22fdaeba989fac2c33d88bcc48cfa6bd2a931af2d57060b77
improvement_hypothesis_ref: sha256:08b6bfc25d399d08567099e49b8b8624f3e5737ca265d6ef761c1da2d4bbe6a7
checkpoint_ref:             sha256:552ced0c5ce4e38d8a2fd66b74f41da4edfe56c993db8a4fd36c1725fca890b6
```

### Neighborhood Repair Baseline

```text
context_ref:                sha256:8e4a85c00f00f65d1794f3acce81c90467496d1e7326b202f4f7937324d66106
report_artifact_ref:        sha256:729beed3a979fe8dd66689e6dd6f876bea6b54363c8ea4f602b1e524e5df7bc1
note_artifact_ref:          sha256:224f626747e30f2aadc85174020ce58d9a11e1d810281bc40032978c69b990c6
safety_hypothesis_ref:      sha256:98380edb22a5e4a45d683312409f89dea54c3a50e18a94fe373ca85fbe1367fc
regret_hypothesis_ref:      sha256:d84a675f6fd352db15f6156c37fa55926cad09c3853deb639c76171c9b22bc47
call_cost_hypothesis_ref:   sha256:c46675b22a8f09f0a3caa7cfadbcb3a9320e8654b6d31c3c64b6b0acdd066039
checkpoint_ref:             sha256:997899ef79e597d9058230d79d5ee2a847c026fa11bf0013a8673dc81100e2a9
```

### Learned Repair Selector

```text
context_ref:                sha256:423e05436ade42ffacfc2d8e6f5c80737b66389b5ba61e2441b2648dbd05f2ae
report_artifact_ref:        sha256:a333de8eb3f573a7270ba724406a847eea3366bc347b35d5759dfdebf8f59922
markdown_artifact_ref:      sha256:f43edf5accf668b559fb54c20d123fe57034e35660e5ebe4982a49b9777bf86e
model_artifact_ref:         sha256:9a51f33e40af1f1df3d75e784a2c6d5241258a23f955f5cb39b689fbddea10ea
safety_hypothesis_ref:      sha256:cc2d3f85bb83e5efb445fd0b2e20a0a01bef04e2dd6bd884e83eac40e879b352
compression_hypothesis_ref: sha256:c2e7e42762e2248f25abd6c1d353d07a0184fa4ea8a7c6178e41116404e7d1b1
hand_beat_hypothesis_ref:   sha256:047ebf186912ebee4ec402f805469432f86d81cdba76a2f793e828470678d3ad
checkpoint_ref:             sha256:e19e2f458b0e559f358f74b3502e5cd6b7e2d32cb3dd5eba5b1dcd9da02adec1
```

### Repair Selector Cross-Seed Stress

```text
context_ref:                sha256:61f2b6607f71f7c77318bc1750974004c5bb4c84f9b536fb5352f4c89c0627a7
report_artifact_ref:        sha256:204cca386fa6b48a0aa7d63ef5191bdcf91f0965ca0c50c11e59b8d59bb1df3b
markdown_artifact_ref:      sha256:050ac5d66e050bd5294e57cd4437f52452309c0f6dbf1d9111aafd08632b30b1
safety_hypothesis_ref:      sha256:11f4ac5be458dcf6b85404859746637e78dae1ff88b49efc8b1a5f950b48a603
compression_hypothesis_ref: sha256:c73f8cde1d40121a70156485602b0acd3eba6f62ba9f3c34d47f5e1e6fee549c
hand_beat_hypothesis_ref:   sha256:bc668d679f48705fdba26de502c2e4ac2ea59e806a8dd463d1b4b035e5c7fedf
checkpoint_ref:             sha256:f30e1571f5decf6c92f465aeee88fd5d3b89ddf257250904dd41b530239f0bb5
```

### Repair Selector Formal Boundary

```text
context_ref:                sha256:816d10e42113d2e25d54e8fbf831824e691aa6ce80f70d3f99db3af1eea13a45
receipt_artifact_ref:       sha256:84328e7d90dd6c0fe3f775b46ac898a7fad73ca4aebf1ee770f742076c2b91ee
receipt_hypothesis_ref:     sha256:3c61e2c848da522e7db1b45fbfe2f8803dfccf7cedb94d1461d7b243c576f47b
checkpoint_ref:             sha256:9e51d623aaa3572497be49f2d28fa61654444ea2bc9317d5eb86a9e62b241c4d
```

## Current Status

```text
H_ZENOENERGY_SET_AWARE_COMPARE_SAFETY_20260517: supported
H_ZENOENERGY_SET_AWARE_LINEAR_STRICTLY_IMPROVES_AGGREGATE_20260517: falsified
H_ZENOENERGY_NEIGHBORHOOD_SAFETY_SUBSET_20260517_V2: supported
H_ZENOENERGY_NEIGHBORHOOD_REDUCES_REGRET_20260517_V2: supported
H_ZENOENERGY_NEIGHBORHOOD_REDUCES_VERIFIER_CALLS_20260517_V2: falsified
H_ZENOENERGY_REPAIR_SELECTOR_SAFETY_20260517: supported
H_ZENOENERGY_REPAIR_SELECTOR_COMPRESSES_FULL_NEIGHBORHOOD_20260517: supported
H_ZENOENERGY_REPAIR_SELECTOR_STRICTLY_BEATS_HAND_SELECTED_20260517: falsified
H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_SAFETY_20260517: supported
H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_COMPRESSES_FULL_NEIGHBORHOOD_20260517: supported
H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_STRICTLY_BEATS_HAND_SELECTED_20260517: falsified
H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517: supported
doctor_ok: true
```

## Replay

```bash
PYTHONPATH=external/PopperPad/src python3 -m popperpad \
  --pad internal/popperpad/zenoenergy doctor
```
