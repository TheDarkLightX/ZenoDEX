FIRE kernel lane.

Current status:
- settlement apply / packet / persisted-bundle execution lives in `src/fire/kernel`
- `kernel_receipt_v1.py` emits non-authoritative kernel-origin package
  evidence for the admitted ref-model lane
- `kernel_eval_receipt_v1.py` emits non-authoritative concrete kernel-eval
  package evidence for the admitted compile/eval lane
- `kernel_replay_receipt_v1.py` emits non-authoritative concrete
  kernel-replay package evidence for the admitted replay-transcript lane
- `kernel_settlement_receipt_v1.py` emits non-authoritative concrete
  kernel-settlement package evidence for the admitted replay/settlement lane
- admitted generated FIRE reference kernels now live in:
  - `fire_burn_boost_call_v1_ref.py`
  - `fire_fee_note_v1_ref.py`
  - `fire_lp_loss_cover_v1_ref.py`
- legacy `src/kernels/python/fire_*_ref.py` modules are compatibility shims back to this lane

Target role:
- canonical integer payoff evaluation
- canonical delta emission
- small admitted execution subset for live families

Current concrete module:
- `src/fire/kernel/kernel_receipt_v1.py`
- `src/fire/kernel/kernel_eval_receipt_v1.py`
- `src/fire/kernel/kernel_replay_receipt_v1.py`
- `src/fire/kernel/kernel_settlement_receipt_v1.py`
- `src/fire/kernel/settlement_v1.py`
- `src/fire/kernel/apply_receipt_v1.py`
- `src/fire/kernel/ledger_adapter_v1.py`
- `src/fire/kernel/persisted_bundle_settlement_v1.py`
- `src/fire/kernel/fire_burn_boost_call_v1_ref.py`
- `src/fire/kernel/fire_fee_note_v1_ref.py`
- `src/fire/kernel/fire_lp_loss_cover_v1_ref.py`

`kernel_receipt.json`, `kernel_eval_receipt.json`, `kernel_replay_receipt.json`,
and `kernel_settlement_receipt.json` remain package evidence only. They help
the proof-tree `IntegerEvalOK` and `ReplayOK` lanes bind to the admitted
ref-model surface plus concrete admitted kernel execution/replay/settlement
surfaces, but they do not authorize settlement.
