"""Local-testnet orchestration for `zenoctl testnet local ...`.

Brings up a real local stack (3-node ledger + Tau + Oracle + stdlib API + UI)
against live local backends — not demo surfaces. See the user-facing doc at
`docs/LOCAL_TESTNET_QUICKSTART.md` and the public schema
`zeno_ledger.local_testnet_manifest.v1`.

Public entry points live in `cli`; the rest of the package is private to
this orchestration family.
"""
