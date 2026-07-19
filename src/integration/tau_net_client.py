"""Non-production compatibility facade for legacy Tau test/tool imports.

Production code must import :mod:`src.integration.tau_net_rpc`.  This facade
retains the old local-testnet API while delegating all private-key and block
production behavior to :mod:`src.nonproduction.tau_net_signing`.  Production
image assembly removes both this facade and the non-production package.
"""

from __future__ import annotations

from src.integration.tau_net_rpc import (
    TauNetRpcError,
    TauNetTcpConfig,
    encode_tau_operations_for_wire,
    tau_rpc_invalid_sequence_numbers,
    tau_rpc_response_is_success,
    verify_tau_transaction_payload_signature,
)
from src.nonproduction.tau_net_signing import (
    NonProductionTauNetTcpClient as TauNetTcpClient,
)
from src.nonproduction.tau_net_signing import (
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    sign_dex_intent_for_engine,
    sign_perp_op_for_engine,
    sign_tau_transaction_payload,
)

__all__ = (
    "TauNetRpcError",
    "TauNetTcpClient",
    "TauNetTcpConfig",
    "bls_pubkey_hex_from_privkey",
    "build_signed_tau_transaction",
    "encode_tau_operations_for_wire",
    "sign_dex_intent_for_engine",
    "sign_perp_op_for_engine",
    "sign_tau_transaction_payload",
    "tau_rpc_invalid_sequence_numbers",
    "tau_rpc_response_is_success",
    "verify_tau_transaction_payload_signature",
)
