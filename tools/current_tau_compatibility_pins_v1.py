"""Exact source and vector pins for current-Tau compatibility replay V1."""

from __future__ import annotations

from typing import Final

SCHEMA_V1: Final = "zenodex/current-tau-compatibility/v1"
CHECK_SCHEMA_V1: Final = "zenodex/current-tau-compatibility-check/v1"

ACTIVE_PLAN_COMMIT_V1: Final = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
ACTIVE_PLAN_SHA256_V1: Final = "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f"
ACTIVE_REGISTRY_SHA256_V1: Final = "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4"
ADMISSION_RECEIPT_SHA256_V1: Final = "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d"
ADMISSION_RECEIPT_PAYLOAD_SHA256_V1: Final = (
    "fdc2d69fe530e0098d66f4a9d5d6297296cdf896b0fb97beb0f959ae054be86d"
)

CURRENT_TAU_COMMIT_V1: Final = "0b038824c8583a1a902ef54369d3d0ecf3384cf5"
CURRENT_TAU_TREE_V1: Final = "445d77a77b451a0babe5b25c2d66bc45ee20ef29"
CURRENT_TAU_TREE_LISTING_SHA256_V1: Final = (
    "635b6ecd1d7bc82f7147ff7015fa751e4505369494c450e20d533d2327bd11db"
)
CURRENT_TAU_SOURCE_SHA256_V1: Final = (
    ("README.md", "5897a1b965096bbb606e0030da84f6beca050518e99428865c95a09f4d34414c"),
    ("api_response.py", "1dad7240f3116e6d309856753ff8e4bcce327772c87206d8e2b0c48bc5912b4a"),
    ("app/container.py", "3a368099b28a23dbac76bee4f4149b1d72b67708d9c9b78dbb725dafff9d708a"),
    (
        "commands/createblock.py",
        "89cf6abd9cd5661f2a7d266d54362f52c5a29432a3c12601f7e389715fb547a7",
    ),
    (
        "commands/gettxstatus.py",
        "f293977bc334540228cf7f27f9af49902a96436beee58e97661086ba501ae844",
    ),
    ("commands/sendtx.py", "82a4805e039fa644b099928dc19a600cc1f9d8753580c7b3a6d2a3a09c7248cf"),
    (
        "consensus/admission.py",
        "cf2e11165a17de3191f73739afaa725693b6ff2fb4df8e36c6e3de2cb486516b",
    ),
    ("server.py", "22cb9ed07749d08bc1b275ad5518c9545eef7da0ce61696741227c00abb22bfb"),
    ("tau_defs.py", "853d55e054116a13af7854b81789da1dbcbfc27a6a60cd78308dd54cc7b7e5ad"),
    ("tau_manager.py", "8c1ad43fd98d1fc3545a4f4ff3d486d736049100b559454479ca04ccb6f8757f"),
)

CURRENT_TAU_LANG_COMMIT_V1: Final = "1195b4a629250d284ac33789021263dd0395cfb3"
CURRENT_TAU_LANG_TREE_V1: Final = "3d2ee089856c98d29bea3da1c9152dba298485d3"
CURRENT_TAU_LANG_TREE_LISTING_SHA256_V1: Final = (
    "deafd7edb60441b74e2e9d711b3c9f7a03f8d77205ac856969d02e14d0bcc120"
)
CURRENT_TAU_LANG_SOURCE_SHA256_V1: Final = (
    ("README.md", "cd6d6377d49b01bfb1a7bec458bb20f1d943431007edbf902dbf64ef8f9d7137"),
    ("src/main.cpp", "f9a9bc2ba7b3d12dab00d2161c6577579a57102a93ea692a63926316029c84dc"),
)

HISTORICAL_BRIDGE_COMMIT_V1: Final = "f7471ea421d32223b7e48bfecec94b639de9986a"
HISTORICAL_BRIDGE_TREE_V1: Final = "da744b8ea91e7997ac78f0026d561b57a932fb64"
HISTORICAL_BRIDGE_TREE_LISTING_SHA256_V1: Final = (
    "fc33e769e45a24827b6ddc4cc09b7a03c50c42a0ca4dff19778710ec836036a8"
)
HISTORICAL_BRIDGE_SOURCE_SHA256_V1: Final = (
    ("app/container.py", "7d6440f3da7e955e36becb690b8eb58e620c38c727a68a0f7e77aa8c07f03c1c"),
    (
        "commands/createblock.py",
        "84a2bb06c32cf7940539b22ab2d1ded6ddfb8dea94eef5c9111ff8f271c04a9e",
    ),
    (
        "commands/getappstate.py",
        "b667ca063588db4ec081ddee6e8e7fcd89bef95abd6c2675585771a84b58fb60",
    ),
    ("commands/sendtx.py", "d8b5cc6be865abed58d133e8aed2ce76e19127e90897e8b5b1242b36dd3fbe97"),
    ("tau_defs.py", "bbbc90bdc0e4ecfb772502c8a7d1ef1828bf1946dbe3b8288aa90f5b3f49a6f5"),
    ("tau_manager.py", "18975f2bbe957eb5b08a3c7cf6effda6adc1a9551824837471577133b2e56431"),
)

LOCAL_PROFILE_SOURCE_SHA256_V1: Final = (
    (
        "docker-compose.local-testnet.yml",
        "6d0e8aa402645d1fcf043fde286e16b1642c2ee6fb99c608f119de40b1b5bc8c",
    ),
    (
        "src/integration/tau_net_client.py",
        "f466df2b9e12ed548c1434a4115ad240428f7cee5741292675125f11e6ae744a",
    ),
    (
        "src/integration/tau_testnet_dex_plugin.py",
        "53e6ded17869eebcccb53f848f5dc043419d53a6ff5b86e3f90abd6d6440023e",
    ),
    (
        "tools/run_local_tau_node_container.sh",
        "a3c841e37e71257bc305eb30993c0bfab4dac5e8e31f280f94ae124176b4afe1",
    ),
    (
        "tools/tau_testnet_local_e2e.py",
        "b6a297ac3606461c0e681cbc24783485cf1032b24bed6807c4a32495b2d73e19",
    ),
)

IMPLEMENTATION_EVIDENCE_PATHS_V1: Final = (
    "tools/__init__.py",
    "tools/current_tau_compatibility_pins_v1.py",
    "tools/current_tau_compatibility_core_v1.py",
    "tools/current_tau_replay_io_v1.py",
    "tests/test_check_current_tau_compatibility_v1.py",
    "tools/build_current_tau_compatibility_v1.py",
    "tools/check_current_tau_compatibility_v1.py",
    "tools/current_tau_source_analysis_v1.py",
)
IMPLEMENTATION_SOURCE_PATHS_V1: Final = tuple(
    path for path, _digest in LOCAL_PROFILE_SOURCE_SHA256_V1
) + IMPLEMENTATION_EVIDENCE_PATHS_V1

EXPECTED_CURRENT_RESERVED_STREAMS_V1: Final = tuple(range(12))
EXPECTED_LEGACY_OPERATION_STREAMS_V1: Final = tuple(range(5, 12))
EXPECTED_CURRENT_USER_TX_SIGNING_FIELDS_V1: Final = (
    "expiration_time",
    "fee_limit",
    "operations",
    "sender_pubkey",
    "sequence_number",
    "tx_type",
)
EXPECTED_LEGACY_USER_TX_SIGNING_FIELDS_V1: Final = (
    "expiration_time",
    "fee_limit",
    "operations",
    "sender_pubkey",
    "sequence_number",
)
EXPECTED_REMOVED_RPC_NAMES_V1: Final = ("apply_app_tx", "getappstate", "getstateproof")
EXPECTED_CURRENT_SIGNING_SHA256_V1: Final = (
    "ef3a6a1e6daffe8ac34e4a3fc23f7fbb5f1ea617c4b4c3b56911ed46ff60a570"
)
EXPECTED_LEGACY_SIGNING_SHA256_V1: Final = (
    "cb9f87ba6c819de2fdced3da8d7a0be55cd2943eca1d47bc8591adb903aebfe9"
)
EXPECTED_CURRENT_SUCCESS_ENVELOPE_SHA256_V1: Final = (
    "057f730b76c46013e4692468e7d72ee678a62720844a39bd73474d629c6f6834"
)
