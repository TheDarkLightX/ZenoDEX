from __future__ import annotations

import pytest

from src.integration.perps_wallet_encrypted_sss_backup import recover_secret_shamir_gf256


@pytest.mark.parametrize("x", [False, True])
def test_recover_secret_shamir_rejects_bool_x_coordinate(x: bool) -> None:
    with pytest.raises(ValueError, match="share x coordinate must be in 1..255"):
        recover_secret_shamir_gf256([(x, b"\x01"), (2, b"\x02")])
