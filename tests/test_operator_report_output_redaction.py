import json

import pytest

from tools.operator_report_output import operator_json_dumps, public_storage_json_dumps


@pytest.mark.parametrize(
    "key",
    [
        "client_secret",
        "signing_secret",
        "secret_hex",
        "Authorization",
        "local_signing_material_hex",
    ],
)
def test_operator_json_redacts_common_secret_keys(key: str) -> None:
    payload = {key: "top-secret"}

    parsed = json.loads(operator_json_dumps(payload, indent=None))

    assert list(parsed.values()) == ["[redacted]"]


@pytest.mark.parametrize("value", [123456789, 987654.0])
def test_operator_json_redacts_numeric_secret_values(value: int | float) -> None:
    payload = {"api_key": value}

    parsed = json.loads(operator_json_dumps(payload, indent=None))

    assert list(parsed.values()) == ["[redacted]"]


@pytest.mark.parametrize(
    "key",
    [
        "client_secret",
        "signing_secret",
        "secret_hex",
        "authorization",
        "local_signing_material_hex",
    ],
)
def test_public_storage_rejects_common_secret_keys(key: str) -> None:
    with pytest.raises(ValueError, match="inline credential material"):
        public_storage_json_dumps({key: "top-secret"}, indent=None)
