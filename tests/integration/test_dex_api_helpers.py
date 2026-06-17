"""BVA coverage for the shared DEX API HTTP helpers.

These helpers replace ad-hoc validation patterns that were duplicated 84 times
inside `src/integration/api_server.py::_Handler._maybe_handle_dex_api`. The
boundary-value tests are the contract: every numeric guard, every JSON-shape
guard, and every error-response shape is pinned here so the dispatch-seam
refactor can byte-compare per-endpoint responses against captured golden
fixtures with confidence that the helpers themselves are exercised.
"""

from __future__ import annotations

import json

import pytest

from src.integration._dex_api_helpers import (
    BadFieldError,
    EndpointSchema,
    IntFieldSpec,
    error_response,
    exact_out_split_quote_from_dict,
    int_field,
    optional_int_list_field,
    parse_int_kwargs,
    parse_json_body_or_400,
    parse_pools,
    projected_path_from_exact_out_quote_payload,
    quote_to_dict,
)


class TestIntFieldBVA:
    """Boundary-value analysis for the `int_field` helper.

    The helper must:
      - Reject `bool` even though `isinstance(True, int)` is True in Python.
      - Accept the exact `minimum` and `maximum` bounds (inclusive).
      - Reject `minimum - 1` and `maximum + 1`.
      - Return the `default` when the key is absent.
      - Raise `BadFieldError` (subclass of `ValueError`) on all rejections.
    """

    def test_accepts_minimum_boundary(self) -> None:
        assert int_field({"n": 0}, "n", minimum=0, maximum=10) == 0

    def test_accepts_minimum_plus_one(self) -> None:
        assert int_field({"n": 1}, "n", minimum=0, maximum=10) == 1

    def test_rejects_minimum_minus_one(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            int_field({"n": -1}, "n", minimum=0, maximum=10)
        assert exc_info.value.field == "n"

    def test_accepts_maximum_boundary(self) -> None:
        assert int_field({"n": 10}, "n", minimum=0, maximum=10) == 10

    def test_accepts_maximum_minus_one(self) -> None:
        assert int_field({"n": 9}, "n", minimum=0, maximum=10) == 9

    def test_rejects_maximum_plus_one(self) -> None:
        with pytest.raises(BadFieldError):
            int_field({"n": 11}, "n", minimum=0, maximum=10)

    def test_rejects_bool_true_even_though_python_treats_it_as_int(self) -> None:
        with pytest.raises(BadFieldError):
            int_field({"n": True}, "n", minimum=0, maximum=10)

    def test_rejects_bool_false(self) -> None:
        with pytest.raises(BadFieldError):
            int_field({"n": False}, "n", minimum=0, maximum=10)

    def test_rejects_non_int_string(self) -> None:
        with pytest.raises(BadFieldError):
            int_field({"n": "42"}, "n", minimum=0, maximum=10)

    def test_rejects_float(self) -> None:
        with pytest.raises(BadFieldError):
            int_field({"n": 3.0}, "n", minimum=0, maximum=10)

    def test_returns_default_when_key_absent(self) -> None:
        assert int_field({}, "n", default=7, minimum=0, maximum=10) == 7

    def test_raises_when_key_absent_and_no_default(self) -> None:
        with pytest.raises(BadFieldError):
            int_field({}, "n", minimum=0, maximum=10)

    def test_accepts_negative_when_minimum_negative(self) -> None:
        assert int_field({"n": -50}, "n", minimum=-100, maximum=0) == -50

    def test_only_minimum_constraint(self) -> None:
        # No maximum given — only lower bound checked
        assert int_field({"n": 10**18}, "n", minimum=0) == 10**18

    def test_only_maximum_constraint(self) -> None:
        assert int_field({"n": -(10**18)}, "n", maximum=0) == -(10**18)

    def test_no_constraints_accepts_any_int(self) -> None:
        assert int_field({"n": 42}, "n") == 42

    def test_error_carries_field_name_and_reason(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            int_field({"n": "oops"}, "n", minimum=0, maximum=10)
        assert exc_info.value.field == "n"
        assert "int" in exc_info.value.reason.lower() or "type" in exc_info.value.reason.lower()

    # Mutmut-driven: the exact error message text is part of the contract.
    # If a caller logs or matches on the reason string, mutations to the
    # message must be detectable.
    def test_required_field_error_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            int_field({}, "amount")
        assert exc_info.value.field == "amount"
        assert exc_info.value.reason == "field is required"

    def test_type_error_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            int_field({"n": "x"}, "n")
        assert exc_info.value.field == "n"
        assert exc_info.value.reason == "must be an int (bool rejected)"

    def test_minimum_violation_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            int_field({"n": -1}, "n", minimum=0)
        assert exc_info.value.field == "n"
        assert exc_info.value.reason == "must be >= 0"

    def test_maximum_violation_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            int_field({"n": 11}, "n", maximum=10)
        assert exc_info.value.field == "n"
        assert exc_info.value.reason == "must be <= 10"


class TestOptionalIntListField:
    """The slippage_options pattern: optional list of bounded positive ints."""

    def test_returns_none_when_absent(self) -> None:
        assert optional_int_list_field({}, "options") is None

    def test_returns_none_when_explicit_null(self) -> None:
        assert optional_int_list_field({"options": None}, "options") is None

    def test_accepts_empty_list(self) -> None:
        assert optional_int_list_field({"options": []}, "options") == []

    def test_accepts_valid_list(self) -> None:
        assert optional_int_list_field({"options": [1, 2, 3]}, "options", item_minimum=1) == [1, 2, 3]

    def test_rejects_non_list(self) -> None:
        with pytest.raises(BadFieldError):
            optional_int_list_field({"options": "not_a_list"}, "options")

    def test_rejects_item_below_minimum(self) -> None:
        with pytest.raises(BadFieldError):
            optional_int_list_field({"options": [0]}, "options", item_minimum=1)

    def test_rejects_bool_item(self) -> None:
        with pytest.raises(BadFieldError):
            optional_int_list_field({"options": [True]}, "options")

    def test_rejects_non_int_item(self) -> None:
        with pytest.raises(BadFieldError):
            optional_int_list_field({"options": ["1"]}, "options")

    def test_enforces_max_length(self) -> None:
        with pytest.raises(BadFieldError):
            optional_int_list_field({"options": [1, 2, 3, 4]}, "options", max_length=3)

    # Mutmut-driven: cover the exact boundary so `> max_length` vs
    # `>= max_length` mutation gets killed.
    def test_max_length_exact_boundary_accepted(self) -> None:
        assert optional_int_list_field({"options": [1, 2, 3]}, "options", max_length=3) == [1, 2, 3]

    # Mutmut-driven: item_maximum has zero coverage. Add full BVA.
    def test_accepts_item_at_maximum_boundary(self) -> None:
        assert optional_int_list_field({"options": [10]}, "options", item_maximum=10) == [10]

    def test_rejects_item_above_maximum_boundary(self) -> None:
        with pytest.raises(BadFieldError):
            optional_int_list_field({"options": [11]}, "options", item_maximum=10)

    def test_item_maximum_boundary_off_by_one(self) -> None:
        assert optional_int_list_field({"options": [9]}, "options", item_maximum=10) == [9]

    # Mutmut-driven: pin the exact error messages.
    def test_non_list_error_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            optional_int_list_field({"options": "x"}, "options")
        assert exc_info.value.field == "options"
        assert exc_info.value.reason == "must be a list of ints"

    def test_max_length_error_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            optional_int_list_field({"options": [1, 2, 3, 4]}, "options", max_length=3)
        assert exc_info.value.field == "options"
        assert exc_info.value.reason == "must have at most 3 items"

    def test_item_type_error_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            optional_int_list_field({"options": ["x"]}, "options")
        assert exc_info.value.field == "options"
        assert exc_info.value.reason == "item 0 must be an int (bool rejected)"

    def test_item_minimum_error_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            optional_int_list_field({"options": [-1]}, "options", item_minimum=0)
        assert exc_info.value.field == "options"
        assert exc_info.value.reason == "item 0 must be >= 0"

    def test_item_maximum_error_uses_canonical_message(self) -> None:
        with pytest.raises(BadFieldError) as exc_info:
            optional_int_list_field({"options": [11]}, "options", item_maximum=10)
        assert exc_info.value.field == "options"
        assert exc_info.value.reason == "item 0 must be <= 10"


class TestParseJsonBodyOr400:
    """Body parsing must accept only JSON objects; everything else is 400."""

    def test_accepts_valid_object(self) -> None:
        obj, err = parse_json_body_or_400(b'{"a": 1}')
        assert obj == {"a": 1}
        assert err is None

    def test_rejects_missing_body(self) -> None:
        obj, err = parse_json_body_or_400(None)
        assert obj is None
        assert err is not None
        status, body = err
        assert status == 400
        assert body["error"] == "missing_body"

    def test_rejects_empty_bytes(self) -> None:
        obj, err = parse_json_body_or_400(b"")
        assert obj is None
        assert err is not None
        status, body = err
        assert status == 400
        assert body["error"] == "bad_json"

    def test_rejects_malformed_json(self) -> None:
        obj, err = parse_json_body_or_400(b'{"a":')
        assert obj is None
        assert err is not None
        assert err[1]["error"] == "bad_json"

    def test_rejects_json_array(self) -> None:
        obj, err = parse_json_body_or_400(b"[1, 2, 3]")
        assert obj is None
        assert err is not None
        assert err[1]["error"] == "bad_body"

    def test_rejects_json_null(self) -> None:
        obj, err = parse_json_body_or_400(b"null")
        assert obj is None
        assert err is not None
        assert err[1]["error"] == "bad_body"

    def test_rejects_json_string(self) -> None:
        obj, err = parse_json_body_or_400(b'"hello"')
        assert obj is None
        assert err is not None
        assert err[1]["error"] == "bad_body"

    def test_accepts_empty_object(self) -> None:
        obj, err = parse_json_body_or_400(b"{}")
        assert obj == {}
        assert err is None

    def test_rejects_non_utf8(self) -> None:
        obj, err = parse_json_body_or_400(b'\xff\xfe{"a": 1}')
        assert obj is None
        assert err is not None
        assert err[1]["error"] == "bad_json"

    # Mutmut-driven: pin the status code on every error branch so mutations
    # like 400 → 401 or 400 → None get killed.
    def test_missing_body_returns_status_400(self) -> None:
        _, err = parse_json_body_or_400(None)
        assert err is not None and err[0] == 400

    def test_bad_json_returns_status_400(self) -> None:
        _, err = parse_json_body_or_400(b"{")
        assert err is not None and err[0] == 400

    def test_bad_body_returns_status_400(self) -> None:
        _, err = parse_json_body_or_400(b"[1]")
        assert err is not None and err[0] == 400


class TestErrorResponse:
    """Error response shape is byte-pinned: status int, body with ok=False."""

    def test_basic_shape(self) -> None:
        status, body = error_response(400, "bad_thing")
        assert status == 400
        assert body == {"ok": False, "error": "bad_thing"}

    def test_with_details(self) -> None:
        status, body = error_response(400, "bad_thing", details="more info", field="x")
        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "bad_thing"
        assert body["details"] == "more info"
        assert body["field"] == "x"

    def test_status_can_be_anything_callable_passes(self) -> None:
        # Helper does not constrain status code values; callers choose.
        status, body = error_response(500, "internal")
        assert status == 500

    def test_body_is_json_serializable(self) -> None:
        _, body = error_response(400, "bad", value=42, nested={"k": "v"})
        json.dumps(body)  # must not raise


class TestBadFieldError:
    """BadFieldError must subclass ValueError so existing except chains catch it."""

    def test_is_value_error(self) -> None:
        assert issubclass(BadFieldError, ValueError)

    def test_carries_field_and_reason(self) -> None:
        err = BadFieldError("amount_in", "must be a positive int")
        assert err.field == "amount_in"
        assert err.reason == "must be a positive int"
        assert "amount_in" in str(err)


class TestParsePools:
    """parse_pools(obj) -> {pool_id: PoolState}; rejects malformed inputs."""

    def _pool_row(
        self,
        *,
        pid: str = "pool_a",
        a0: str = "asset0",
        a1: str = "asset1",
        r0: int = 100,
        r1: int = 100,
        fee: int = 30,
        status: str = "ACTIVE",
        curve: str = "CPMM",
    ) -> dict:
        return {
            "pool_id": pid,
            "asset0": a0,
            "asset1": a1,
            "reserve0": r0,
            "reserve1": r1,
            "fee_bps": fee,
            "lp_supply": 1,
            "status": status,
            "created_at": 0,
            "curve_tag": curve,
            "curve_params": "",
        }

    def test_accepts_single_pool(self) -> None:
        result = parse_pools({"pools": [self._pool_row()]})
        assert "pool_a" in result
        assert result["pool_a"].reserve0 == 100

    def test_accepts_multiple_pools(self) -> None:
        result = parse_pools({"pools": [self._pool_row(pid="p1"), self._pool_row(pid="p2")]})
        assert set(result.keys()) == {"p1", "p2"}

    def test_rejects_missing_pools_key(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^pools must be a non-empty list$"):
            parse_pools({})

    def test_rejects_empty_list(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^pools must be a non-empty list$"):
            parse_pools({"pools": []})

    def test_rejects_non_list(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^pools must be a non-empty list$"):
            parse_pools({"pools": "not_a_list"})

    def test_rejects_non_dict_row(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^pool must be an object$"):
            parse_pools({"pools": ["not_a_dict"]})

    def test_rejects_missing_pool_id(self) -> None:
        import pytest

        row = self._pool_row()
        del row["pool_id"]
        with pytest.raises(ValueError, match=r"^pool_id must be a non-empty string$"):
            parse_pools({"pools": [row]})

    def test_rejects_empty_pool_id(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^pool_id must be a non-empty string$"):
            parse_pools({"pools": [self._pool_row(pid="")]})

    def test_rejects_non_string_pool_id(self) -> None:
        import pytest

        row = self._pool_row()
        row["pool_id"] = 42
        with pytest.raises(ValueError, match=r"^pool_id must be a non-empty string$"):
            parse_pools({"pools": [row]})

    def test_rejects_duplicate_pool_id(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^duplicate pool_id: dup$"):
            parse_pools({"pools": [self._pool_row(pid="dup"), self._pool_row(pid="dup")]})

    def test_rejects_bad_status(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad pool status: NOT_A_STATUS$"):
            parse_pools({"pools": [self._pool_row(status="not_a_status")]})

    @pytest.mark.parametrize(
        "field",
        ("reserve0", "reserve1", "fee_bps", "lp_supply", "created_at"),
    )
    def test_rejects_bool_numeric_pool_fields(self, field: str) -> None:
        row = self._pool_row()
        row[field] = True

        with pytest.raises(BadFieldError) as exc_info:
            parse_pools({"pools": [row]})

        assert exc_info.value.field == field
        assert exc_info.value.reason == "must be an int (bool rejected)"

    @pytest.mark.parametrize(
        "field",
        ("reserve0", "reserve1", "fee_bps", "lp_supply", "created_at"),
    )
    def test_rejects_numeric_string_pool_fields(self, field: str) -> None:
        row = self._pool_row()
        row[field] = "1"

        with pytest.raises(BadFieldError) as exc_info:
            parse_pools({"pools": [row]})

        assert exc_info.value.field == field
        assert exc_info.value.reason == "must be an int (bool rejected)"

    def test_default_status_is_active(self) -> None:
        row = self._pool_row()
        del row["status"]
        result = parse_pools({"pools": [row]})
        from src.state.pools import PoolStatus

        assert result["pool_a"].status == PoolStatus.ACTIVE

    # Mutmut-driven: assert every PoolState field is populated from the
    # right source so field-substitution mutations (e.g. pool_id=None,
    # asset0=str(row.get("asset0", None))) get killed. We use asset names
    # that satisfy PoolState's canonical-order invariant (asset0 < asset1)
    # and curve_tag="CPMM" which is the only validated tag without extra
    # curve_params requirements.
    def test_pool_fields_round_trip_exactly(self) -> None:
        row = self._pool_row(
            pid="precise_id",
            a0="aaa_left",
            a1="bbb_right",
            r0=12345,
            r1=67890,
            fee=42,
            curve="CPMM",
        )
        row["lp_supply"] = 999
        row["created_at"] = 777
        row["curve_params"] = ""
        result = parse_pools({"pools": [row]})
        pool = result["precise_id"]
        assert pool.pool_id == "precise_id"
        assert pool.asset0 == "aaa_left"
        assert pool.asset1 == "bbb_right"
        assert pool.reserve0 == 12345
        assert pool.reserve1 == 67890
        assert pool.fee_bps == 42
        assert pool.lp_supply == 999
        assert pool.created_at == 777
        assert pool.curve_tag == "CPMM"
        assert pool.curve_params == ""


class TestQuoteToDict:
    """quote_to_dict converts a RouteQuote into a JSON-friendly dict."""

    def test_returns_empty_dict_for_non_route_quote(self) -> None:
        assert quote_to_dict(None) == {}
        assert quote_to_dict("not a quote") == {}
        assert quote_to_dict(42) == {}

    def test_returns_legacy_shape_for_route_quote(self) -> None:
        from src.core.routing import RouteHop, RouteLeg, RouteQuote

        hop = RouteHop(pool_id="pool_a", asset_in="A", asset_out="B", amount_in=100, amount_out=99)
        leg = RouteLeg(amount_in=100, amount_out=99, hops=(hop,))
        quote = RouteQuote(asset_in="A", asset_out="B", amount_in=100, amount_out=99, legs=(leg,))
        result = quote_to_dict(quote)
        assert result["asset_in"] == "A"
        assert result["asset_out"] == "B"
        assert result["amount_in"] == 100
        assert result["amount_out"] == 99
        assert len(result["legs"]) == 1
        assert result["legs"][0]["amount_in"] == 100
        assert result["legs"][0]["hops"][0]["pool_id"] == "pool_a"


class TestExactOutSplitQuoteFromDict:
    """exact_out_split_quote_from_dict parses a split quote payload."""

    def _good_payload(self) -> dict:
        return {
            "amount_out_total": 100,
            "amount_in_total": 110,
            "legs": [{"pool_id": "p1", "amount_out": 100, "amount_in": 110}],
        }

    def test_accepts_well_formed_payload(self) -> None:
        result = exact_out_split_quote_from_dict(self._good_payload())
        assert result.amount_out_total == 100
        assert result.amount_in_total == 110
        assert len(result.legs) == 1

    def test_rejects_non_dict(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote$"):
            exact_out_split_quote_from_dict("not a dict")

    def test_rejects_missing_amount_out_total(self) -> None:
        import pytest

        payload = self._good_payload()
        del payload["amount_out_total"]
        with pytest.raises(ValueError, match=r"^bad_amount_out_total$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_zero_amount_out_total(self) -> None:
        import pytest

        payload = self._good_payload()
        payload["amount_out_total"] = 0
        with pytest.raises(ValueError, match=r"^bad_amount_out_total$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_bool_amount_out_total(self) -> None:
        import pytest

        payload = self._good_payload()
        payload["amount_out_total"] = True
        with pytest.raises(ValueError, match=r"^bad_amount_out_total$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_missing_amount_in_total(self) -> None:
        import pytest

        payload = self._good_payload()
        del payload["amount_in_total"]
        with pytest.raises(ValueError, match=r"^bad_amount_in_total$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_empty_legs(self) -> None:
        import pytest

        payload = self._good_payload()
        payload["legs"] = []
        with pytest.raises(ValueError, match=r"^bad_exact_out_legs$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_missing_legs(self) -> None:
        import pytest

        payload = self._good_payload()
        del payload["legs"]
        with pytest.raises(ValueError, match=r"^bad_exact_out_legs$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_non_dict_leg(self) -> None:
        import pytest

        payload = self._good_payload()
        payload["legs"] = ["not_a_dict"]
        with pytest.raises(ValueError, match=r"^bad_exact_out_leg$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_leg_missing_pool_id(self) -> None:
        import pytest

        payload = self._good_payload()
        del payload["legs"][0]["pool_id"]
        with pytest.raises(ValueError, match=r"^bad_exact_out_leg_pool_id$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_leg_zero_amount_out(self) -> None:
        import pytest

        payload = self._good_payload()
        payload["legs"][0]["amount_out"] = 0
        with pytest.raises(ValueError, match=r"^bad_exact_out_leg_amount_out$"):
            exact_out_split_quote_from_dict(payload)

    def test_rejects_leg_zero_amount_in(self) -> None:
        import pytest

        payload = self._good_payload()
        payload["legs"][0]["amount_in"] = 0
        with pytest.raises(ValueError, match=r"^bad_exact_out_leg_amount_in$"):
            exact_out_split_quote_from_dict(payload)


class TestProjectedPathFromExactOutQuotePayload:
    """projected_path_from_exact_out_quote_payload extracts [[pool_id, amount_out, amount_in], ...]."""

    def test_returns_none_for_none(self) -> None:
        assert projected_path_from_exact_out_quote_payload(None) is None

    def test_extracts_projected_path(self) -> None:
        payload = {
            "legs": [
                {"pool_id": "p1", "amount_out": 100, "amount_in": 110},
                {"pool_id": "p2", "amount_out": 50, "amount_in": 60},
            ]
        }
        result = projected_path_from_exact_out_quote_payload(payload)
        assert result == [["p1", 100, 110], ["p2", 50, 60]]

    def test_accepts_empty_legs_list(self) -> None:
        result = projected_path_from_exact_out_quote_payload({"legs": []})
        assert result == []

    def test_rejects_non_dict_payload(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote_payload$"):
            projected_path_from_exact_out_quote_payload("not a dict")

    def test_rejects_missing_legs(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote_legs$"):
            projected_path_from_exact_out_quote_payload({"foo": "bar"})

    def test_rejects_non_list_legs(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote_legs$"):
            projected_path_from_exact_out_quote_payload({"legs": "not_a_list"})

    def test_rejects_non_dict_leg(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote_leg$"):
            projected_path_from_exact_out_quote_payload({"legs": ["not_a_dict"]})

    def test_rejects_leg_missing_pool_id(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote_leg_pool_id$"):
            projected_path_from_exact_out_quote_payload(
                {"legs": [{"amount_out": 100, "amount_in": 110}]}
            )

    def test_rejects_leg_empty_pool_id(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote_leg_pool_id$"):
            projected_path_from_exact_out_quote_payload(
                {"legs": [{"pool_id": "", "amount_out": 100, "amount_in": 110}]}
            )

    def test_rejects_leg_bool_amount_out(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote_leg_amount_out$"):
            projected_path_from_exact_out_quote_payload(
                {"legs": [{"pool_id": "p", "amount_out": True, "amount_in": 110}]}
            )

    def test_rejects_leg_bool_amount_in(self) -> None:
        import pytest

        with pytest.raises(ValueError, match=r"^bad_exact_out_quote_leg_amount_in$"):
            projected_path_from_exact_out_quote_payload(
                {"legs": [{"pool_id": "p", "amount_out": 100, "amount_in": True}]}
            )


class TestIntFieldSpec:
    """Declarative spec for a single int field. Used by parse_int_kwargs +
    OpenAPI generation."""

    def test_required_when_no_default(self) -> None:
        spec = IntFieldSpec(name="n")
        assert spec.required is True
        assert spec.default is None

    def test_optional_when_default_set(self) -> None:
        spec = IntFieldSpec(name="n", default=42)
        assert spec.required is False
        assert spec.default == 42

    def test_json_schema_minimal(self) -> None:
        spec = IntFieldSpec(name="n")
        assert spec.to_json_schema() == {"type": "integer"}

    def test_json_schema_with_bounds(self) -> None:
        spec = IntFieldSpec(name="n", minimum=0, maximum=100)
        assert spec.to_json_schema() == {
            "type": "integer",
            "minimum": 0,
            "maximum": 100,
        }

    def test_json_schema_with_default_and_description(self) -> None:
        spec = IntFieldSpec(name="n", default=7, description="the quick brown fox")
        schema = spec.to_json_schema()
        assert schema["default"] == 7
        assert schema["description"] == "the quick brown fox"

    def test_is_frozen(self) -> None:
        import dataclasses

        spec = IntFieldSpec(name="n")
        with pytest.raises(dataclasses.FrozenInstanceError):
            spec.name = "other"  # type: ignore[misc]


class TestParseIntKwargs:
    """Validates a dict against a sequence of IntFieldSpec, returning
    a dict[str, int] suitable for **kwargs splat. Raises BadFieldError
    on the first invalid field."""

    def test_all_required_present(self) -> None:
        specs = [IntFieldSpec(name="a"), IntFieldSpec(name="b")]
        result = parse_int_kwargs({"a": 1, "b": 2}, specs)
        assert result == {"a": 1, "b": 2}

    def test_default_used_when_key_absent(self) -> None:
        specs = [IntFieldSpec(name="a", default=7)]
        result = parse_int_kwargs({}, specs)
        assert result == {"a": 7}

    def test_explicit_value_overrides_default(self) -> None:
        specs = [IntFieldSpec(name="a", default=7)]
        result = parse_int_kwargs({"a": 9}, specs)
        assert result == {"a": 9}

    def test_required_missing_raises(self) -> None:
        specs = [IntFieldSpec(name="a")]
        with pytest.raises(BadFieldError) as exc_info:
            parse_int_kwargs({}, specs)
        assert exc_info.value.field == "a"
        assert exc_info.value.reason == "field is required"

    def test_bool_rejected(self) -> None:
        specs = [IntFieldSpec(name="a")]
        with pytest.raises(BadFieldError) as exc_info:
            parse_int_kwargs({"a": True}, specs)
        assert exc_info.value.reason == "must be an int (bool rejected)"

    def test_non_int_rejected(self) -> None:
        specs = [IntFieldSpec(name="a")]
        with pytest.raises(BadFieldError) as exc_info:
            parse_int_kwargs({"a": "1"}, specs)
        assert exc_info.value.reason == "must be an int (bool rejected)"

    def test_below_minimum_rejected(self) -> None:
        specs = [IntFieldSpec(name="a", minimum=10)]
        with pytest.raises(BadFieldError) as exc_info:
            parse_int_kwargs({"a": 9}, specs)
        assert exc_info.value.reason == "must be >= 10"

    def test_minimum_boundary_accepted(self) -> None:
        specs = [IntFieldSpec(name="a", minimum=10)]
        assert parse_int_kwargs({"a": 10}, specs) == {"a": 10}

    def test_above_maximum_rejected(self) -> None:
        specs = [IntFieldSpec(name="a", maximum=100)]
        with pytest.raises(BadFieldError) as exc_info:
            parse_int_kwargs({"a": 101}, specs)
        assert exc_info.value.reason == "must be <= 100"

    def test_maximum_boundary_accepted(self) -> None:
        specs = [IntFieldSpec(name="a", maximum=100)]
        assert parse_int_kwargs({"a": 100}, specs) == {"a": 100}

    def test_short_circuits_on_first_error(self) -> None:
        # Spec order determines which field reports the error
        specs = [IntFieldSpec(name="a", minimum=0), IntFieldSpec(name="b", minimum=0)]
        with pytest.raises(BadFieldError) as exc_info:
            parse_int_kwargs({"a": -1, "b": -2}, specs)
        assert exc_info.value.field == "a"

    def test_kwargs_dict_preserves_spec_order(self) -> None:
        specs = [
            IntFieldSpec(name="z", default=1),
            IntFieldSpec(name="a", default=2),
            IntFieldSpec(name="m", default=3),
        ]
        result = parse_int_kwargs({}, specs)
        assert list(result.keys()) == ["z", "a", "m"]

    def test_empty_specs_yields_empty_dict(self) -> None:
        assert parse_int_kwargs({"a": 1}, []) == {}


class TestEndpointSchema:
    """EndpointSchema bundles per-endpoint int field specs + descriptive
    metadata for OpenAPI generation."""

    def test_empty_request_body_schema(self) -> None:
        schema = EndpointSchema()
        body = schema.to_request_body_schema()
        assert body == {"type": "object", "properties": {}}

    def test_request_body_schema_with_required_fields(self) -> None:
        schema = EndpointSchema(
            int_fields=(
                IntFieldSpec(name="a", minimum=1),
                IntFieldSpec(name="b", default=10, maximum=100),
            ),
        )
        body = schema.to_request_body_schema()
        assert body["type"] == "object"
        assert "a" in body["properties"]
        assert "b" in body["properties"]
        assert body["properties"]["a"] == {"type": "integer", "minimum": 1}
        assert body["properties"]["b"] == {"type": "integer", "maximum": 100, "default": 10}
        assert body["required"] == ["a"]  # only `a` is required (b has default)

    def test_no_required_omits_required_field(self) -> None:
        schema = EndpointSchema(int_fields=(IntFieldSpec(name="a", default=0),))
        body = schema.to_request_body_schema()
        assert "required" not in body
