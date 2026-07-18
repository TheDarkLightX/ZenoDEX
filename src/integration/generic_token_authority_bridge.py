"""Strict canonical app-state ABI for generic-token authority state."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from ..core.generic_token_authority import (
    GenericTokenAssetAuthority,
    GenericTokenAuthorityState,
)

GENERIC_TOKEN_AUTHORITY_SCHEMA = "zenodex/generic_token_authority/v1"
GENERIC_TOKEN_AUTHORITY_VERSION = 1


def generic_token_authority_to_obj(
    state: GenericTokenAuthorityState,
) -> dict[str, Any]:
    if not isinstance(state, GenericTokenAuthorityState):
        raise TypeError("state must be a GenericTokenAuthorityState")
    return {
        "schema": GENERIC_TOKEN_AUTHORITY_SCHEMA,
        "version": GENERIC_TOKEN_AUTHORITY_VERSION,
        "assets": [
            {
                "asset_id": asset.asset_id,
                "total_supply_units": asset.total_supply_units,
                "mint_authority_pubkey": asset.mint_authority_pubkey,
            }
            for asset in state.assets
        ],
    }


def generic_token_authority_from_obj(obj: object) -> GenericTokenAuthorityState:
    if not isinstance(obj, Mapping):
        raise TypeError("generic_token_authority must be an object")
    if set(obj) != {"schema", "version", "assets"}:
        raise ValueError(
            "generic_token_authority fields must match the v1 schema exactly"
        )
    if obj.get("schema") != GENERIC_TOKEN_AUTHORITY_SCHEMA:
        raise ValueError("unsupported generic_token_authority schema")
    version = obj.get("version")
    if type(version) is not int or version != GENERIC_TOKEN_AUTHORITY_VERSION:
        raise ValueError("unsupported generic_token_authority version")
    raw_assets = obj.get("assets")
    if not isinstance(raw_assets, list):
        raise TypeError("generic_token_authority.assets must be a list")

    assets: list[GenericTokenAssetAuthority] = []
    previous_asset: str | None = None
    for index, raw_asset in enumerate(raw_assets):
        if not isinstance(raw_asset, Mapping):
            raise TypeError(
                f"generic_token_authority.assets[{index}] must be an object"
            )
        if set(raw_asset) != {
            "asset_id",
            "total_supply_units",
            "mint_authority_pubkey",
        }:
            raise ValueError(
                f"generic_token_authority.assets[{index}] fields must match exactly"
            )
        asset_id = raw_asset.get("asset_id")
        supply = raw_asset.get("total_supply_units")
        authority = raw_asset.get("mint_authority_pubkey")
        if not isinstance(asset_id, str):
            raise TypeError(
                f"generic_token_authority.assets[{index}].asset_id must be a string"
            )
        if type(supply) is not int:
            raise TypeError(
                f"generic_token_authority.assets[{index}].total_supply_units must be an int"
            )
        if authority is not None and not isinstance(authority, str):
            raise TypeError(
                f"generic_token_authority.assets[{index}].mint_authority_pubkey "
                "must be a string or null"
            )
        entry = GenericTokenAssetAuthority(
            asset_id=asset_id,
            total_supply_units=supply,
            mint_authority_pubkey=authority,
        )
        if entry.asset_id != asset_id:
            raise ValueError(
                f"generic_token_authority.assets[{index}].asset_id must use "
                "canonical lowercase wire form"
            )
        if authority is not None and entry.mint_authority_pubkey != authority:
            raise ValueError(
                f"generic_token_authority.assets[{index}].mint_authority_pubkey "
                "must use canonical lowercase wire form"
            )
        if previous_asset is not None and entry.asset_id <= previous_asset:
            raise ValueError(
                "generic_token_authority.assets must be strictly sorted by asset_id"
            )
        assets.append(entry)
        previous_asset = entry.asset_id
    return GenericTokenAuthorityState(assets=tuple(assets))
