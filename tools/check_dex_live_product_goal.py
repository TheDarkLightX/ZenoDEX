#!/usr/bin/env python3
"""Audit the fail-closed, live-only ZenoDEX production UI boundary."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "zenodex/dex_live_product_goal_audit/v1"


@dataclass(frozen=True)
class AnchorCheck:
    area_id: str
    check_id: str
    path: str
    anchors: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class ForbiddenCheck:
    area_id: str
    check_id: str
    path: str
    pattern: re.Pattern[str]
    description: str


ANCHOR_CHECKS: tuple[AnchorCheck, ...] = (
    AnchorCheck(
        area_id="mounted_live_surfaces",
        check_id="app_mounts_only_supported_product_tabs",
        path="tools/dex-ui/src/App.jsx",
        description="The production shell mounts the six supported live product surfaces.",
        anchors=(
            "swap: () => import('./components/SwapInterface')",
            "pools: () => import('./components/PoolDashboard')",
            "stats: () => import('./components/TokenStats')",
            "perps: () => import('./components/perps/PerpTradingView')",
            "zusd: () => import('./components/ZUSDWorkbench.jsx')",
            "oracle: () => import('./components/ZenoOracleDashboard.jsx')",
            "const [wallet, setWallet] = useState(null)",
        ),
    ),
    AnchorCheck(
        area_id="mounted_live_surfaces",
        check_id="zusd_mounts_live_prepare_surfaces",
        path="tools/dex-ui/src/components/ZUSDWorkbench.jsx",
        description="The zUSD route mounts live monetary and token-wallet views.",
        anchors=("<ZUSDMonetarySurface />", "<ZUSDTauWalletSurface />"),
    ),
    AnchorCheck(
        area_id="live_data_authority",
        check_id="swap_feed_fails_to_empty_unavailable_state",
        path="tools/dex-ui/src/lib/swapData.js",
        description="A failed spot feed cannot be replaced by synthetic reserves or balances.",
        anchors=("source: 'unavailable'", "pools: {}", "tokens: []"),
    ),
    AnchorCheck(
        area_id="live_data_authority",
        check_id="oracle_is_read_only_live_dashboard",
        path="tools/dex-ui/src/components/ZenoOracleDashboard.jsx",
        description="The Oracle surface displays only live dashboard responses.",
        anchors=(
            "fetch(oracleApiUrl('/api/oracle/dashboard')",
            "This surface never synthesizes or submits reports",
            "Only feed rows returned by the live node are displayed",
        ),
    ),
    AnchorCheck(
        area_id="live_data_authority",
        check_id="perps_reads_tau_wallet_status",
        path="tools/dex-ui/src/lib/PerpProvider.jsx",
        description="Perpetuals market state comes from the live wallet status endpoint.",
        anchors=("const statusResp = await apiGetPerpsWalletStatus", "const status = statusResp?.status || {}"),
    ),
    AnchorCheck(
        area_id="signer_and_write_boundary",
        check_id="wallet_connection_requires_external_signer_and_chain",
        path="tools/dex-ui/src/components/WalletConnect.jsx",
        description="Wallet connection fails closed without a configured chain and external signer.",
        anchors=("throw new Error('chain_id_unavailable')", "connectPreferredWallet", "External signer"),
    ),
    AnchorCheck(
        area_id="signer_and_write_boundary",
        check_id="perps_writes_require_external_signer",
        path="tools/dex-ui/src/lib/PerpProvider.jsx",
        description="Perpetuals writes require an external signing callback.",
        anchors=(
            "const writeEnabled = Boolean(externalTauSigner)",
            "Trader writes require a production signer bridge",
            "The browser does not hold or forward private keys",
        ),
    ),
    AnchorCheck(
        area_id="signer_and_write_boundary",
        check_id="zusd_monetary_is_prepare_only",
        path="tools/dex-ui/src/components/ZUSDMonetarySurface.jsx",
        description="zUSD monetary writes remain excluded until signed-envelope integration exists.",
        anchors=("apiPrepareZusdMonetary", "Production profile is prepare-only", "Prepare unsigned request"),
    ),
    AnchorCheck(
        area_id="signer_and_write_boundary",
        check_id="zusd_wallet_is_prepare_only",
        path="tools/dex-ui/src/components/ZUSDTauWalletSurface.jsx",
        description="zUSD token-wallet writes remain excluded until signed-envelope integration exists.",
        anchors=("apiPrepareZusdWallet", "External signer required", "Prepare unsigned request"),
    ),
    AnchorCheck(
        area_id="artifact_exclusion",
        check_id="production_build_scans_emitted_bytes",
        path="tools/dex-ui/package.json",
        description="Every production build runs the emitted-byte exclusion scan.",
        anchors=("vite build && node scripts/check-production-bundle.mjs",),
    ),
    AnchorCheck(
        area_id="artifact_exclusion",
        check_id="bundle_scan_covers_demo_and_signer_failures",
        path="tools/dex-ui/scripts/check-production-bundle.mjs",
        description="The artifact gate excludes query writes, fixtures, synthetic data, and raw/browser signing.",
        anchors=(
            "query smoke harness",
            "demo-mode runtime",
            "fixture-funded settlement",
            "browser or raw-key signer",
            "synthetic asset placeholder",
        ),
    ),
    AnchorCheck(
        area_id="artifact_exclusion",
        check_id="production_runtime_config_is_explicit",
        path="tools/dex-ui/public/zenodex-config.json",
        description="The checked-in runtime configuration declares production and fails closed without a chain injection.",
        anchors=('"deployment": "production"', '"chainId": ""'),
    ),
    AnchorCheck(
        area_id="artifact_exclusion",
        check_id="ui_contract_pins_live_only_boundary",
        path="tools/dex-ui/audit/production-surface-contract.json",
        description="The UI contract pins the live-only, prepare-only production posture.",
        anchors=(
            "dex-ui-production-facing-20260719-v6",
            "production_bundle_demo_free",
            "wallet_connection_requires_real_signer",
            "oracle_read_only_live_dashboard",
        ),
    ),
)


FORBIDDEN_CHECKS: tuple[ForbiddenCheck, ...] = (
    ForbiddenCheck(
        area_id="mounted_live_surfaces",
        check_id="removed_fixture_surfaces_are_not_mounted",
        path="tools/dex-ui/src/App.jsx",
        description="Removed fixture-backed surfaces cannot be imported, routed, or prefetched.",
        pattern=re.compile(r"(?:StrategyWorkbench|ConfidentialWorkbench|ProofMiningWorkbench|PerpsGovernanceSurface|DemoModeProvider)"),
    ),
    ForbiddenCheck(
        area_id="live_data_authority",
        check_id="token_selector_has_no_placeholder_import",
        path="tools/dex-ui/src/components/TokenSelectModal.jsx",
        description="Token selection cannot construct a placeholder asset.",
        pattern=re.compile(r"(?:allowImportCustom|CUSTOM\s+Token|DEFAULT_TOKENS)"),
    ),
    ForbiddenCheck(
        area_id="signer_and_write_boundary",
        check_id="wallet_policy_has_no_browser_key_fallback",
        path="tools/dex-ui/src/sdk/walletSignerPolicy.js",
        description="The production wallet policy cannot generate or fall back to a browser key.",
        pattern=re.compile(r"(?:browserKeyGenerationAllowed|allowBrowserFallback|generateLocalTauWallet|browser-local-last-resort)"),
    ),
    ForbiddenCheck(
        area_id="signer_and_write_boundary",
        check_id="production_intent_sdk_has_no_raw_key_signer",
        path="tools/dex-ui/src/sdk/dexIntentSigner.js",
        description="Raw-key signing fixtures are isolated from production intent construction.",
        pattern=re.compile(r"(?:privkey|signTauTransactionPayload|signDexIntentForEngine|signPerpOpForEngine)"),
    ),
    ForbiddenCheck(
        area_id="signer_and_write_boundary",
        check_id="zusd_monetary_has_no_submit_or_raw_key",
        path="tools/dex-ui/src/components/ZUSDMonetarySurface.jsx",
        description="The monetary surface cannot submit or forward raw key material.",
        pattern=re.compile(r"(?:apiSubmitZusdMonetary|signer_privkey)"),
    ),
    ForbiddenCheck(
        area_id="signer_and_write_boundary",
        check_id="zusd_wallet_has_no_submit_or_raw_key",
        path="tools/dex-ui/src/components/ZUSDTauWalletSurface.jsx",
        description="The token-wallet surface cannot submit or forward raw key material.",
        pattern=re.compile(r"(?:apiSubmitZusdWallet|signer_privkey)"),
    ),
    ForbiddenCheck(
        area_id="artifact_exclusion",
        check_id="runtime_config_exposes_no_demo_or_browser_key_switch",
        path="tools/dex-ui/public/zenodex-config.json",
        description="Production runtime configuration exposes no demo or browser-key capability.",
        pattern=re.compile(r'"(?:demoMode|allowDemoMode|allowBrowserKeyGeneration)"'),
    ),
)


AREA_TITLES: dict[str, str] = {
    "mounted_live_surfaces": "Mounted Live Surfaces",
    "live_data_authority": "Live Data Authority",
    "signer_and_write_boundary": "Signer And Write Boundary",
    "artifact_exclusion": "Production Artifact Exclusion",
}


RESIDUAL_LIMITS: tuple[dict[str, str], ...] = (
    {
        "id": "production_chain_configuration",
        "description": "The production deployer must inject a non-empty approved chain ID; the checked-in artifact intentionally fails closed.",
    },
    {
        "id": "zusd_external_signed_envelopes",
        "description": "zUSD remains prepare-only until its APIs consume externally signed envelopes without browser or server raw-key custody.",
    },
    {
        "id": "production_oracle_authority",
        "description": "Public-testnet evidence for the intended production Oracle authority lifecycle remains a promotion obligation.",
    },
    {
        "id": "production_proof_artifacts",
        "description": "Production circuit/verifier artifacts and same-commit refinement evidence remain promotion obligations.",
    },
)


def _normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _read_text(root: Path, rel_path: str) -> tuple[str | None, str | None]:
    path = root / rel_path
    if not path.is_file():
        return None, "missing_file"
    return path.read_text(encoding="utf-8"), None


def check_anchor(check: AnchorCheck, *, root: Path = REPO_ROOT) -> dict[str, Any]:
    text, error = _read_text(root, check.path)
    missing = list(check.anchors)
    if text is not None:
        normalized = _normalize(text)
        missing = [anchor for anchor in check.anchors if _normalize(anchor) not in normalized]
    return {
        "id": check.check_id,
        "kind": "anchors",
        "path": check.path,
        "ok": error is None and not missing,
        "description": check.description,
        "missing": missing,
        "error": error,
    }


def check_forbidden(check: ForbiddenCheck, *, root: Path = REPO_ROOT) -> dict[str, Any]:
    text, error = _read_text(root, check.path)
    matches: list[str] = []
    if text is not None:
        matches = [match.group(0) for match in check.pattern.finditer(_normalize(text))]
    return {
        "id": check.check_id,
        "kind": "forbidden",
        "path": check.path,
        "ok": error is None and not matches,
        "description": check.description,
        "matches": matches,
        "error": error,
    }


def _group_by_area(checks: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = {area_id: [] for area_id in AREA_TITLES}
    for check in checks:
        grouped.setdefault(str(check["area_id"]), []).append(
            {key: value for key, value in check.items() if key != "area_id"}
        )
    return [
        {
            "id": area_id,
            "title": AREA_TITLES.get(area_id, area_id),
            "ok": all(check["ok"] for check in area_checks),
            "checks": area_checks,
        }
        for area_id, area_checks in grouped.items()
    ]


def audit_live_product_goal(*, root: Path = REPO_ROOT) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    for anchor_check in ANCHOR_CHECKS:
        result = check_anchor(anchor_check, root=root)
        result["area_id"] = anchor_check.area_id
        checks.append(result)
    for forbidden_check in FORBIDDEN_CHECKS:
        result = check_forbidden(forbidden_check, root=root)
        result["area_id"] = forbidden_check.area_id
        checks.append(result)

    areas = _group_by_area(checks)
    ok = all(area["ok"] for area in areas)
    return {
        "schema": SCHEMA,
        "ok": ok,
        "goal_complete": False,
        "status": "production_live_only_surface_present_with_open_promotion_limits" if ok else "missing_required_goal_evidence",
        "areas": areas,
        "residual_limits": list(RESIDUAL_LIMITS),
    }


def _format_failures(report: dict[str, Any]) -> str:
    lines: list[str] = []
    for area in report["areas"]:
        for check in area["checks"]:
            if check["ok"]:
                continue
            location = f"{area['id']}:{check['id']}:{check['path']}"
            if check.get("error"):
                lines.append(f"{location}: {check['error']}")
            lines.extend(f"{location}: missing anchor: {missing}" for missing in check.get("missing", []))
            lines.extend(f"{location}: forbidden text: {match}" for match in check.get("matches", []))
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    args = parser.parse_args(argv)

    report = audit_live_product_goal(root=args.root)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif report["ok"]:
        print(f"dex live-product goal evidence ok: {report['status']}")
        print("residual limits:")
        for limit in report["residual_limits"]:
            print(f"- {limit['id']}: {limit['description']}")
    else:
        print(_format_failures(report), file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
