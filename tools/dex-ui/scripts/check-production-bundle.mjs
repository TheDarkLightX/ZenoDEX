#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const uiRoot = path.resolve(scriptDir, '..');
const distRoot = path.join(uiRoot, 'dist');

const forbidden = [
  ['declarative demo marker', /\bdemo(?:s|[_-][a-z0-9_-]+)?\b/i],
  ['declarative mock marker', /\bmock(?:s|ed|ing|[_-][a-z0-9_-]+)?\b/i],
  ['declarative fixture marker', /\bfixture(?:s|[_-][a-z0-9_-]+)?\b/i],
  ['declarative faucet marker', /\bfaucet\b/i],
  ['declarative smoke marker', /\bsmoke\b/i],
  ['declarative synthetic marker', /\bsynthetic(?:[_-][a-z0-9_-]+)?\b/i],
  ['raw-key marker', /\braw[-_ ]?key\b/i],
  ['local-test marker', /\blocal[-_ ]?test(?:net)?\b/i],
  ['retired N-party perps marker', /clearinghouse_np|perp:chnp:|init_market_np|allow_nonproduction_np/i],
  ['bundled local market placeholder', /perp:ch2p:local/i],
  ['local-network UI copy', /local Tau node|oracle (?:production|network).{0,32}\blocal\b/i],
  ['query smoke harness', /zenodexUiSmoke|uiSmoke/i],
  ['demo-mode runtime', /DemoMode|demoMode|allowDemoMode/],
  ['proof-mining workbench', /ProofMiningWorkbench|proof mining smoke|faucet_mint/i],
  ['bundled mock data', /mockData|perpMockData|DEMO_(?:POOLS|TOKENS|MARKETS|POSITIONS|HISTORY|STRATEGIES)/],
  ['synthetic swap fallback', /FALLBACK_SWAP|Reference snapshot|reference reserve snapshot/i],
  ['fixture-funded settlement', /local_ledger_fixture|fund_local_fixture|local_fixture_mode/],
  ['fixture faucet endpoint', /\/testnet-faucet|apiMintTestnetFaucet/],
  ['local chain fallback', /zeno-ledger-localtest-v0|tau-local|\blocal-test(?:net)?\b/i],
  ['browser-local Oracle fallback', /https?:\/\/(?:127\.0\.0\.1|localhost):8787/i],
  ['browser or raw-key signer', /signer_privkey|generateLocalTauWallet|browser-local-last-resort|browser key generation|\bLocal signer\b/i],
  ['synthetic asset placeholder', /CUSTOM Token|synthetic (?:pool|token|reserve|balance|market)/i],
  ['zUSD submit before external-envelope integration', /apiSubmitZusd|\/api\/zusd\/(?:wallet|monetary)\/submit/i],
];

const required = [
  ['Oracle authority fails closed', /zeno_oracle_api_base_unconfigured/],
  ['liquidity preview authority fails closed', /live_pool_snapshot_unavailable/],
  ['tokenomics values fail closed', /No bundled supply values are substituted\./],
];

function walk(dir) {
  const out = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) out.push(...walk(full));
    else if (/\.(?:css|html|js|json|map|svg|txt|webmanifest|xml)$/i.test(entry.name)) out.push(full);
  }
  return out;
}

if (!fs.existsSync(distRoot)) {
  console.error('production-bundle: dist directory is missing; run the production build first');
  process.exit(1);
}

const violations = [];
let emittedText = '';
const retiredAuditContract = path.join(distRoot, 'zenodex-ui-contract.json');
if (fs.existsSync(retiredAuditContract)) {
  violations.push('dist/zenodex-ui-contract.json: audit evidence must not be shipped');
}
for (const file of walk(distRoot)) {
  const body = fs.readFileSync(file, 'utf8');
  emittedText += `\n${body}`;
  for (const [label, pattern] of forbidden) {
    const match = pattern.exec(body);
    if (match) {
      violations.push(`${path.relative(uiRoot, file)}: ${label}: ${JSON.stringify(match[0])}`);
    }
  }
}
for (const [label, pattern] of required) {
  if (!pattern.test(emittedText)) {
    violations.push(`dist: required production behavior missing: ${label}`);
  }
}

if (violations.length > 0) {
  console.error('production-bundle: forbidden demo/test functionality is present');
  for (const violation of violations) console.error(`- ${violation}`);
  process.exit(1);
}

console.log('production-bundle: demo/test functionality absent');
