#!/usr/bin/env node
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const uiRoot = path.resolve(path.dirname(__filename), '..');
const contractPath = path.join(uiRoot, 'audit', 'production-surface-contract.json');
const packagePath = path.join(uiRoot, 'package.json');
const runtimeConfigPath = path.join(uiRoot, 'public', 'zenodex-config.json');
const retiredPublicContractPath = path.join(uiRoot, 'public', 'zenodex-ui-contract.json');
const retiredRawKeyTestSupportPath = path.join(uiRoot, 'src', 'sdk', 'rawKeySigner.testSupport.mjs');

function fail(message) {
  console.error(`ui-contract: ${message}`);
  process.exitCode = 1;
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function walkSource(dir) {
  const out = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) out.push(...walkSource(full));
    else if (/\.(?:css|js|jsx|mjs)$/i.test(entry.name) && !/\.test\./i.test(entry.name)) out.push(full);
  }
  return out;
}

function countLiteral(body, literal) {
  return body.split(literal).length - 1;
}

function canonicalJson(value) {
  if (Array.isArray(value)) {
    return `[${value.map(canonicalJson).join(',')}]`;
  }
  if (value !== null && typeof value === 'object') {
    return `{${Object.keys(value)
      .sort()
      .map((key) => `${JSON.stringify(key)}:${canonicalJson(value[key])}`)
      .join(',')}}`;
  }
  return JSON.stringify(value);
}

function removeNarrowDefensiveVocabulary(relPath, body) {
  if (relPath !== 'src/sdk/zenoProofClient.js') return body;

  // This parser consumes an untrusted proof-status schema. These three terms
  // are retained solely to identify and block non-production evidence. Keep
  // the exception exact and count-pinned so it cannot mask new UI behavior.
  const allowed = [
    ["'fixture'", 2],
    ['fixture_backed', 3],
    ['non-fixture', 1],
  ];
  let sanitized = body;
  for (const [literal, expectedCount] of allowed) {
    const actualCount = countLiteral(body, literal);
    if (actualCount !== expectedCount) {
      fail(`${relPath} defensive ${JSON.stringify(literal)} count changed: ${actualCount} != ${expectedCount}`);
    }
    sanitized = sanitized.split(literal).join('');
  }
  if (!body.includes("gaps.push('production_security_claim requires strict non-fixture zk mode')")) {
    fail(`${relPath} no longer proves that the defensive fixture vocabulary fails closed`);
  }
  return sanitized;
}

const contract = readJson(contractPath);
if (fs.existsSync(retiredPublicContractPath)) {
  fail('the audit contract must not be present under public/ or copied into production builds');
}
if (fs.existsSync(retiredRawKeyTestSupportPath)) {
  fail('raw-key test support must remain outside the production src/ tree');
}
if (contract.schema !== 'zenodex.dex_ui.surface_contract.v1') {
  fail(`unexpected schema: ${contract.schema}`);
}
if (typeof contract.version !== 'string' || contract.version.length === 0) {
  fail('contract version must be non-empty');
}

const runtimeConfig = readJson(runtimeConfigPath);
const contractHash = `sha256:${crypto
  .createHash('sha256')
  .update(canonicalJson(contract), 'utf8')
  .digest('hex')}`;
const expectedRuntimeBinding = {
  uiSurfaceContractSchema: contract.schema,
  uiSurfaceContractVersion: contract.version,
  uiSurfaceContractHash: contractHash,
};
for (const [key, expected] of Object.entries(expectedRuntimeBinding)) {
  if (runtimeConfig[key] !== expected) {
    fail(`runtime config ${key} does not bind the source contract`);
  }
}

for (const marker of contract.source_markers || []) {
  const relPath = String(marker.path || '');
  const expected = String(marker.contains || '');
  if (!relPath || !expected) {
    fail(`malformed source marker: ${JSON.stringify(marker)}`);
    continue;
  }
  const fullPath = path.join(uiRoot, relPath);
  if (!fs.existsSync(fullPath)) {
    fail(`missing required UI file: ${relPath}`);
    continue;
  }
  const body = fs.readFileSync(fullPath, 'utf8');
  if (!body.includes(expected)) {
    fail(`missing required UI marker in ${relPath}: ${expected}`);
  }
}

for (const marker of contract.forbidden_source_markers || []) {
  const relPath = String(marker.path || '');
  const forbidden = String(marker.forbids || '');
  if (!relPath || !forbidden) {
    fail(`malformed forbidden source marker: ${JSON.stringify(marker)}`);
    continue;
  }
  const fullPath = path.join(uiRoot, relPath);
  if (!fs.existsSync(fullPath)) {
    fail(`missing UI file for forbidden marker: ${relPath}`);
    continue;
  }
  const body = fs.readFileSync(fullPath, 'utf8');
  if (body.includes(forbidden)) {
    fail(`forbidden UI marker in ${relPath}: ${forbidden}`);
  }
}

const broadForbiddenSource = [
  ['demo', /\bdemo(?:s|[_-][a-z0-9_-]+)?\b|DemoMode|demoMode|allowDemoMode/i],
  ['mock', /\bmock(?:s|ed|ing|[_-][a-z0-9_-]+)?\b|mockData|perpMockData/i],
  ['fixture', /\bfixture(?:s|[_-][a-z0-9_-]+)?\b/i],
  ['faucet', /\bfaucet\b|apiMintTestnetFaucet/i],
  ['smoke', /\bsmoke\b|zenodexUiSmoke|uiSmoke/i],
  ['synthetic', /\bsynthetic(?:[_-][a-z0-9_-]+)?\b|FALLBACK_SWAP/i],
  ['raw-key', /\braw[-_ ]?key\b|signer_privkey|generateLocalTauWallet/i],
  ['local-test', /\blocal[-_ ]?test(?:net)?\b|browser-local-last-resort/i],
  ['retired-np-perps', /clearinghouse_np|perp:chnp:|init_market_np|allow_nonproduction_np/i],
];
for (const fullPath of walkSource(path.join(uiRoot, 'src'))) {
  const relPath = path.relative(uiRoot, fullPath).split(path.sep).join('/');
  const body = removeNarrowDefensiveVocabulary(relPath, fs.readFileSync(fullPath, 'utf8'));
  for (const [label, pattern] of broadForbiddenSource) {
    const match = pattern.exec(body);
    if (match) {
      fail(`production source contains ${label} vocabulary in ${relPath}: ${JSON.stringify(match[0])}`);
    }
  }
}

const pkg = readJson(packagePath);
const semverExact = /^\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?$/;
for (const section of ['dependencies', 'devDependencies']) {
  for (const [name, spec] of Object.entries(pkg[section] || {})) {
    if (typeof spec !== 'string') {
      fail(`${section}.${name} must be a string`);
      continue;
    }
    if (spec.startsWith('file:')) {
      continue;
    }
    if (!semverExact.test(spec)) {
      fail(`${section}.${name} must use an exact pinned version, got ${spec}`);
    }
  }
}

if (process.exitCode) {
  process.exit(process.exitCode);
}
console.log(`${contract.version} ok`);
