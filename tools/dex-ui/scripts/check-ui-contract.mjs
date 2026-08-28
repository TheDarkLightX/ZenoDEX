#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const uiRoot = path.resolve(path.dirname(__filename), '..');
const contractPath = path.join(uiRoot, 'public', 'zenodex-ui-contract.json');
const runtimeConfigPath = path.join(uiRoot, 'public', 'zenodex-config.json');
const packagePath = path.join(uiRoot, 'package.json');
const REQUIRED_QUARANTINED_VALUE_ROUTE_UI_FLAGS = Object.freeze([
  'perpsWalletUiEnabled',
  'zusdTauWalletUiEnabled',
  'zusdMonetaryWalletUiEnabled',
]);

function fail(message) {
  console.error(`ui-contract: ${message}`);
  process.exitCode = 1;
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

const contract = readJson(contractPath);
if (contract.schema !== 'zenodex.dex_ui.surface_contract.v1') {
  fail(`unexpected schema: ${contract.schema}`);
}
if (typeof contract.version !== 'string' || contract.version.length === 0) {
  fail('contract version must be non-empty');
}

const runtimeConfig = readJson(runtimeConfigPath);
const quarantineFields = contract.current_quarantined_value_route_ui_flags;
if (
  !Array.isArray(quarantineFields)
  || quarantineFields.length !== REQUIRED_QUARANTINED_VALUE_ROUTE_UI_FLAGS.length
  || quarantineFields.some((field, index) => field !== REQUIRED_QUARANTINED_VALUE_ROUTE_UI_FLAGS[index])
) {
  fail('current_quarantined_value_route_ui_flags must equal the exact closed current-profile registry');
} else {
  for (const field of quarantineFields) {
    if (!Object.prototype.hasOwnProperty.call(runtimeConfig, field)) {
      fail(`runtime config is missing quarantined value-route UI flag: ${field}`);
      continue;
    }
    if (runtimeConfig[field] !== false) {
      fail(`runtime config must keep ${field} exactly false in the current profile`);
    }
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
