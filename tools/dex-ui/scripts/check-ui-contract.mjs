#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const uiRoot = path.resolve(path.dirname(__filename), '..');
const contractPath = path.join(uiRoot, 'public', 'zenodex-ui-contract.json');
const packagePath = path.join(uiRoot, 'package.json');
const srcRoot = path.join(uiRoot, 'src');

function fail(message) {
  console.error(`ui-contract: ${message}`);
  process.exitCode = 1;
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function walkFiles(root) {
  const out = [];
  for (const entry of fs.readdirSync(root, { withFileTypes: true })) {
    const fullPath = path.join(root, entry.name);
    if (entry.isDirectory()) {
      out.push(...walkFiles(fullPath));
    } else if (entry.isFile()) {
      out.push(fullPath);
    }
  }
  return out;
}

function lineNumberForPattern(body, pattern) {
  const match = pattern.exec(body);
  if (!match) return 0;
  return body.slice(0, match.index).split('\n').length;
}

const contract = readJson(contractPath);
if (contract.schema !== 'zenodex.dex_ui.surface_contract.v1') {
  fail(`unexpected schema: ${contract.schema}`);
}
if (typeof contract.version !== 'string' || contract.version.length === 0) {
  fail('contract version must be non-empty');
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

const falseAuthorityPatterns = [
  {
    pattern: /setTimeout\s*\([\s\S]{0,1600}status:\s*['"]confirmed['"]/m,
    reason: 'submissions must not be promoted to accepted/confirmed by a timer',
  },
  {
    pattern: /Swap Confirmed|Wallet submission confirmed|Broadcasting transaction to Tau Net Alpha/m,
    reason: 'transaction-hash submission copy must not imply runtime acceptance',
  },
  {
    pattern: /Verified math\s*·\s*proofs off|Math verified\s*\(proofs off\)/m,
    reason: 'proof-off UI must say spec-checked, not verified',
  },
];

for (const sourcePath of walkFiles(srcRoot)) {
  const relPath = path.relative(uiRoot, sourcePath);
  const body = fs.readFileSync(sourcePath, 'utf8');
  for (const rule of falseAuthorityPatterns) {
    const line = lineNumberForPattern(body, rule.pattern);
    if (line > 0) {
      fail(`${relPath}:${line}: ${rule.reason}`);
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
