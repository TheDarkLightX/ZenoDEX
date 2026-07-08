#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const uiRoot = path.resolve(path.dirname(__filename), '..');
const srcRoot = path.join(uiRoot, 'src');

const ADVISORY_CUES = [
  /\badvisory\b/i,
  /\bspec-checked\b/i,
  /\bproofs off\b/i,
  /\bspec conformance only\b/i,
  /\bhost-computed\b/i,
  /\bnot a production proof\b/i,
];

const STRONG_AUTHORITY_PATTERNS = [
  /\bauthori[sz](?:e|es|ed|ing|ation)\b/i,
  /\bsettlement is final\b/i,
  /\bledger accepted\b/i,
  /\bproduction proof\b/i,
  /\bsettlement authority\b/i,
];

const ALWAYS_FORBIDDEN = [
  {
    pattern: /\bauthori[sz]es its consensus-critical path\b/i,
    reason: 'spec/model text must not claim it authorizes a consensus-critical path',
  },
  {
    pattern: /\bVerified by\b/,
    reason: 'UI spec badges must use Spec-bound wording, not broad verified-by wording',
  },
];

const FINALITY_ALLOWED_FILES = new Set([
  'src/components/swap/SwapSubmittedModal.jsx',
]);

function walkFiles(dir, out = []) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    if (entry.name === 'node_modules' || entry.name.startsWith('.')) continue;
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      walkFiles(full, out);
      continue;
    }
    if (!/\.(?:jsx|js|mjs)$/.test(entry.name)) continue;
    if (/\.test\.mjs$/.test(entry.name)) continue;
    out.push(full);
  }
  return out.sort();
}

function relPath(filePath) {
  return path.relative(uiRoot, filePath).replaceAll(path.sep, '/');
}

function normalizeLine(line) {
  return String(line || '').replace(/\s+/g, ' ').trim();
}

function hasAdvisoryCue(text) {
  return ADVISORY_CUES.some((pattern) => pattern.test(text));
}

function strongAuthorityMatches(text) {
  return STRONG_AUTHORITY_PATTERNS.filter((pattern) => {
    if (!pattern.test(text)) return false;
    if (pattern.source.includes('production proof') && /\bnot a production proof\b/i.test(text)) {
      return false;
    }
    return true;
  }).map((pattern) => pattern.source);
}

function scanSourceText(sourceText, rel) {
  const violations = [];
  const lines = String(sourceText || '').split(/\r?\n/);

  lines.forEach((line, idx) => {
    for (const rule of ALWAYS_FORBIDDEN) {
      if (rule.pattern.test(line)) {
        violations.push({
          path: rel,
          line: idx + 1,
          reason: rule.reason,
          text: normalizeLine(line),
        });
      }
    }
  });

  lines.forEach((line, idx) => {
    const text = normalizeLine(line);
    if (!text) return;
    if (/\b(setAuthority|authorityStatus|walletAuthority|oracleAuthority|AuthorityProfile|authorityExercise)\b/.test(line)) {
      return;
    }
    const finalityMatches = strongAuthorityMatches(text).filter((pattern) => (
      pattern.includes('settlement is final') || pattern.includes('ledger accepted')
    ));
    if (finalityMatches.length > 0 && !FINALITY_ALLOWED_FILES.has(rel)) {
      violations.push({
        path: rel,
        line: idx + 1,
        reason: 'ledger acceptance/finality wording is only allowed in confirmed submitted-swap receipt UI',
        text,
      });
    }
  });

  lines.forEach((line, idx) => {
    const text = normalizeLine(line);
    if (!hasAdvisoryCue(text)) return;
    const start = Math.max(0, idx - 2);
    const end = Math.min(lines.length - 1, idx + 2);
    const windowText = normalizeLine(lines.slice(start, end + 1).join(' '));
    const matches = strongAuthorityMatches(windowText);
    if (matches.length === 0) return;
    violations.push({
      path: rel,
      line: idx + 1,
      reason: `advisory/spec-only label window contains authority wording: ${matches.join(', ')}`,
      text: windowText,
    });
  });

  return violations;
}

function scanAuthorityLabels({ root = srcRoot } = {}) {
  const files = walkFiles(root);
  const violations = files.flatMap((filePath) => {
    const rel = relPath(filePath);
    return scanSourceText(fs.readFileSync(filePath, 'utf8'), rel);
  });
  return {
    ok: violations.length === 0,
    checked_file_count: files.length,
    violations,
    invariant: 'advisory_or_spec_only_label -> no settlement_authority_wording',
    finality_allowed_files: Array.from(FINALITY_ALLOWED_FILES).sort(),
  };
}

function main() {
  const report = scanAuthorityLabels();
  if (!report.ok) {
    console.error(JSON.stringify(report, null, 2));
    process.exit(1);
  }
  console.log(JSON.stringify(report, null, 2));
}

if (process.argv[1] && fileURLToPath(import.meta.url) === path.resolve(process.argv[1])) {
  main();
}

export {
  scanAuthorityLabels,
  scanSourceText,
};
