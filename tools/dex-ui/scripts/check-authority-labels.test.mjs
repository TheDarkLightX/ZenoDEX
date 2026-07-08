import assert from 'node:assert/strict';
import { describe, it } from 'node:test';

import { scanSourceText } from './check-authority-labels.mjs';

describe('authority label scanner', () => {
  it('accepts advisory wording when it preserves the authority boundary', () => {
    const source = `
      <span>Spec-checked (proofs off)</span>
      <p>Spec conformance only, not a production proof.</p>
      <p>Runtime admission and ledger acceptance remain authoritative.</p>
    `;
    assert.deepEqual(scanSourceText(source, 'src/components/Example.jsx'), []);
  });

  it('rejects advisory wording coupled to settlement finality', () => {
    const source = `
      <span>Spec-checked (proofs off)</span>
      <p>The ledger accepted this swap. Settlement is final.</p>
    `;
    const violations = scanSourceText(source, 'src/components/Example.jsx');
    assert.equal(violations.length > 0, true);
    assert.match(violations[0].reason, /finality|authority/);
  });

  it('rejects broad verified-by spec badges', () => {
    const source = `
      <span>Verified by cpmm_v1</span>
    `;
    const violations = scanSourceText(source, 'src/components/VerifiedBySpec.jsx');
    assert.equal(violations.length, 1);
    assert.match(violations[0].reason, /Spec-bound/);
  });
});
