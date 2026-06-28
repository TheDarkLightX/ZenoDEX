import assert from 'node:assert/strict';
import test from 'node:test';
import { createSupervisorExecutionId } from './executionIds.js';

function deterministicCrypto(byte) {
  return {
    getRandomValues(bytes) {
      bytes.fill(byte);
      return bytes;
    },
  };
}

test('createSupervisorExecutionId returns safe supervisor replay keys', () => {
  const id = createSupervisorExecutionId({ now: () => 1_777_777_777_000, crypto: deterministicCrypto(0xab) });

  assert.match(id, /^strategy-ui-supervisor-[a-z0-9]+-[a-f0-9]{32}$/);
  assert.equal(id.length <= 128, true);
  assert.equal(/\s/.test(id), false);
});

test('createSupervisorExecutionId is per-call unique with crypto entropy', () => {
  let counter = 0;
  const crypto = {
    getRandomValues(bytes) {
      bytes.fill(counter);
      counter += 1;
      return bytes;
    },
  };

  const ids = new Set(Array.from({ length: 32 }, () => createSupervisorExecutionId({ now: () => 1, crypto })));

  assert.equal(ids.size, 32);
});

test('createSupervisorExecutionId does not fall back to the historic static ID', () => {
  const ids = new Set(
    Array.from({ length: 100 }, (_, idx) => createSupervisorExecutionId({
      now: () => idx,
      random: () => (idx + 1) / 101,
      crypto: null,
    })),
  );

  assert.equal(ids.has('strategy-ui-supervisor-1'), false);
  assert.equal(ids.size, 100);
});
