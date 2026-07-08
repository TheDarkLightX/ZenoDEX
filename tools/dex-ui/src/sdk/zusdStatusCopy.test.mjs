import assert from 'node:assert/strict';
import { test } from 'node:test';

import { formatZusdStatusIssue } from '../components/zusd/statusCopy.js';

test('zUSD transport failures are mapped to user recovery copy without raw status tokens', () => {
  for (const raw of ['http_500', 'not_found', 'status_unavailable']) {
    const message = formatZusdStatusIssue(raw);
    assert.doesNotMatch(message, /http_500|not_found|status_unavailable|Status error:/i);
    assert.doesNotMatch(message, /\bunavailable\b/i);
    assert.match(message, /local node|local testnet/i);
  }
});
