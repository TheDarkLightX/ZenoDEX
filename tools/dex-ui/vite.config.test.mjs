import assert from 'node:assert/strict';
import test from 'node:test';

import {
  discoverLocalTestnetApiProxyTarget,
  parseDockerPublishedPort,
  resolveApiProxyTarget,
} from './vite.config.js';

test('parseDockerPublishedPort normalizes loopback-safe Docker bindings', () => {
  assert.equal(parseDockerPublishedPort('127.0.0.1:19108'), 'http://127.0.0.1:19108');
  assert.equal(parseDockerPublishedPort('0.0.0.0:19108'), 'http://127.0.0.1:19108');
  assert.equal(parseDockerPublishedPort('[::]:19108'), 'http://127.0.0.1:19108');
  assert.equal(parseDockerPublishedPort('bad'), '');
});

test('resolveApiProxyTarget respects explicit API_PROXY_TARGET including empty disable', () => {
  assert.equal(
    resolveApiProxyTarget({ env: { API_PROXY_TARGET: 'http://127.0.0.1:19108/' } }),
    'http://127.0.0.1:19108',
  );
  assert.equal(resolveApiProxyTarget({ env: { API_PROXY_TARGET: '' } }), '');
});

test('discoverLocalTestnetApiProxyTarget finds the running local-testnet nginx host port', () => {
  const calls = [];
  const execFile = (cmd, args) => {
    calls.push([cmd, args]);
    if (args[0] === 'ps') {
      return [
        'zenodex-local-testnet-9cafb4ab-zenodex-nginx-1\tzenodex-local-testnet-9cafb4ab',
        'unrelated-nginx\tother-project',
      ].join('\n');
    }
    if (args[0] === 'port') {
      assert.equal(args[1], 'zenodex-local-testnet-9cafb4ab-zenodex-nginx-1');
      return '127.0.0.1:19108\n';
    }
    throw new Error(`unexpected docker args: ${args.join(' ')}`);
  };

  assert.equal(
    discoverLocalTestnetApiProxyTarget({ execFile }),
    'http://127.0.0.1:19108',
  );
  assert.equal(calls.length, 2);
});

test('resolveApiProxyTarget falls back to the historical API port without local-testnet', () => {
  const execFile = () => {
    throw new Error('docker unavailable');
  };
  assert.equal(
    resolveApiProxyTarget({ command: 'serve', env: {}, execFile }),
    'http://127.0.0.1:8000',
  );
});
