import assert from 'node:assert/strict';
import test from 'node:test';

import {
  getRuntimeValueRoutePresentationV1,
  isLocalTestnetDeployment,
  readLocalSmokeFragmentSecret,
} from './api.js';

function withWindow(windowMock, fn) {
  const originalWindow = globalThis.window;
  const originalConfig = globalThis.window?.__ZENODEX_CONFIG__;
  if (windowMock === null) {
    delete globalThis.window;
  } else {
    globalThis.window = windowMock;
  }
  try {
    return fn();
  } finally {
    if (originalWindow === undefined) {
      delete globalThis.window;
    } else {
      globalThis.window = originalWindow;
      if (originalConfig !== undefined) {
        globalThis.window.__ZENODEX_CONFIG__ = originalConfig;
      }
    }
  }
}

test('isLocalTestnetDeployment returns true for local-testnet', () => {
  assert.equal(isLocalTestnetDeployment({ deployment: 'local-testnet' }), true);
});

test('isLocalTestnetDeployment returns true for localtest', () => {
  assert.equal(isLocalTestnetDeployment({ deployment: 'localtest' }), true);
});

test('isLocalTestnetDeployment is case-insensitive', () => {
  assert.equal(isLocalTestnetDeployment({ deployment: 'Local-Testnet' }), true);
  assert.equal(isLocalTestnetDeployment({ deployment: 'LOCALTEST' }), true);
});

test('isLocalTestnetDeployment returns false for production', () => {
  assert.equal(isLocalTestnetDeployment({ deployment: 'production' }), false);
});

test('isLocalTestnetDeployment returns false for undefined deployment', () => {
  assert.equal(isLocalTestnetDeployment({}), false);
  assert.equal(isLocalTestnetDeployment(undefined), false);
});

test('isLocalTestnetDeployment returns false for empty string', () => {
  assert.equal(isLocalTestnetDeployment({ deployment: '' }), false);
});

test('isLocalTestnetDeployment returns false when window is undefined (SSR)', () => {
  withWindow(null, () => {
    assert.equal(isLocalTestnetDeployment(), false);
  });
});

test('readLocalSmokeFragmentSecret returns empty when not local-testnet', () => {
  withWindow({ __ZENODEX_CONFIG__: { deployment: 'production' }, location: { hash: '#signerPrivkey=abc' } }, () => {
    assert.equal(readLocalSmokeFragmentSecret('signerPrivkey'), '');
  });
});

test('readLocalSmokeFragmentSecret returns empty when no hash fragment', () => {
  withWindow({ __ZENODEX_CONFIG__: { deployment: 'local-testnet' }, location: { hash: '' } }, () => {
    assert.equal(readLocalSmokeFragmentSecret('signerPrivkey'), '');
  });
});

test('readLocalSmokeFragmentSecret returns value from hash fragment', () => {
  withWindow({ __ZENODEX_CONFIG__: { deployment: 'local-testnet' }, location: { hash: '#signerPrivkey=0xdeadbeef' } }, () => {
    assert.equal(readLocalSmokeFragmentSecret('signerPrivkey'), '0xdeadbeef');
  });
});

test('readLocalSmokeFragmentSecret accepts array of alias names', () => {
  withWindow({ __ZENODEX_CONFIG__: { deployment: 'local-testnet' }, location: { hash: '#accountPrivkey=0xabc' } }, () => {
    assert.equal(readLocalSmokeFragmentSecret(['accountAPrivkey', 'accountPrivkey']), '0xabc');
  });
});

test('readLocalSmokeFragmentSecret returns first matching alias', () => {
  withWindow({ __ZENODEX_CONFIG__: { deployment: 'local-testnet' }, location: { hash: '#accountAPrivkey=0xaaa&accountPrivkey=0xbbb' } }, () => {
    assert.equal(readLocalSmokeFragmentSecret(['accountAPrivkey', 'accountPrivkey']), '0xaaa');
  });
});

test('readLocalSmokeFragmentSecret returns empty when key not in fragment', () => {
  withWindow({ __ZENODEX_CONFIG__: { deployment: 'local-testnet' }, location: { hash: '#otherKey=0x123' } }, () => {
    assert.equal(readLocalSmokeFragmentSecret('signerPrivkey'), '');
  });
});

test('readLocalSmokeFragmentSecret returns empty when window is undefined (SSR)', () => {
  withWindow(null, () => {
    assert.equal(readLocalSmokeFragmentSecret('signerPrivkey'), '');
  });
});

test('value route presentation fails closed for absent and malformed configuration', () => {
  const malformedConfigs = [
    undefined,
    null,
    '',
    [],
    {},
    {
      perpsWalletUiEnabled: 'true',
      zusdTauWalletUiEnabled: 1,
      zusdMonetaryWalletUiEnabled: Object(true),
    },
  ];

  for (const runtimeConfig of malformedConfigs) {
    assert.deepEqual(getRuntimeValueRoutePresentationV1(runtimeConfig), {
      perpsWalletEnabled: false,
      zusdTauWalletEnabled: false,
      zusdMonetaryWalletEnabled: false,
    });
  }
});

test('value route presentation rejects inherited enable flags', () => {
  const runtimeConfig = Object.create({
    perpsWalletUiEnabled: true,
    zusdTauWalletUiEnabled: true,
    zusdMonetaryWalletUiEnabled: true,
  });

  assert.deepEqual(getRuntimeValueRoutePresentationV1(runtimeConfig), {
    perpsWalletEnabled: false,
    zusdTauWalletEnabled: false,
    zusdMonetaryWalletEnabled: false,
  });
});

test('value route presentation accepts only exact owned true flags', () => {
  const presentation = getRuntimeValueRoutePresentationV1({
    perpsWalletUiEnabled: true,
    zusdTauWalletUiEnabled: false,
    zusdMonetaryWalletUiEnabled: true,
  });

  assert.deepEqual(presentation, {
    perpsWalletEnabled: true,
    zusdTauWalletEnabled: false,
    zusdMonetaryWalletEnabled: true,
  });
});

test('value route presentation is an immutable snapshot', () => {
  const runtimeConfig = {
    perpsWalletUiEnabled: true,
    zusdTauWalletUiEnabled: true,
    zusdMonetaryWalletUiEnabled: true,
  };

  const presentation = getRuntimeValueRoutePresentationV1(runtimeConfig);
  runtimeConfig.perpsWalletUiEnabled = false;

  assert.equal(Object.isFrozen(presentation), true);
  assert.equal(presentation.perpsWalletEnabled, true);
  assert.throws(() => {
    presentation.perpsWalletEnabled = false;
  }, TypeError);
});
