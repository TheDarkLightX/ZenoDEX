import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import { execFileSync } from 'node:child_process'

// https://vite.dev/config/
const DEFAULT_API_PROXY_TARGET = 'http://127.0.0.1:8000';

function normalizeProxyTarget(raw) {
  const value = (raw ?? '').toString().trim();
  return value.endsWith('/') ? value.slice(0, -1) : value;
}

export function parseDockerPublishedPort(raw) {
  const value = (raw ?? '').toString().trim().split(/\s+/)[0] || '';
  const idx = value.lastIndexOf(':');
  if (idx <= 0 || idx === value.length - 1) {
    return '';
  }
  let host = value.slice(0, idx);
  const port = value.slice(idx + 1);
  if (!/^[0-9]+$/.test(port)) {
    return '';
  }
  if (host === '0.0.0.0' || host === '::' || host === '[::]') {
    host = '127.0.0.1';
  }
  if (host.startsWith('[') && host.endsWith(']')) {
    host = host.slice(1, -1);
  }
  if (!host) {
    return '';
  }
  if (host.includes(':')) {
    host = `[${host}]`;
  }
  return `http://${host}:${port}`;
}

export function discoverLocalTestnetApiProxyTarget({ execFile = execFileSync } = {}) {
  let listing;
  try {
    listing = execFile(
      'docker',
      [
        'ps',
        '--filter',
        'label=com.docker.compose.service=zenodex-nginx',
        '--format',
        '{{.Names}}\t{{.Label "com.docker.compose.project"}}',
      ],
      { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] },
    );
  } catch {
    return '';
  }

  const candidates = String(listing || '')
    .split('\n')
    .map((line) => {
      const [name, project] = line.split('\t');
      return { name: (name || '').trim(), project: (project || '').trim() };
    })
    .filter(({ name, project }) => name && project.startsWith('zenodex-local-testnet-'));

  for (const { name } of candidates) {
    try {
      const published = execFile(
        'docker',
        ['port', name, '8080/tcp'],
        { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] },
      );
      const target = parseDockerPublishedPort(published);
      if (target) {
        return target;
      }
    } catch {
      // Try the next running local-testnet nginx container.
    }
  }
  return '';
}

export function resolveApiProxyTarget({ command, env = process.env, execFile = execFileSync } = {}) {
  if (Object.prototype.hasOwnProperty.call(env, 'API_PROXY_TARGET')) {
    return normalizeProxyTarget(env.API_PROXY_TARGET);
  }
  const allowLocalTestnetDiscovery = env.API_PROXY_ALLOW_LOCAL_TESTNET_DISCOVERY === '1';
  if (command === 'serve' && allowLocalTestnetDiscovery) {
    const localTestnetTarget = discoverLocalTestnetApiProxyTarget({ execFile });
    if (localTestnetTarget) {
      return localTestnetTarget;
    }
  }
  return DEFAULT_API_PROXY_TARGET;
}

// Paths that the production nginx local-testnet template routes to the
// ZenoLedger writer (node) instead of the stdlib api_server. Mirrors
// .docker/nginx.local-testnet.conf.template so local dev matches prod.
const NODE_API_PATHS = [
  '/api/pools',
  '/api/swap',
  '/api/liquidity/add',
  '/api/liquidity/create',
  '/api/liquidity/remove',
  '/api/testnet/faucet',
  '/api/tokenomics/status',
  '/api/tokenomics/active-participant/claim',
  '/tx',
  '/status',
  '/features',
  '/tokens',
  '/network',
  '/public_network_config.json',
  '/ledger-bundle/',
  '/live',
];

function buildProxyConfig(stdlibTarget, nodeTarget) {
  if (!stdlibTarget && !nodeTarget) return undefined;
  // Single-target fast path: everything to one origin.
  if (stdlibTarget && !nodeTarget) {
    return { '/api': { target: stdlibTarget, changeOrigin: true } };
  }
  if (!stdlibTarget && nodeTarget) {
    return { '/api': { target: nodeTarget, changeOrigin: true } };
  }
  // Split routing: node paths first (longest-match wins in Vite proxy),
  // then the catch-all /api -> stdlib api_server. Mirrors nginx ordering.
  const proxy = {};
  for (const p of NODE_API_PATHS) {
    proxy[p] = { target: nodeTarget, changeOrigin: true };
  }
  proxy['/api'] = { target: stdlibTarget, changeOrigin: true };
  return proxy;
}

export default defineConfig(({ command }) => {
  const apiTarget = resolveApiProxyTarget({ command });
  const previewApiTarget = normalizeProxyTarget(process.env.API_PROXY_TARGET);
  const nodeApiTarget = normalizeProxyTarget(process.env.NODE_API_PROXY_TARGET || '');
  const basePathRaw = (process.env.VITE_BASE_PATH || '/').toString().trim();
  const basePath = basePathRaw || '/';
  return {
    plugins: [react()],
    base: basePath,
    build: {
      rollupOptions: {
        output: {
          // Split heavy, rarely-changing vendor deps into their own long-cached
          // chunks so app edits don't bust them and the React runtime loads
          // separately from the noble crypto primitives.
          manualChunks(id) {
            if (!id.includes('node_modules')) return undefined;
            if (id.includes('react-dom') || id.includes('/react/') || id.includes('scheduler')) return 'vendor-react';
            if (id.includes('@noble') || id.includes('@scure')) return 'vendor-crypto';
            return undefined;
          },
        },
      },
    },
    server: {
      proxy: buildProxyConfig(apiTarget, nodeApiTarget),
    },
    preview: {
      proxy: buildProxyConfig(previewApiTarget, nodeApiTarget),
    },
  };
})
