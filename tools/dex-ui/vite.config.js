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
  if (command !== 'build') {
    const localTestnetTarget = discoverLocalTestnetApiProxyTarget({ execFile });
    if (localTestnetTarget) {
      return localTestnetTarget;
    }
  }
  return DEFAULT_API_PROXY_TARGET;
}

export default defineConfig(({ command }) => {
  const apiTarget = resolveApiProxyTarget({ command });
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
      proxy: apiTarget ? {
        '/api': {
          target: apiTarget,
          changeOrigin: true,
        },
      } : undefined,
    },
    preview: {
      proxy: apiTarget ? {
        '/api': {
          target: apiTarget,
          changeOrigin: true,
        },
      } : undefined,
    },
  };
})
