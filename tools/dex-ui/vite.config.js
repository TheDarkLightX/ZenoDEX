import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'

// https://vite.dev/config/
export default defineConfig(() => {
  const apiTarget = (process.env.API_PROXY_TARGET || 'http://127.0.0.1:8000').toString().trim();
  const writerTarget = (process.env.LEDGER_WRITER_TARGET || 'http://127.0.0.1:8787').toString().trim();
  const forwarderTarget = (process.env.LEDGER_FORWARDER_TARGET || 'http://127.0.0.1:8788').toString().trim();
  const readonlyTarget = (process.env.LEDGER_READONLY_TARGET || 'http://127.0.0.1:8789').toString().trim();
  const basePathRaw = (process.env.VITE_BASE_PATH || '/').toString().trim();
  const basePath = basePathRaw || '/';
  const proxy = {};
  if (apiTarget) {
    proxy['/api'] = {
      target: apiTarget,
      changeOrigin: true,
    };
  }
  if (writerTarget) {
    proxy['/ledger/writer'] = {
      target: writerTarget,
      changeOrigin: true,
      rewrite: (path) => path.replace(/^\/ledger\/writer/, ''),
    };
  }
  if (forwarderTarget) {
    proxy['/ledger/forwarder'] = {
      target: forwarderTarget,
      changeOrigin: true,
      rewrite: (path) => path.replace(/^\/ledger\/forwarder/, ''),
    };
  }
  if (readonlyTarget) {
    proxy['/ledger/readonly'] = {
      target: readonlyTarget,
      changeOrigin: true,
      rewrite: (path) => path.replace(/^\/ledger\/readonly/, ''),
    };
  }
  return {
    plugins: [react()],
    base: basePath,
    server: {
      proxy: Object.keys(proxy).length > 0 ? proxy : undefined,
    },
  };
})
