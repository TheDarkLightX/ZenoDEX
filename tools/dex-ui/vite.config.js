import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'

// https://vite.dev/config/
export default defineConfig(() => {
  const apiTarget = (process.env.API_PROXY_TARGET || 'http://127.0.0.1:8000').toString().trim();
  return {
    plugins: [react()],
    server: {
      proxy: apiTarget ? {
        '/api': {
          target: apiTarget,
          changeOrigin: true,
        },
      } : undefined,
    },
  };
})
