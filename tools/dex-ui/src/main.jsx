import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import "./index.css";
import App from "./App.jsx";

async function loadRuntimeConfig() {
  const base = (import.meta?.env?.BASE_URL || "/").toString();
  const configUrl = `${base}zenodex-config.json`;
  try {
    const res = await fetch(configUrl, { cache: "no-store" });
    if (!res.ok) {
      return;
    }
    const data = await res.json();
    if (data && typeof data === "object") {
      window.__ZENODEX_CONFIG__ = data;
    }
  } catch {
    // Fail closed to built-in defaults when the runtime config file is absent.
  }
}

async function bootstrap() {
  await loadRuntimeConfig();
  createRoot(document.getElementById("root")).render(
    <StrictMode>
      <App />
    </StrictMode>,
  );
}

bootstrap();
