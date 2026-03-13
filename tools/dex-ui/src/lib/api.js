const DEFAULT_API_BASE = "";
const DEFAULT_TIMEOUT_MS = 15_000;

function getRuntimeConfig() {
  if (typeof window === "undefined") {
    return {};
  }
  const cfg = window.__ZENODEX_CONFIG__;
  return cfg && typeof cfg === "object" ? cfg : {};
}

function normalizeApiBase(raw) {
  const value = (raw ?? "").toString().trim();
  if (!value) {
    return "";
  }
  return value.endsWith("/") ? value.slice(0, -1) : value;
}

export function getApiBase() {
  const runtimeBase = normalizeApiBase(getRuntimeConfig().apiBase);
  if (runtimeBase) {
    return runtimeBase;
  }
  const envBase = normalizeApiBase(import.meta?.env?.VITE_API_BASE ?? "");
  return envBase || DEFAULT_API_BASE;
}

export function getApiToken() {
  const value = (import.meta?.env?.VITE_API_TOKEN ?? "").toString().trim();
  return value || "";
}

export async function apiFetchJson(path, options = {}) {
  const base = getApiBase();
  const url = `${base}${path}`;
  const token = getApiToken();
  const { timeoutMs, ...fetchOptions } = options || {};
  const method = (fetchOptions.method || "GET").toString().toUpperCase();
  const headers = {
    Accept: "application/json",
    ...(fetchOptions.headers || {}),
  };
  const hasHeader = (name) => Object.keys(headers).some((key) => key.toLowerCase() === name);
  const hasBody = fetchOptions.body !== undefined && fetchOptions.body !== null;
  if (hasBody && !hasHeader("content-type")) {
    headers["Content-Type"] = "application/json";
  }
  if (token && !hasHeader("authorization")) {
    headers.Authorization = `Bearer ${token}`;
  }

  const effectiveTimeoutMs = Number.isFinite(timeoutMs) && timeoutMs > 0 ? Math.trunc(timeoutMs) : DEFAULT_TIMEOUT_MS;
  const controller = fetchOptions.signal ? null : new AbortController();
  const signal = fetchOptions.signal || controller?.signal;
  const timer = controller ? setTimeout(() => controller.abort(), effectiveTimeoutMs) : null;

  let response;
  try {
    response = await fetch(url, {
      ...fetchOptions,
      method,
      headers: {
        ...headers,
      },
      signal,
    });
  } catch (err) {
    if (timer) {
      clearTimeout(timer);
    }
    const name = err && typeof err === "object" ? err.name : "";
    if (name === "AbortError") {
      throw new Error("timeout");
    }
    throw err;
  } finally {
    if (timer) {
      clearTimeout(timer);
    }
  }

  const text = await response.text();
  let data;
  try {
    data = text ? JSON.parse(text) : null;
  } catch {
    data = null;
  }

  if (!response.ok) {
    const message = (data && (data.error || data.message)) || `http_${response.status}`;
    throw new Error(message);
  }
  return data;
}

export function apiGetConfidentialStatus(options = {}) {
  return apiFetchJson("/api/confidential/status", { method: "GET", ...(options || {}) });
}
