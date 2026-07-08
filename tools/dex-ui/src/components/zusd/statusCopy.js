export function formatZusdStatusIssue(statusError) {
  const raw = String(statusError || '').trim();
  if (!raw) {
    return '';
  }
  const lower = raw.toLowerCase();
  if (
    lower.includes('http_500')
    || lower.includes('failed to fetch')
    || lower.includes('fetch failed')
    || lower.includes('connection refused')
    || lower.includes('err_connection_refused')
    || lower.includes('status_unavailable')
  ) {
    return 'Local testnet is unavailable. Start or reconnect the local node, then retry.';
  }
  if (lower.includes('not_found') || lower.includes('wallet service unavailable')) {
    return 'zUSD wallet service is unavailable on this local node.';
  }
  return 'Status is unavailable. Retry after the local node is reachable.';
}
