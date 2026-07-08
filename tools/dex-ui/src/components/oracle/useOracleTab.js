// Copyright DarkLightX/Dana Edwards
// Tab state hook — URL-routable via ?oracleTab=monitor|resolve|admin

import { useEffect, useState } from 'react';

const VALID_TABS = ['monitor', 'resolve', 'admin'];
const DEFAULT_TAB = 'monitor';

function getTabFromUrl() {
  if (typeof window === 'undefined') return DEFAULT_TAB;
  const params = new URLSearchParams(window.location.search);
  const requested = params.get('oracleTab');
  return VALID_TABS.includes(requested) ? requested : DEFAULT_TAB;
}

function setTabInUrl(tab) {
  if (typeof window === 'undefined') return;
  const url = new URL(window.location.href);
  url.searchParams.set('oracleTab', tab);
  window.history.replaceState({}, '', url.toString());
}

export function useOracleTab() {
  const [tab, setTab] = useState(getTabFromUrl);

  useEffect(() => {
    setTabInUrl(tab);
  }, [tab]);

  return [tab, setTab];
}

export { VALID_TABS, DEFAULT_TAB };
