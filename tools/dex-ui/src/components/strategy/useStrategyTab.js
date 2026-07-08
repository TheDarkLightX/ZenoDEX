// Copyright DarkLightX/Dana Edwards
// Tab state hook — URL-routable via ?strategyTab=strategies|safety|developer

import { useEffect, useState } from 'react';

const VALID_TABS = ['strategies', 'safety', 'developer'];
const DEFAULT_TAB = 'strategies';

function getTabFromUrl() {
  if (typeof window === 'undefined') return DEFAULT_TAB;
  const params = new URLSearchParams(window.location.search);
  const requested = params.get('strategyTab');
  return VALID_TABS.includes(requested) ? requested : DEFAULT_TAB;
}

function setTabInUrl(tab) {
  if (typeof window === 'undefined') return;
  const url = new URL(window.location.href);
  url.searchParams.set('strategyTab', tab);
  window.history.replaceState({}, '', url.toString());
}

export function useStrategyTab() {
  const [tab, setTab] = useState(getTabFromUrl);

  useEffect(() => {
    setTabInUrl(tab);
  }, [tab]);

  return [tab, setTab];
}
