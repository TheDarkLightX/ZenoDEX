// Copyright DarkLightX/Dana Edwards
// Tab state hook — URL-routable via ?proofsTab=claim|checkpoint|api

import { useEffect, useState } from 'react';

const VALID_TABS = ['claim', 'checkpoint', 'api'];
const DEFAULT_TAB = 'claim';

function getTabFromUrl() {
  if (typeof window === 'undefined') return DEFAULT_TAB;
  const params = new URLSearchParams(window.location.search);
  const requested = params.get('proofsTab');
  return VALID_TABS.includes(requested) ? requested : DEFAULT_TAB;
}

function setTabInUrl(tab) {
  if (typeof window === 'undefined') return;
  const url = new URL(window.location.href);
  url.searchParams.set('proofsTab', tab);
  window.history.replaceState({}, '', url.toString());
}

export function useProofsTab() {
  const [tab, setTab] = useState(getTabFromUrl);

  useEffect(() => {
    setTabInUrl(tab);
  }, [tab]);

  return [tab, setTab];
}
