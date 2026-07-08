// Copyright DarkLightX/Dana Edwards
// Admin tab — sub-tabs: Feeds / Reporters / Authority
// Power-user configuration. Authority collapsed by default (progressive disclosure).

import { useState } from 'react';
import { FeedCreationPanel, FeedStatusPanel } from './FeedPanels.jsx';
import { ReporterPanel, ReporterOnboardingPanel } from './ReporterPanels.jsx';
import { RewardsPanel, SourceDiversityPanel, ConsumerProfilePanel } from './RewardPanels.jsx';
import { AuthorityProfilePanel, AuthorityExercisePanel } from './AuthorityPanels.jsx';

const SUB_TABS = [
  { id: 'feeds', label: 'Feeds' },
  { id: 'reporters', label: 'Reporters' },
  { id: 'authority', label: 'Security' },
];

const AUTH_COLLAPSE_KEY = 'zenodex.oracle.authorityCollapsed';

export default function AdminTab({
  feeds = [],
  selectedFeed = null,
  reporters = [],
  rewards = [],
  sources = [],
  authorityStatus = null,
  authorityExerciseResult = null,
  authorityExerciseState = '',
  authorityExerciseBusy = false,
  onRunAuthorityExercise = () => {},
  onCreateFeed = () => {},
}) {
  const [subTab, setSubTab] = useState('feeds');
  const [authorityCollapsed, setAuthorityCollapsed] = useState(() => {
    if (typeof window === 'undefined') return true;
    return window.localStorage.getItem(AUTH_COLLAPSE_KEY) !== 'false';
  });

  const toggleAuthority = () => {
    const next = !authorityCollapsed;
    setAuthorityCollapsed(next);
    if (typeof window !== 'undefined') {
      window.localStorage.setItem(AUTH_COLLAPSE_KEY, String(next));
    }
  };

  return (
    <div className="oracle-tab-panel">
      {/* Sub-tabs */}
      <div className="oracle-admin-subtabs">
        {SUB_TABS.map((st) => (
          <button
            key={st.id}
            className={`oracle-admin-subtab ${subTab === st.id ? 'active' : ''}`}
            type="button"
            onClick={() => setSubTab(st.id)}
          >
            {st.label}
          </button>
        ))}
      </div>

      {/* Feeds sub-tab */}
      {subTab === 'feeds' && (
        <div>
          <div style={{ marginBottom: 12 }}>
            <button className="btn btn-primary" type="button" onClick={onCreateFeed}>
              + New feed
            </button>
          </div>
          {feeds.length > 0 && (
            <div className="oracle-feed-table" style={{ marginBottom: 16 }}>
              <div className="oracle-feed-table-head">
                <span>Feed</span>
                <span>Price</span>
                <span>Evidence</span>
                <span>Status</span>
                <span>Freshness</span>
              </div>
              {feeds.map((feed) => (
                <div key={feed.id} className="oracle-feed-row">
                  <span>{feed.feed}</span>
                  <span>{feed.value}{feed.unit ? ` ${feed.unit}` : ''}</span>
                  <span style={{ opacity: 0.6 }}>{feed.evidenceClass || '—'}</span>
                  <span className={`oracle-feed-status ${feed.status === 'fresh' ? 'live' : feed.status === 'stale' ? 'stale' : 'down'}`}>
                    <span className="dot" aria-hidden="true"></span>
                    {feed.status === 'fresh' ? 'live' : feed.status}
                  </span>
                  <span style={{ opacity: 0.5 }}>{feed.freshness || '—'}</span>
                </div>
              ))}
            </div>
          )}
          <FeedCreationPanel />
          {selectedFeed && <FeedStatusPanel feed={selectedFeed} />}
          <SourceDiversityPanel sources={sources} />
          <ConsumerProfilePanel />
        </div>
      )}

      {/* Reporters sub-tab */}
      {subTab === 'reporters' && (
        <div>
          <ReporterPanel reporters={reporters} />
          <RewardsPanel rewards={rewards} />
          <ReporterOnboardingPanel selectedFeed={selectedFeed} />
        </div>
      )}

      {/* Authority sub-tab (collapsed by default, persisted) */}
      {subTab === 'authority' && (
        <div>
          <div
            className="oracle-collapsible-toggle"
            onClick={toggleAuthority}
            role="button"
            tabIndex={0}
            aria-expanded={!authorityCollapsed}
            onKeyDown={(e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); toggleAuthority(); } }}
          >
            <span>{authorityCollapsed ? '▶' : '▼'}</span>
            <span>Security Settings</span>
          </div>
          {!authorityCollapsed && (
            <div className="oracle-collapsible-body">
              <AuthorityProfilePanel authorityStatus={authorityStatus} />
              <AuthorityExercisePanel
                authorityStatus={authorityStatus}
                authorityExerciseResult={authorityExerciseResult}
                authorityExerciseState={authorityExerciseState}
                authorityExerciseBusy={authorityExerciseBusy}
                onRunAuthorityExercise={onRunAuthorityExercise}
              />
            </div>
          )}
        </div>
      )}
    </div>
  );
}
