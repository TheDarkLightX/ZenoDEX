// Copyright DarkLightX/Dana Edwards
// Task tabs — URL-routable via ?proofsTab=claim|checkpoint|api

const VALID_TABS = ['claim', 'checkpoint', 'api'];

export default function ProofsTabs({ activeTab, onTabChange }) {
  return (
    <div className="proofs-task-tabs" role="tablist" aria-label="Proof tasks">
      {VALID_TABS.map((tabId) => (
        <button
          key={tabId}
          className={`proofs-task-tab ${activeTab === tabId ? 'active' : ''}`}
          role="tab"
          aria-selected={activeTab === tabId}
          type="button"
          onClick={() => onTabChange(tabId)}
        >
          {tabId === 'claim' ? 'Claim reward' : tabId === 'checkpoint' ? 'Verify checkpoint' : 'API reference'}
        </button>
      ))}
    </div>
  );
}
