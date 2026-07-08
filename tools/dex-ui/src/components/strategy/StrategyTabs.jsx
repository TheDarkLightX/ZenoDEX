// Copyright DarkLightX/Dana Edwards
// Task tabs — Strategies, Safety, Developer

const TABS = [
  { id: 'strategies', label: 'Strategies' },
  { id: 'safety', label: 'Safety' },
  { id: 'developer', label: 'Developer' },
];

export default function StrategyTabs({ activeTab, onTabChange }) {
  return (
    <nav className="strategy-task-tabs" role="tablist" aria-label="Strategy task tabs">
      {TABS.map((tab) => (
        <button
          key={tab.id}
          className={`strategy-task-tab ${activeTab === tab.id ? 'active' : ''}`}
          type="button"
          role="tab"
          aria-selected={activeTab === tab.id}
          onClick={() => onTabChange(tab.id)}
        >
          {tab.label}
        </button>
      ))}
    </nav>
  );
}
