// Copyright DarkLightX/Dana Edwards
// Task tabs — Monitor, Resolve, Admin

const TABS = [
  { id: 'monitor', label: 'Monitor' },
  { id: 'resolve', label: 'Resolve' },
  { id: 'admin', label: 'Admin' },
];

export default function OracleTabs({ activeTab, onTabChange }) {
  return (
    <nav className="oracle-task-tabs" role="tablist" aria-label="Oracle task tabs">
      {TABS.map((tab) => (
        <button
          key={tab.id}
          className={`oracle-task-tab ${activeTab === tab.id ? 'active' : ''}`}
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
