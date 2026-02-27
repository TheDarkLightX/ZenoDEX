import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import './index.css'
import App from './App.jsx'
import ErrorBoundary from './components/ErrorBoundary.jsx'
import { TransactionCenterProvider } from './lib/TransactionCenterContext.jsx'

createRoot(document.getElementById('root')).render(
  <StrictMode>
    <ErrorBoundary>
      <TransactionCenterProvider>
        <App />
      </TransactionCenterProvider>
    </ErrorBoundary>
  </StrictMode>,
)
