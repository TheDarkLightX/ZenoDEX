import { Component } from 'react';
import './ErrorBoundary.css';

/**
 * ErrorBoundary - Catch React errors and display fallback UI
 * Prevents the entire app from crashing on component errors
 */
class ErrorBoundary extends Component {
    constructor(props) {
        super(props);
        this.state = { hasError: false, error: null };
    }

    static getDerivedStateFromError(error) {
        return { hasError: true, error };
    }

    componentDidCatch(error, errorInfo) {
        console.error('ErrorBoundary caught an error:', error, errorInfo);
    }

    handleRetry = () => {
        // Reset error state to re-render children without full page reload
        this.setState({ hasError: false, error: null });
    };

    handleGoHome = () => {
        if (typeof window !== 'undefined') {
            const url = new URL(window.location.href);
            url.searchParams.delete('tab');
            window.location.href = url.toString();
        }
    };

    handleCopyError = () => {
        if (typeof navigator !== 'undefined' && navigator.clipboard) {
            const text = `${this.state.error?.toString()}\n\nStack:\n${this.state.error?.stack || '(no stack)'}`;
            navigator.clipboard.writeText(text).catch(() => {});
        }
    };

    render() {
        if (this.state.hasError) {
            return (
                <div className="error-boundary" role="alert" aria-live="assertive">
                    <div className="error-content">
                        <svg className="error-icon-svg" width="40" height="40" viewBox="0 0 40 40" fill="none" aria-hidden="true">
                            <path d="M20 4 L36 32 L4 32 Z" stroke="currentColor" strokeWidth="2" fill="none" strokeLinejoin="round" />
                            <path d="M20 16 L20 24" stroke="currentColor" strokeWidth="2" strokeLinecap="round" />
                            <circle cx="20" cy="28" r="1.5" fill="currentColor" />
                        </svg>
                        <h2>Something went wrong</h2>
                        <p>An unexpected error occurred in this panel. Other tabs are unaffected.</p>
                        <div className="error-actions">
                            <button
                                className="btn btn-primary"
                                onClick={this.handleRetry}
                                type="button"
                            >
                                Try Again
                            </button>
                            <button
                                className="btn btn-secondary"
                                onClick={this.handleGoHome}
                                type="button"
                            >
                                Go to Swap
                            </button>
                            <button
                                className="btn btn-ghost"
                                onClick={this.handleCopyError}
                                type="button"
                                aria-label="Copy error details to clipboard"
                            >
                                Copy Error
                            </button>
                        </div>
                        <details className="error-details">
                            <summary>Error details</summary>
                            <pre>{this.state.error?.toString()}</pre>
                        </details>
                    </div>
                </div>
            );
        }

        return this.props.children;
    }
}

export default ErrorBoundary;
