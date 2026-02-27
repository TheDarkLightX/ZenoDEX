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

    render() {
        if (this.state.hasError) {
            return (
                <div className="error-boundary">
                    <div className="error-content">
                        <span className="error-icon">⚠️</span>
                        <h2>Something went wrong</h2>
                        <p>An unexpected error occurred. Please try refreshing the page.</p>
                        <button
                            className="btn btn-primary"
                            onClick={() => window.location.reload()}
                        >
                            Refresh Page
                        </button>
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
