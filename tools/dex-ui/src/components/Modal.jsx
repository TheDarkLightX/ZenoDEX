import { useCallback, useEffect, useId, useRef } from 'react';
import { createPortal } from 'react-dom';
import './Modal.css';

const modalStack = [];

function registerModal(modalId) {
  modalStack.push(modalId);
  document.body.classList.add('modal-open');
}

function unregisterModal(modalId) {
  const idx = modalStack.lastIndexOf(modalId);
  if (idx !== -1) {
    modalStack.splice(idx, 1);
  }
  if (modalStack.length === 0) {
    document.body.classList.remove('modal-open');
  }
}

function isTopModal(modalId) {
  return modalStack[modalStack.length - 1] === modalId;
}

/**
 * Modal — accessible dialog primitive. Renders into document.body via
 * portal so it escapes whatever overflow:hidden parent it lives under.
 *
 * Props:
 *   open       — bool. When false, returns null (does not render).
 *   onClose    — () => void. Called on ESC, backdrop click, or close-X.
 *   title      — string. Rendered as <h2 id="modal-title-N"> and used
 *                for aria-labelledby on the dialog.
 *   description — optional string, rendered below the title as <p>.
 *   size       — "sm" | "md" (default) | "lg". Caps the modal width.
 *   children   — modal body. Rendered inside a scrollable container.
 *
 * Behavior:
 *   - ESC key closes (capture phase so it beats inner inputs).
 *   - Click on backdrop closes; click inside the modal does not.
 *   - Focus moves to the first focusable inside on open; returns to
 *     the trigger element on close.
 *   - Body scroll is locked while open (added `modal-open` class
 *     to <body>).
 *   - role="dialog" aria-modal="true" aria-labelledby wired.
 */

function Modal({ open, onClose, title, description, size = 'md', children }) {
  const overlayRef = useRef(null);
  const dialogRef = useRef(null);
  const previouslyFocused = useRef(null);
  const modalIdRef = useRef(Symbol('modal'));
  const titleId = useId();

  const handleClose = useCallback(() => {
    onClose?.();
  }, [onClose]);

  // ESC to close + body scroll lock + focus trap.
  useEffect(() => {
    if (!open) return undefined;

    const modalId = modalIdRef.current;
    previouslyFocused.current = document.activeElement;
    registerModal(modalId);

    const FOCUSABLE_SELECTOR =
      'a[href], button:not([disabled]), input:not([disabled]), textarea:not([disabled]), select:not([disabled]), [tabindex]:not([tabindex="-1"])';

    function focusableElements() {
      const dialog = dialogRef.current;
      if (!dialog) return [];
      return Array.from(dialog.querySelectorAll(FOCUSABLE_SELECTOR))
        .filter((el) => !el.hasAttribute('disabled') && el.tabIndex !== -1);
    }

    // Defer initial focus until the portal subtree mounts.
    const focusTimer = window.setTimeout(() => {
      const els = focusableElements();
      (els[0] || dialogRef.current)?.focus();
    }, 0);

    function onKeyDown(event) {
      if (!isTopModal(modalId)) {
        return;
      }
      if (event.key === 'Escape') {
        event.preventDefault();
        event.stopPropagation();
        if (typeof event.stopImmediatePropagation === 'function') {
          event.stopImmediatePropagation();
        }
        handleClose();
        return;
      }
      if (event.key === 'Tab') {
        // Focus trap: when Tab would leave the dialog, wrap to the
        // other end. Cannot escape until the modal closes.
        const els = focusableElements();
        if (els.length === 0) {
          // Nothing focusable inside; keep focus on the dialog itself.
          event.preventDefault();
          dialogRef.current?.focus();
          return;
        }
        const first = els[0];
        const last = els[els.length - 1];
        const active = document.activeElement;
        if (event.shiftKey && (active === first || !dialogRef.current?.contains(active))) {
          event.preventDefault();
          last.focus();
        } else if (!event.shiftKey && (active === last || !dialogRef.current?.contains(active))) {
          event.preventDefault();
          first.focus();
        }
      }
    }
    document.addEventListener('keydown', onKeyDown, true);

    return () => {
      document.removeEventListener('keydown', onKeyDown, true);
      unregisterModal(modalId);
      window.clearTimeout(focusTimer);
      const prev = previouslyFocused.current;
      if (prev && typeof prev.focus === 'function') {
        prev.focus();
      }
    };
  }, [open, handleClose]);

  if (!open) return null;

  const onBackdropMouseDown = (event) => {
    // Only close if the click landed on the overlay itself, not bubbled
    // up from the dialog. mousedown (not click) avoids closing when a
    // drag begins inside and ends on the overlay.
    if (event.target === overlayRef.current && isTopModal(modalIdRef.current)) {
      handleClose();
    }
  };

  return createPortal(
    <div
      ref={overlayRef}
      className="modal-overlay"
      onMouseDown={onBackdropMouseDown}
    >
      <div
        ref={dialogRef}
        className={`modal-dialog modal-dialog-${size}`}
        role="dialog"
        aria-modal="true"
        aria-labelledby={titleId}
        tabIndex={-1}
      >
        <header className="modal-header">
          <div className="modal-titles">
            <h2 id={titleId} className="modal-title">{title}</h2>
            {description && <p className="modal-description">{description}</p>}
          </div>
          <button
            type="button"
            className="modal-close"
            onClick={handleClose}
            aria-label="Close"
            title="Close (ESC)"
          >
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none"
              stroke="currentColor" strokeWidth="2" strokeLinecap="round"
              strokeLinejoin="round" aria-hidden="true">
              <path d="M18 6 6 18M6 6l12 12" />
            </svg>
          </button>
        </header>
        <div className="modal-body">{children}</div>
      </div>
    </div>,
    document.body,
  );
}

export default Modal;
