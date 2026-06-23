"""
Grammar Loader - Loads and uses tau.tgf for validation.

The user must provide their own tau.tgf file (obtained from tau-lang repo).
This module does NOT include or distribute any Tau Language files.
"""

import os
import subprocess
from pathlib import Path
from typing import Optional, Tuple


class GrammarLoader:
    """
    Loads tau.tgf grammar for output validation.

    Usage:
        loader = GrammarLoader(tgf_path="/path/to/tau.tgf")
        if loader.available:
            valid, errors = loader.validate(tau_code)
    """

    def __init__(self, tgf_path: Optional[str] = None, tau_binary: Optional[str] = None):
        """
        Initialize grammar loader.

        Args:
            tgf_path: Path to tau.tgf file. If None, searches common locations.
            tau_binary: Path to tau binary. If None, searches PATH and common locations.
        """
        self.tgf_path = self._find_tgf(tgf_path)
        self.tau_binary = self._find_tau_binary(tau_binary)
        self.available = self.tau_binary is not None

    def _find_tgf(self, provided: Optional[str]) -> Optional[Path]:
        """Find tau.tgf file."""
        if provided and Path(provided).exists():
            return Path(provided)

        # Search common locations relative to this file
        search_paths = [
            # Relative to project root
            Path(__file__).parent.parent.parent / "external/tau-lang/parser/tau.tgf",
            # Environment variable
            Path(os.environ.get("TAU_TGF_PATH", "")) if os.environ.get("TAU_TGF_PATH") else None,
        ]

        for path in search_paths:
            if path and path.exists():
                return path

        return None

    def _find_tau_binary(self, provided: Optional[str]) -> Optional[Path]:
        """Find tau binary."""
        if provided and Path(provided).exists():
            return Path(provided)

        # Try to find in PATH
        try:
            result = subprocess.run(["which", "tau"], capture_output=True, text=True)
            if result.returncode == 0:
                return Path(result.stdout.strip())
        except Exception:
            pass

        # Search common locations
        search_paths = [
            Path(__file__).parent.parent.parent / "external/tau-lang/build-Release/tau",
            Path(os.environ.get("TAU_BINARY_PATH", "")) if os.environ.get("TAU_BINARY_PATH") else None,
        ]

        for path in search_paths:
            if path and path.exists():
                return path

        return None

    def validate(self, tau_code: str) -> Tuple[bool, str]:
        """
        Validate Tau code against the grammar.

        Args:
            tau_code: Generated Tau code to validate.

        Returns:
            Tuple of (is_valid, error_message).
            If tau binary not available, returns (False, "Tau binary not found").
        """
        if not self.available:
            return False, "Tau binary not found. Set TAU_BINARY_PATH or build tau-lang."

        if not self.tgf_path:
            return False, "tau.tgf not found. Set TAU_TGF_PATH."

        # Write code to temp file
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.tau', delete=False) as f:
            f.write(tau_code)
            temp_path = f.name

        try:
            # Run tau to validate syntax
            result = subprocess.run(
                [str(self.tau_binary), temp_path],
                capture_output=True,
                text=True,
                timeout=10
            )

            if result.returncode == 0:
                return True, ""
            else:
                return False, result.stderr or result.stdout or "Unknown error"

        except subprocess.TimeoutExpired:
            return False, "Validation timed out"
        except Exception as e:
            return False, str(e)
        finally:
            os.unlink(temp_path)

    def get_status(self) -> str:
        """Get status message about grammar availability."""
        lines = []

        if self.tgf_path:
            lines.append(f"Grammar: {self.tgf_path}")
        else:
            lines.append("Grammar: NOT FOUND")
            lines.append("  Set TAU_TGF_PATH or place tau.tgf in external/tau-lang/parser/")

        if self.tau_binary:
            lines.append(f"Tau binary: {self.tau_binary}")
        else:
            lines.append("Tau binary: NOT FOUND")
            lines.append("  Set TAU_BINARY_PATH or build tau-lang")

        if self.available:
            lines.append("Validation: AVAILABLE")
        else:
            lines.append("Validation: UNAVAILABLE (output will be best-effort)")

        return "\n".join(lines)
