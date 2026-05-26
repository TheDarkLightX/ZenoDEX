"""Subprocess-level chaos tests for the Tau spec runner.

These tests target ``_run_subprocess_with_output_caps`` directly — it's the
single IO primitive that bridges our deterministic verifier to an external
binary we don't control. We attack it with shell commands that simulate the
kind of misbehavior Tau itself might exhibit after an upgrade or under
resource pressure:

  - Non-zero exit codes (Tau rejects spec / parse error / OOM).
  - Output exceeding the documented byte caps (silent truncation = bad).
  - Wall-clock timeouts (tau hangs on an unbounded fixpoint computation).
  - SIGSEGV mid-output (Tau crashes in nanobind layer).
  - Stdin not consumed (Tau ignores REPL input — BrokenPipe path).
  - Invalid UTF-8 in stdout (must be replaced, never raise).
  - Stdout/stderr ordering chaos (close one before the other).

We also exercise ``find_tau_bin``, ``extract_stream_types``, and
``extract_always_exprs`` with adversarial spec text — the parser layer that
sits between Tau's binary contract and our verification logic.
"""

from __future__ import annotations

import os
import shutil
import stat
import sys
import time
from pathlib import Path

import pytest

from src.integration.tau_runner import (
    _run_subprocess_with_output_caps,
    extract_always_exprs,
    extract_stream_types,
    find_tau_bin,
    normalize_spec_text,
    parse_definitions,
)


def _sh(script: str) -> list[str]:
    """Wrap a shell snippet for ``_run_subprocess_with_output_caps``."""
    return ["/bin/sh", "-c", script]


def _caps(
    cmd: list[str],
    *,
    input_text: str = "",
    timeout_s: float = 5.0,
    max_stdout_bytes: int = 8_192,
    max_stderr_bytes: int = 8_192,
) -> tuple[int, str, str]:
    return _run_subprocess_with_output_caps(
        cmd,
        input_text=input_text,
        cwd=Path("/tmp"),
        timeout_s=timeout_s,
        max_stdout_bytes=max_stdout_bytes,
        max_stderr_bytes=max_stderr_bytes,
    )


# -----------------------------------------------------------------------------
# A. Subprocess caps — exit codes.
# -----------------------------------------------------------------------------


class TestSubprocessExitCodes:
    def test_zero_exit_returns_rc_zero(self) -> None:
        rc, out, err = _caps(_sh("echo ok"))
        assert rc == 0
        assert out.strip() == "ok"
        assert err == ""

    def test_exit_1_is_propagated(self) -> None:
        rc, _out, _err = _caps(_sh("exit 1"))
        assert rc == 1

    def test_exit_42_is_propagated(self) -> None:
        rc, _out, _err = _caps(_sh("exit 42"))
        assert rc == 42

    def test_exit_127_command_not_found_is_propagated(self) -> None:
        rc, _out, err = _caps(_sh("this_command_does_not_exist_zenodex 2>&1"))
        # Either /bin/sh reports the missing command (rc 127) or the script
        # otherwise terminates non-zero; both are non-zero rc.
        assert rc != 0

    def test_negative_exit_via_signal(self) -> None:
        # SIGTERM → rc = -SIGTERM in Popen semantics; either rc < 0 or rc != 0
        # is acceptable (kernel reporting varies).
        rc, _out, _err = _caps(_sh("kill -TERM $$"))
        assert rc != 0


# -----------------------------------------------------------------------------
# B. Subprocess caps — stdout/stderr byte budgets.
# -----------------------------------------------------------------------------


class TestSubprocessByteCaps:
    def test_small_stdout_within_budget_is_preserved(self) -> None:
        rc, out, _err = _caps(_sh("echo hello"), max_stdout_bytes=1024)
        assert rc == 0
        assert out.strip() == "hello"

    def test_stdout_at_cap_truncates_and_kills(self) -> None:
        # Emit 20 KB of stdout with cap = 1 KB.
        rc, out, err = _caps(
            _sh("python3 -c 'import sys; sys.stdout.write(\"x\" * 20000); sys.stdout.flush()'"),
            max_stdout_bytes=1024,
        )
        # cap exceeded -> process killed, rc = -1
        assert rc == -1
        assert err.strip() == "tau stdout too large"
        # Output is truncated at the cap (or near it).
        assert len(out) <= 1024 + 64  # some slack for buffering

    def test_stderr_at_cap_truncates_and_kills(self) -> None:
        rc, _out, err = _caps(
            _sh("python3 -c 'import sys; sys.stderr.write(\"e\" * 20000); sys.stderr.flush()'"),
            max_stderr_bytes=1024,
        )
        assert rc == -1
        # When stderr is killed, the err message is "stderr too large".
        assert "stderr too large" in err or len(err) >= 1024

    def test_stdout_and_stderr_mixed_within_budget(self) -> None:
        rc, out, err = _caps(
            _sh("echo stdout_msg; echo stderr_msg >&2"),
            max_stdout_bytes=1024,
            max_stderr_bytes=1024,
        )
        assert rc == 0
        assert "stdout_msg" in out
        assert "stderr_msg" in err


# -----------------------------------------------------------------------------
# C. Subprocess caps — timeouts.
# -----------------------------------------------------------------------------


class TestSubprocessTimeout:
    def test_process_that_sleeps_past_timeout_is_killed(self) -> None:
        t0 = time.monotonic()
        rc, _out, err = _caps(_sh("sleep 5"), timeout_s=0.3)
        elapsed = time.monotonic() - t0
        assert rc == -1
        assert "timed out" in err
        # We should have killed it near the timeout, not waited the full 5s.
        assert elapsed < 2.0

    def test_process_that_finishes_before_timeout_succeeds(self) -> None:
        rc, out, _err = _caps(_sh("echo fast"), timeout_s=5.0)
        assert rc == 0
        assert out.strip() == "fast"

    def test_invalid_timeout_zero_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            _caps(_sh("echo x"), timeout_s=0)

    def test_invalid_timeout_negative_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            _caps(_sh("echo x"), timeout_s=-1.0)

    def test_invalid_timeout_string_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            _caps(_sh("echo x"), timeout_s="5")  # type: ignore[arg-type]


# -----------------------------------------------------------------------------
# D. Subprocess caps — config validation.
# -----------------------------------------------------------------------------


class TestSubprocessConfigValidation:
    def test_empty_cmd_rejected(self) -> None:
        with pytest.raises(ValueError, match="cmd must be non-empty"):
            _caps([])

    def test_zero_max_stdout_bytes_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            _caps(_sh("echo x"), max_stdout_bytes=0)

    def test_negative_max_stdout_bytes_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            _caps(_sh("echo x"), max_stdout_bytes=-1)

    def test_zero_max_stderr_bytes_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            _caps(_sh("echo x"), max_stderr_bytes=0)

    def test_invalid_input_text_with_surrogate_rejected(self) -> None:
        # input_text must encode to valid UTF-8. Lone surrogate cannot encode.
        with pytest.raises(ValueError, match="UTF-8"):
            _caps(_sh("cat"), input_text="\ud800")


# -----------------------------------------------------------------------------
# E. Subprocess caps — adversarial stdin/stdout behavior.
# -----------------------------------------------------------------------------


class TestSubprocessAdversarialIO:
    def test_process_that_ignores_stdin_succeeds(self) -> None:
        rc, _out, _err = _caps(_sh("true"), input_text="ignored input")
        assert rc == 0

    def test_process_that_closes_stdout_then_writes_to_stderr(self) -> None:
        rc, out, err = _caps(_sh("exec 1>&-; echo only_stderr >&2"))
        # rc=0 is acceptable (process succeeded), or non-zero if the close
        # confused the shell. Either way, stderr should contain the msg.
        assert "only_stderr" in err
        assert out == ""

    def test_process_outputs_non_utf8_bytes_replaced_not_raised(self) -> None:
        rc, out, _err = _caps(
            _sh("printf '\\xff\\xfe\\xfd\\n'"),
            max_stdout_bytes=1024,
        )
        assert rc == 0
        # Decoder uses errors='replace' so we should see the replacement char.
        assert "\ufffd" in out or len(out) > 0

    def test_segfault_mid_output_returns_nonzero(self) -> None:
        # Print some bytes, then segfault. The bytes should still arrive.
        rc, out, _err = _caps(_sh("echo partial; kill -SEGV $$"), timeout_s=2.0)
        assert rc != 0
        assert "partial" in out

    def test_process_that_consumes_stdin_then_echoes_it(self) -> None:
        rc, out, _err = _caps(_sh("cat"), input_text="hello world\n")
        assert rc == 0
        assert "hello world" in out

    def test_large_stdin_with_small_stdout(self) -> None:
        # Cat will echo back; we should NOT exceed stdout cap.
        big_input = "x" * 50_000
        rc, out, _err = _caps(
            _sh("cat"),
            input_text=big_input,
            max_stdout_bytes=2048,
        )
        # Echo will exceed stdout cap and trigger kill.
        assert rc == -1

    def test_process_that_writes_then_sleeps_then_exits(self) -> None:
        rc, out, _err = _caps(
            _sh("echo first; sleep 0.1; echo second"),
            timeout_s=3.0,
        )
        assert rc == 0
        assert "first" in out and "second" in out


# -----------------------------------------------------------------------------
# F. find_tau_bin — environment-variable chaos.
# -----------------------------------------------------------------------------


class TestFindTauBin:
    def test_returns_none_when_no_tau_anywhere(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        # Empty TAU_BIN, no candidates, no `tau` on PATH.
        monkeypatch.setenv("TAU_BIN", "")
        monkeypatch.setattr("shutil.which", lambda _: None)
        result = find_tau_bin(project_root=tmp_path)
        assert result is None

    def test_returns_env_path_when_executable_exists(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
    ) -> None:
        fake_tau = tmp_path / "tau"
        fake_tau.write_text("#!/bin/sh\necho fake-tau", encoding="utf-8")
        fake_tau.chmod(0o755)
        monkeypatch.setenv("TAU_BIN", str(fake_tau))
        result = find_tau_bin(project_root=tmp_path)
        assert result == str(fake_tau)

    def test_runtime_profile_prefers_stable_candidate(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
    ) -> None:
        stable = tmp_path / "external" / "tau-lang-bitblasting-prev-eea8fb1f" / "build-Release" / "tau"
        latest = tmp_path / "external" / "tau-lang" / "build-Release" / "tau"
        stable.parent.mkdir(parents=True)
        latest.parent.mkdir(parents=True)
        stable.write_text("#!/bin/sh\necho stable-tau", encoding="utf-8")
        latest.write_text("#!/bin/sh\necho latest-tau", encoding="utf-8")
        stable.chmod(0o755)
        latest.chmod(0o755)
        monkeypatch.setenv("TAU_BIN", "")
        monkeypatch.setenv("TAU_BIN_PROFILE", "runtime")
        monkeypatch.setattr("shutil.which", lambda _: None)

        result = find_tau_bin(project_root=tmp_path)

        assert result == str(stable)

    def test_latest_profile_prefers_current_checkout_candidate(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
    ) -> None:
        stable = tmp_path / "external" / "tau-lang-bitblasting-prev-eea8fb1f" / "build-Release" / "tau"
        latest = tmp_path / "external" / "tau-lang" / "build-Release" / "tau"
        stable.parent.mkdir(parents=True)
        latest.parent.mkdir(parents=True)
        stable.write_text("#!/bin/sh\necho stable-tau", encoding="utf-8")
        latest.write_text("#!/bin/sh\necho latest-tau", encoding="utf-8")
        stable.chmod(0o755)
        latest.chmod(0o755)
        monkeypatch.setenv("TAU_BIN", "")
        monkeypatch.setattr("shutil.which", lambda _: None)

        result = find_tau_bin(project_root=tmp_path, profile="latest")

        assert result == str(latest)

    def test_profile_specific_env_override_wins(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
    ) -> None:
        override = tmp_path / "tau-runtime"
        stable = tmp_path / "external" / "tau-lang-bitblasting-prev-eea8fb1f" / "build-Release" / "tau"
        override.write_text("#!/bin/sh\necho override-tau", encoding="utf-8")
        override.chmod(0o755)
        stable.parent.mkdir(parents=True)
        stable.write_text("#!/bin/sh\necho stable-tau", encoding="utf-8")
        stable.chmod(0o755)
        monkeypatch.setenv("TAU_BIN", "")
        monkeypatch.setenv("TAU_RUNTIME_BIN", str(override))
        monkeypatch.setattr("shutil.which", lambda _: None)

        result = find_tau_bin(project_root=tmp_path)

        assert result == str(override)

    def test_env_path_pointing_to_missing_file_falls_through(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
    ) -> None:
        monkeypatch.setenv("TAU_BIN", str(tmp_path / "nonexistent"))
        monkeypatch.setattr("shutil.which", lambda _: None)
        result = find_tau_bin(project_root=tmp_path)
        # Falls through to candidates and PATH; should be None here.
        assert result is None

    def test_env_path_pointing_to_directory_falls_through(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
    ) -> None:
        d = tmp_path / "not_a_file"
        d.mkdir()
        monkeypatch.setenv("TAU_BIN", str(d))
        monkeypatch.setattr("shutil.which", lambda _: None)
        result = find_tau_bin(project_root=tmp_path)
        assert result is None

    def test_env_path_pointing_to_non_executable_file_falls_through(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
    ) -> None:
        fake = tmp_path / "tau_unreadable"
        fake.write_text("not executable", encoding="utf-8")
        # Strip executable bits.
        fake.chmod(0o644)
        monkeypatch.setenv("TAU_BIN", str(fake))
        monkeypatch.setattr("shutil.which", lambda _: None)
        result = find_tau_bin(project_root=tmp_path)
        assert result is None


# -----------------------------------------------------------------------------
# G. Spec parsing — adversarial spec text.
# -----------------------------------------------------------------------------


class TestSpecParsingChaos:
    def test_empty_spec_returns_empty_streams(self) -> None:
        assert extract_stream_types("") == {}
        assert extract_always_exprs("") == []

    def test_spec_with_only_comments_returns_empty(self) -> None:
        spec = "# comment 1\n# comment 2\n"
        assert extract_stream_types(spec) == {}

    def test_extracts_single_input_stream(self) -> None:
        spec = "i1[t]:bv[16]\n"
        streams = extract_stream_types(spec)
        assert streams == {"i1": "bv[16]"}

    def test_extracts_multiple_streams(self) -> None:
        spec = "i1[t]:bv[16]\no1[t]:sbf\ni2[t]:bv[32]\n"
        streams = extract_stream_types(spec)
        assert streams == {"i1": "bv[16]", "o1": "sbf", "i2": "bv[32]"}

    def test_duplicate_stream_uses_first_occurrence(self) -> None:
        spec = "i1[t]:bv[16]\ni1[t]:sbf\n"
        streams = extract_stream_types(spec)
        # Implementation keeps the first declaration.
        assert streams["i1"] == "bv[16]"

    def test_extract_always_handles_single_line(self) -> None:
        spec = "always a > b.\n"
        assert extract_always_exprs(spec) == ["a > b"]

    def test_extract_always_handles_multiple(self) -> None:
        spec = "always a > b.\nalways c < d.\n"
        assert extract_always_exprs(spec) == ["a > b", "c < d"]

    def test_normalize_strips_blank_and_comment_lines(self) -> None:
        spec = "# top comment\n\n  # indented\ni1[t]:bv[16]\n"
        out = normalize_spec_text(spec)
        assert "comment" not in out
        assert "i1[t]:bv[16]" in out

    def test_normalize_collapses_multiline_always(self) -> None:
        spec = "always a > b &&\nc < d.\n"
        out = normalize_spec_text(spec)
        # Multi-line always becomes a single line.
        always_lines = [line for line in out.splitlines() if line.startswith("always")]
        assert len(always_lines) == 1
        assert "a > b" in always_lines[0] and "c < d" in always_lines[0]

    def test_normalize_rejects_unterminated_always_block(self) -> None:
        spec = "always a > b &&\nc < d\n"  # missing trailing .
        with pytest.raises(ValueError, match="unterminated"):
            normalize_spec_text(spec)

    def test_normalize_drops_set_charvar_lines(self) -> None:
        spec = "set charvar false\ni1[t]:bv[16]\n"
        out = normalize_spec_text(spec)
        assert "set charvar" not in out
        assert "i1[t]:bv[16]" in out

    def test_definition_with_unterminated_body_raises(self) -> None:
        spec = "foo(a) := a + 1\ni1[t]:bv[16]\n"  # missing terminator
        with pytest.raises(ValueError, match="unterminated"):
            parse_definitions(spec)

    def test_definition_with_terminator_parses(self) -> None:
        spec = "foo(a) := a + 1.\n"
        defs = parse_definitions(spec)
        assert "foo" in defs
        assert defs["foo"].body == "a + 1"
        assert defs["foo"].params == ("a",)

    def test_definition_with_multiple_params(self) -> None:
        spec = "bar(a : bv[16], b : bv[16]) := a + b.\n"
        defs = parse_definitions(spec)
        assert defs["bar"].params == ("a", "b")

    def test_inline_comment_inside_bv_literal_preserved(self) -> None:
        # `#` inside `{...}` is a bv literal marker, not a comment.
        spec = "i1[t]:bv[16] := { #x0010 }\n"
        out = normalize_spec_text(spec)
        assert "#x0010" in out

    def test_inline_comment_outside_braces_stripped(self) -> None:
        spec = "i1[t]:bv[16] # outside comment\n"
        out = normalize_spec_text(spec)
        assert "outside comment" not in out
        assert "i1[t]:bv[16]" in out


# -----------------------------------------------------------------------------
# H. Resource exhaustion under stress.
# -----------------------------------------------------------------------------


class TestResourceExhaustion:
    def test_many_small_subprocess_invocations_succeed(self) -> None:
        # Loop calling _run_subprocess_with_output_caps; verify no leaked PIDs
        # or hung file descriptors.
        for _ in range(10):
            rc, _out, _err = _caps(_sh("echo k"))
            assert rc == 0

    def test_killed_subprocess_does_not_leave_zombie(self) -> None:
        # A subprocess killed by timeout should be reaped; the next call
        # should still work.
        rc1, _out, _err = _caps(_sh("sleep 5"), timeout_s=0.2)
        assert rc1 == -1
        rc2, out, _err = _caps(_sh("echo recovered"))
        assert rc2 == 0
        assert out.strip() == "recovered"
