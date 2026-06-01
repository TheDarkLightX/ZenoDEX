#![forbid(unsafe_code)]
//! Native ZenoDEX launcher.
//!
//! This binary is intentionally a small shell around the existing operator
//! orchestration. It gives users one stable native entrypoint while keeping the
//! current Python `zenoctl.py` lifecycle code as the behavior source of truth.

use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

const TAU_TESTNET_REPO: &str = "https://github.com/IDNI/tau-testnet.git";
const TAU_TESTNET_REF: &str = "refs/heads/main";
const TAU_TESTNET_COMMIT: &str = "638661d654a7449193f103c54fefc9f9b25f7e2d";
const TAU_TESTNET_SERVER_PATH: &str = "server.py";
const TAU_TESTNET_LOCK_REL: &str = "config/tau_testnet.lock";

#[derive(Debug, Clone, PartialEq, Eq)]
struct GlobalOptions {
    repo_root: Option<PathBuf>,
    python: Option<String>,
    dry_run: bool,
    auto_tau: bool,
    tau_repo: Option<String>,
    tau_commit: Option<String>,
    allow_unpinned_tau: bool,
}

impl Default for GlobalOptions {
    fn default() -> Self {
        Self {
            repo_root: None,
            python: None,
            dry_run: false,
            auto_tau: true,
            tau_repo: None,
            tau_commit: None,
            allow_unpinned_tau: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TauLock {
    repo: String,
    ref_name: String,
    commit: String,
    server_path: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TauSelection {
    repo: String,
    commit: Option<String>,
    server_path: PathBuf,
    pinned: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedArgs {
    globals: GlobalOptions,
    command: LauncherCommand,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LauncherCommand {
    Help,
    Version,
    Doctor(Vec<String>),
    LocalTestnet { action: String, args: Vec<String> },
    Zenoctl(Vec<String>),
}

fn main() -> ExitCode {
    match run(env::args().skip(1).collect(), &RealEnv) {
        Ok(code) => ExitCode::from(code),
        Err(err) => {
            eprintln!("error: {err}");
            ExitCode::from(2)
        }
    }
}

fn run(args: Vec<String>, env: &impl HostEnv) -> Result<u8, String> {
    let parsed = parse_args(args)?;
    match parsed.command {
        LauncherCommand::Help => {
            print_help();
            Ok(0)
        }
        LauncherCommand::Version => {
            println!("zenodex {}", env!("CARGO_PKG_VERSION"));
            Ok(0)
        }
        LauncherCommand::Doctor(extra) => {
            let repo_root = find_repo_root(parsed.globals.repo_root.as_deref(), env)?;
            run_doctor(&repo_root, &parsed.globals, extra, env)
        }
        LauncherCommand::LocalTestnet { action, args } => {
            let repo_root = find_repo_root(parsed.globals.repo_root.as_deref(), env)?;
            let with_out_dir = ensure_out_dir_arg(args, env);
            if action == "up" {
                ensure_tau_testnet(&repo_root, &parsed.globals, env)?;
            }
            run_zenoctl(
                &repo_root,
                &parsed.globals,
                vec!["testnet".to_string(), "local".to_string(), action],
                with_out_dir,
                env,
            )
        }
        LauncherCommand::Zenoctl(args) => {
            let repo_root = find_repo_root(parsed.globals.repo_root.as_deref(), env)?;
            run_zenoctl(&repo_root, &parsed.globals, Vec::new(), args, env)
        }
    }
}

fn parse_args(raw_args: Vec<String>) -> Result<ParsedArgs, String> {
    let mut globals = GlobalOptions::default();
    let mut index = 0;
    while index < raw_args.len() {
        match raw_args[index].as_str() {
            "--repo-root" => {
                index += 1;
                let value = raw_args
                    .get(index)
                    .ok_or_else(|| "--repo-root requires a value".to_string())?;
                globals.repo_root = Some(PathBuf::from(value));
            }
            arg if arg.starts_with("--repo-root=") => {
                globals.repo_root = Some(PathBuf::from(
                    arg.strip_prefix("--repo-root=").unwrap_or_default(),
                ));
            }
            "--python" => {
                index += 1;
                globals.python = Some(
                    raw_args
                        .get(index)
                        .ok_or_else(|| "--python requires a value".to_string())?
                        .clone(),
                );
            }
            arg if arg.starts_with("--python=") => {
                globals.python = Some(
                    arg.strip_prefix("--python=")
                        .unwrap_or_default()
                        .to_string(),
                );
            }
            "--dry-run" => globals.dry_run = true,
            "--no-auto-tau" => globals.auto_tau = false,
            "--allow-unpinned-tau" => globals.allow_unpinned_tau = true,
            "--tau-repo" => {
                index += 1;
                globals.tau_repo = Some(
                    raw_args
                        .get(index)
                        .ok_or_else(|| "--tau-repo requires a value".to_string())?
                        .clone(),
                );
            }
            arg if arg.starts_with("--tau-repo=") => {
                globals.tau_repo = Some(
                    arg.strip_prefix("--tau-repo=")
                        .unwrap_or_default()
                        .to_string(),
                );
            }
            "--tau-commit" => {
                index += 1;
                globals.tau_commit = Some(
                    raw_args
                        .get(index)
                        .ok_or_else(|| "--tau-commit requires a value".to_string())?
                        .clone(),
                );
            }
            arg if arg.starts_with("--tau-commit=") => {
                globals.tau_commit = Some(
                    arg.strip_prefix("--tau-commit=")
                        .unwrap_or_default()
                        .to_string(),
                );
            }
            "-h" | "--help" => {
                return Ok(ParsedArgs {
                    globals,
                    command: LauncherCommand::Help,
                })
            }
            "--version" | "-V" => {
                return Ok(ParsedArgs {
                    globals,
                    command: LauncherCommand::Version,
                })
            }
            _ => break,
        }
        index += 1;
    }

    let rest = raw_args[index..].to_vec();
    if rest.is_empty() {
        return Ok(ParsedArgs {
            globals,
            command: LauncherCommand::Help,
        });
    }

    let command = match rest[0].as_str() {
        "doctor" => LauncherCommand::Doctor(rest[1..].to_vec()),
        "local-testnet" => {
            let action = rest.get(1).cloned().unwrap_or_else(|| "status".to_string());
            LauncherCommand::LocalTestnet {
                action,
                args: rest.get(2..).unwrap_or(&[]).to_vec(),
            }
        }
        "testnet" if rest.get(1).map(String::as_str) == Some("local") => {
            let action = rest.get(2).cloned().unwrap_or_else(|| "status".to_string());
            LauncherCommand::LocalTestnet {
                action,
                args: rest.get(3..).unwrap_or(&[]).to_vec(),
            }
        }
        "zenoctl" => LauncherCommand::Zenoctl(rest[1..].to_vec()),
        _ => LauncherCommand::Zenoctl(rest),
    };

    Ok(ParsedArgs { globals, command })
}

fn run_doctor(
    repo_root: &Path,
    globals: &GlobalOptions,
    extra: Vec<String>,
    env: &impl HostEnv,
) -> Result<u8, String> {
    let python = resolve_python(globals, env);
    let zenoctl = repo_root.join("tools").join("zenoctl.py");
    let engine = pick_engine(env);
    let tau_ok = env.file_exists(&tau_testnet_path(repo_root).join("server.py"));

    if !extra.iter().any(|arg| arg == "--json") {
        println!("ZenoDEX native launcher doctor");
        println!("  repo_root: {}", repo_root.display());
        println!("  python: {}", python.as_deref().unwrap_or("missing"));
        println!("  zenoctl: {}", yes_no(env.file_exists(&zenoctl)));
        println!(
            "  container_engine: {}",
            engine.as_deref().unwrap_or("missing")
        );
        println!("  tau_testnet: {}", yes_no(tau_ok));
    }

    let mut args = vec!["doctor".to_string()];
    args.extend(extra);
    run_zenoctl(repo_root, globals, Vec::new(), args, env)
}

fn run_zenoctl(
    repo_root: &Path,
    globals: &GlobalOptions,
    prefix: Vec<String>,
    args: Vec<String>,
    env: &impl HostEnv,
) -> Result<u8, String> {
    let python = resolve_python(globals, env).ok_or_else(|| {
        "python3/python not found. Install Python 3.11+ or pass --python <path>.".to_string()
    })?;
    let zenoctl = repo_root.join("tools").join("zenoctl.py");
    if !env.file_exists(&zenoctl) {
        return Err(format!(
            "could not find tools/zenoctl.py under repo root {}",
            repo_root.display()
        ));
    }
    let mut command = vec![python, zenoctl.display().to_string()];
    command.extend(prefix);
    command.extend(args);
    run_command(command, Some(repo_root), globals.dry_run, env)
}

fn ensure_tau_testnet(
    repo_root: &Path,
    globals: &GlobalOptions,
    env: &impl HostEnv,
) -> Result<(), String> {
    let lock = load_tau_lock(repo_root, env)?;
    let selection = resolve_tau_selection(globals, &lock)?;
    let tau_path = tau_testnet_path(repo_root);
    if env.file_exists(&tau_path.join(&selection.server_path)) {
        if selection.pinned && env.file_exists(&tau_path.join(".git").join("HEAD")) {
            verify_tau_commit(
                &tau_path,
                selection.commit.as_deref().unwrap_or_default(),
                globals.dry_run,
                env,
            )?;
        }
        return Ok(());
    }
    if !globals.auto_tau {
        return Err(format!(
            "required dependency missing: {}. Run `git clone {} {}` or retry without --no-auto-tau.",
            tau_path.display(),
            selection.repo,
            tau_path.display()
        ));
    }
    if env.which("git").is_none() {
        return Err(
            "git not found; install git or clone external/tau-testnet manually".to_string(),
        );
    }
    if !selection.pinned && !globals.allow_unpinned_tau {
        return Err(
            "Tau auto-fetch is unpinned. Pass --tau-commit <40-hex-sha> or --allow-unpinned-tau for local development."
                .to_string(),
        );
    }
    let external = repo_root.join("external");
    if globals.dry_run {
        println!("mkdir -p {}", external.display());
    } else {
        std::fs::create_dir_all(&external)
            .map_err(|exc| format!("could not create {}: {exc}", external.display()))?;
    }
    match selection.commit.as_deref() {
        Some(commit) => fetch_pinned_tau(
            repo_root,
            &tau_path,
            &selection.repo,
            commit,
            globals.dry_run,
            env,
        )?,
        None => {
            run_checked_command(
                vec![
                    "git".to_string(),
                    "clone".to_string(),
                    "--depth".to_string(),
                    "1".to_string(),
                    selection.repo.clone(),
                    tau_path.display().to_string(),
                ],
                Some(repo_root),
                globals.dry_run,
                env,
            )?;
        }
    }
    if !globals.dry_run {
        if let Some(commit) = selection.commit.as_deref() {
            verify_tau_commit(&tau_path, commit, false, env)?;
        }
        if !env.file_exists(&tau_path.join(&selection.server_path)) {
            return Err(format!(
                "Tau checkout missing required {}",
                tau_path.join(&selection.server_path).display()
            ));
        }
    }
    Ok(())
}

fn load_tau_lock(repo_root: &Path, env: &impl HostEnv) -> Result<TauLock, String> {
    let path = repo_root.join(TAU_TESTNET_LOCK_REL);
    if !env.file_exists(&path) {
        return Ok(TauLock {
            repo: TAU_TESTNET_REPO.to_string(),
            ref_name: TAU_TESTNET_REF.to_string(),
            commit: TAU_TESTNET_COMMIT.to_string(),
            server_path: PathBuf::from(TAU_TESTNET_SERVER_PATH),
        });
    }
    let text = env
        .read_to_string(&path)
        .map_err(|exc| format!("could not read {}: {exc}", path.display()))?;
    parse_tau_lock(&text)
}

fn parse_tau_lock(text: &str) -> Result<TauLock, String> {
    let mut schema = None;
    let mut repo = None;
    let mut ref_name = None;
    let mut commit = None;
    let mut server_path = None;

    for raw_line in text.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (key, value) = line
            .split_once('=')
            .ok_or_else(|| format!("invalid Tau lock line: {line}"))?;
        let value = value.trim();
        match key.trim() {
            "schema" => schema = Some(value.to_string()),
            "repo" => repo = Some(value.to_string()),
            "ref" => ref_name = Some(value.to_string()),
            "commit" => commit = Some(value.to_string()),
            "server_path" => server_path = Some(PathBuf::from(value)),
            other => return Err(format!("unknown Tau lock key: {other}")),
        }
    }

    if schema.as_deref() != Some("zenodex.tau_testnet_dependency_lock.v0") {
        return Err("Tau lock has an unsupported schema".to_string());
    }
    let commit = commit.ok_or_else(|| "Tau lock missing commit".to_string())?;
    validate_commit(&commit)?;
    let server_path = server_path.ok_or_else(|| "Tau lock missing server_path".to_string())?;
    if server_path.is_absolute()
        || server_path.components().any(|part| {
            matches!(
                part,
                std::path::Component::ParentDir | std::path::Component::Prefix(_)
            )
        })
    {
        return Err(
            "Tau lock server_path must be relative and stay inside the checkout".to_string(),
        );
    }
    Ok(TauLock {
        repo: repo.ok_or_else(|| "Tau lock missing repo".to_string())?,
        ref_name: ref_name.ok_or_else(|| "Tau lock missing ref".to_string())?,
        commit,
        server_path,
    })
}

fn resolve_tau_selection(globals: &GlobalOptions, lock: &TauLock) -> Result<TauSelection, String> {
    if let Some(commit) = globals.tau_commit.as_deref() {
        validate_commit(commit)?;
    }
    let repo = globals
        .tau_repo
        .clone()
        .unwrap_or_else(|| lock.repo.clone());
    let custom_repo = globals
        .tau_repo
        .as_deref()
        .is_some_and(|value| value != lock.repo);
    let commit = if let Some(commit) = &globals.tau_commit {
        Some(commit.clone())
    } else if custom_repo {
        None
    } else {
        Some(lock.commit.clone())
    };
    Ok(TauSelection {
        repo,
        pinned: commit.is_some() && !globals.allow_unpinned_tau,
        commit,
        server_path: lock.server_path.clone(),
    })
}

fn validate_commit(commit: &str) -> Result<(), String> {
    if commit.len() != 40 || !commit.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("Tau commit must be a 40-character hex SHA-1".to_string());
    }
    Ok(())
}

fn fetch_pinned_tau(
    repo_root: &Path,
    tau_path: &Path,
    repo: &str,
    commit: &str,
    dry_run: bool,
    env: &impl HostEnv,
) -> Result<(), String> {
    run_checked_command(
        vec![
            "git".to_string(),
            "init".to_string(),
            tau_path.display().to_string(),
        ],
        Some(repo_root),
        dry_run,
        env,
    )?;
    let _ = run_command(
        vec![
            "git".to_string(),
            "-C".to_string(),
            tau_path.display().to_string(),
            "remote".to_string(),
            "remove".to_string(),
            "origin".to_string(),
        ],
        Some(repo_root),
        dry_run,
        env,
    )?;
    run_checked_command(
        vec![
            "git".to_string(),
            "-C".to_string(),
            tau_path.display().to_string(),
            "remote".to_string(),
            "add".to_string(),
            "origin".to_string(),
            repo.to_string(),
        ],
        Some(repo_root),
        dry_run,
        env,
    )?;
    run_checked_command(
        vec![
            "git".to_string(),
            "-C".to_string(),
            tau_path.display().to_string(),
            "fetch".to_string(),
            "--depth".to_string(),
            "1".to_string(),
            "origin".to_string(),
            commit.to_string(),
        ],
        Some(repo_root),
        dry_run,
        env,
    )?;
    run_checked_command(
        vec![
            "git".to_string(),
            "-C".to_string(),
            tau_path.display().to_string(),
            "checkout".to_string(),
            "--detach".to_string(),
            commit.to_string(),
        ],
        Some(repo_root),
        dry_run,
        env,
    )
}

fn verify_tau_commit(
    tau_path: &Path,
    expected_commit: &str,
    dry_run: bool,
    env: &impl HostEnv,
) -> Result<(), String> {
    if dry_run {
        println!(
            "+ git -C {} rev-parse HEAD # expect {}",
            tau_path.display(),
            expected_commit
        );
        return Ok(());
    }
    let actual = env.command_output(vec![
        "git".to_string(),
        "-C".to_string(),
        tau_path.display().to_string(),
        "rev-parse".to_string(),
        "HEAD".to_string(),
    ])?;
    let actual = actual.trim();
    if actual != expected_commit {
        return Err(format!(
            "Tau checkout is not pinned to expected commit {expected_commit}; found {actual}. Remove {} to let zenodex fetch the locked commit, or pass --allow-unpinned-tau for local development.",
            tau_path.display()
        ));
    }
    Ok(())
}

fn find_repo_root(explicit: Option<&Path>, env: &impl HostEnv) -> Result<PathBuf, String> {
    if let Some(path) = explicit {
        return validate_repo_root(path, env);
    }
    if let Some(path) = env.env_var("ZENODEX_REPO_ROOT") {
        return validate_repo_root(Path::new(&path), env);
    }
    if let Some(exe) = env.current_exe() {
        if let Some(root) = find_ancestor_with_zenoctl(exe.parent(), env) {
            return Ok(root);
        }
    }
    if let Some(cwd) = env.current_dir() {
        if let Some(root) = find_ancestor_with_zenoctl(Some(&cwd), env) {
            return Ok(root);
        }
    }
    Err("could not locate repo root; pass --repo-root <dir>".to_string())
}

fn validate_repo_root(path: &Path, env: &impl HostEnv) -> Result<PathBuf, String> {
    let root = path.to_path_buf();
    if env.file_exists(&root.join("tools").join("zenoctl.py")) {
        Ok(root)
    } else {
        Err(format!(
            "{} is not a ZenoDEX operator bundle root (missing tools/zenoctl.py)",
            root.display()
        ))
    }
}

fn find_ancestor_with_zenoctl(start: Option<&Path>, env: &impl HostEnv) -> Option<PathBuf> {
    let mut current = start?;
    loop {
        if env.file_exists(&current.join("tools").join("zenoctl.py")) {
            return Some(current.to_path_buf());
        }
        current = current.parent()?;
    }
}

fn ensure_out_dir_arg(args: Vec<String>, env: &impl HostEnv) -> Vec<String> {
    let has_out_dir = args
        .iter()
        .any(|arg| arg == "--out-dir" || arg.starts_with("--out-dir="));
    if has_out_dir {
        return args;
    }
    let mut out = args;
    out.push("--out-dir".to_string());
    out.push(default_out_dir(env).display().to_string());
    out
}

fn default_out_dir(env: &impl HostEnv) -> PathBuf {
    if let Some(path) = env.env_var("ZENODEX_LOCAL_TESTNET_DIR") {
        return PathBuf::from(path);
    }
    let base = env
        .env_var("HOME")
        .or_else(|| env.env_var("USERPROFILE"))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));
    base.join(".zenodex").join("local-testnet")
}

fn tau_testnet_path(repo_root: &Path) -> PathBuf {
    repo_root.join("external").join("tau-testnet")
}

fn resolve_python(globals: &GlobalOptions, env: &impl HostEnv) -> Option<String> {
    if let Some(python) = &globals.python {
        return Some(python.clone());
    }
    env.which("python3").or_else(|| env.which("python"))
}

fn pick_engine(env: &impl HostEnv) -> Option<String> {
    env.which("docker").or_else(|| env.which("podman"))
}

fn run_command(
    command: Vec<String>,
    cwd: Option<&Path>,
    dry_run: bool,
    env: &impl HostEnv,
) -> Result<u8, String> {
    if dry_run {
        println!("+ {}", shell_join(&command));
        return Ok(0);
    }
    env.run_command(command, cwd)
}

fn run_checked_command(
    command: Vec<String>,
    cwd: Option<&Path>,
    dry_run: bool,
    env: &impl HostEnv,
) -> Result<(), String> {
    let printable = shell_join(&command);
    let code = run_command(command, cwd, dry_run, env)?;
    if code == 0 {
        Ok(())
    } else {
        Err(format!("command failed with exit code {code}: {printable}"))
    }
}

fn shell_join(parts: &[String]) -> String {
    parts
        .iter()
        .map(|part| shell_quote(part))
        .collect::<Vec<_>>()
        .join(" ")
}

fn shell_quote(part: &str) -> String {
    if part
        .chars()
        .all(|ch| ch.is_ascii_alphanumeric() || "-_./:=+".contains(ch))
    {
        part.to_string()
    } else {
        format!("'{}'", part.replace('\'', "'\\''"))
    }
}

fn yes_no(value: bool) -> &'static str {
    if value {
        "ok"
    } else {
        "missing"
    }
}

fn print_help() {
    println!(
        "\
ZenoDEX native launcher

Usage:
  zenodex [global options] doctor [zenoctl doctor options]
  zenodex [global options] local-testnet <up|down|status|smoke|logs|reset> [options]
  zenodex [global options] testnet local <up|down|status|smoke|logs|reset> [options]
  zenodex [global options] zenoctl <args...>

Global options:
  --repo-root DIR       Operator bundle or repo root. Defaults to auto-discovery.
  --python PATH         Python interpreter for the existing zenoctl orchestrator.
  --dry-run             Print commands without running them.
  --no-auto-tau         Refuse instead of cloning external/tau-testnet on `up`.
  --tau-repo URL        Tau testnet Git URL. Default comes from {TAU_TESTNET_LOCK_REL}.
  --tau-commit SHA      Pin a custom Tau checkout to a 40-hex commit.
  --allow-unpinned-tau  Allow a custom or existing Tau checkout without commit verification.
  -h, --help            Show this help.
  -V, --version         Print launcher version.

Convenience:
  local-testnet commands default --out-dir to ~/.zenodex/local-testnet.
  `local-testnet up` clones external/tau-testnet when missing, unless
  --no-auto-tau is set. The default clone is pinned by {TAU_TESTNET_LOCK_REL}.
"
    );
}

trait HostEnv {
    fn env_var(&self, key: &str) -> Option<String>;
    fn current_exe(&self) -> Option<PathBuf>;
    fn current_dir(&self) -> Option<PathBuf>;
    fn which(&self, name: &str) -> Option<String>;
    fn file_exists(&self, path: &Path) -> bool;
    fn read_to_string(&self, path: &Path) -> Result<String, String>;
    fn command_output(&self, command: Vec<String>) -> Result<String, String>;
    fn run_command(&self, command: Vec<String>, cwd: Option<&Path>) -> Result<u8, String>;
}

struct RealEnv;

impl HostEnv for RealEnv {
    fn env_var(&self, key: &str) -> Option<String> {
        env::var(key).ok()
    }

    fn current_exe(&self) -> Option<PathBuf> {
        env::current_exe().ok()
    }

    fn current_dir(&self) -> Option<PathBuf> {
        env::current_dir().ok()
    }

    fn which(&self, name: &str) -> Option<String> {
        which_on_path(name, env::var_os("PATH"))?.into_string().ok()
    }

    fn file_exists(&self, path: &Path) -> bool {
        path.is_file()
    }

    fn read_to_string(&self, path: &Path) -> Result<String, String> {
        std::fs::read_to_string(path).map_err(|exc| exc.to_string())
    }

    fn command_output(&self, command: Vec<String>) -> Result<String, String> {
        let mut iter = command.into_iter();
        let program = iter
            .next()
            .ok_or_else(|| "internal error: empty command".to_string())?;
        let output = Command::new(program)
            .args(iter)
            .output()
            .map_err(|exc| format!("failed to execute command: {exc}"))?;
        if !output.status.success() {
            return Err(format!(
                "command failed with exit code {}",
                output.status.code().unwrap_or(1)
            ));
        }
        String::from_utf8(output.stdout).map_err(|exc| exc.to_string())
    }

    fn run_command(&self, command: Vec<String>, cwd: Option<&Path>) -> Result<u8, String> {
        let mut iter = command.into_iter();
        let program = iter
            .next()
            .ok_or_else(|| "internal error: empty command".to_string())?;
        let mut cmd = Command::new(program);
        cmd.args(iter);
        if let Some(cwd) = cwd {
            cmd.current_dir(cwd);
        }
        let status = cmd
            .status()
            .map_err(|exc| format!("failed to execute command: {exc}"))?;
        Ok(status.code().unwrap_or(1).try_into().unwrap_or(1))
    }
}

fn which_on_path(name: &str, path: Option<OsString>) -> Option<OsString> {
    let candidate = Path::new(name);
    if candidate.components().count() > 1 && candidate.is_file() {
        return Some(OsString::from(name));
    }
    let path = path?;
    for dir in env::split_paths(&path) {
        let direct = dir.join(name);
        if direct.is_file() {
            return Some(direct.into_os_string());
        }
        #[cfg(windows)]
        {
            for suffix in [".exe", ".cmd", ".bat"] {
                let with_suffix = dir.join(format!("{name}{suffix}"));
                if with_suffix.is_file() {
                    return Some(with_suffix.into_os_string());
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::collections::{BTreeMap, BTreeSet};

    #[derive(Default)]
    struct FakeEnv {
        vars: BTreeMap<String, String>,
        bins: BTreeMap<String, String>,
        files: BTreeSet<PathBuf>,
        texts: BTreeMap<PathBuf, String>,
        outputs: BTreeMap<String, String>,
        current_exe: Option<PathBuf>,
        current_dir: Option<PathBuf>,
        commands: RefCell<Vec<Vec<String>>>,
    }

    impl FakeEnv {
        fn with_repo(root: &str) -> Self {
            let root = PathBuf::from(root);
            let mut env = Self::default();
            env.files.insert(root.join("tools").join("zenoctl.py"));
            env.current_dir = Some(root);
            env.bins
                .insert("python3".to_string(), "/usr/bin/python3".to_string());
            env
        }

        fn with_tau(mut self) -> Self {
            let root = self.current_dir.clone().unwrap();
            self.files
                .insert(root.join("external").join("tau-testnet").join("server.py"));
            self
        }
    }

    impl HostEnv for FakeEnv {
        fn env_var(&self, key: &str) -> Option<String> {
            self.vars.get(key).cloned()
        }

        fn current_exe(&self) -> Option<PathBuf> {
            self.current_exe.clone()
        }

        fn current_dir(&self) -> Option<PathBuf> {
            self.current_dir.clone()
        }

        fn which(&self, name: &str) -> Option<String> {
            self.bins.get(name).cloned()
        }

        fn file_exists(&self, path: &Path) -> bool {
            self.files.contains(path) || self.texts.contains_key(path)
        }

        fn read_to_string(&self, path: &Path) -> Result<String, String> {
            self.texts
                .get(path)
                .cloned()
                .ok_or_else(|| format!("missing fake file: {}", path.display()))
        }

        fn command_output(&self, command: Vec<String>) -> Result<String, String> {
            self.outputs
                .get(&shell_join(&command))
                .cloned()
                .ok_or_else(|| format!("missing fake output: {}", shell_join(&command)))
        }

        fn run_command(&self, command: Vec<String>, _cwd: Option<&Path>) -> Result<u8, String> {
            self.commands.borrow_mut().push(command);
            Ok(0)
        }
    }

    #[test]
    fn parses_local_testnet_alias() {
        let parsed = parse_args(vec![
            "--dry-run".to_string(),
            "local-testnet".to_string(),
            "up".to_string(),
            "--ui-port".to_string(),
            "18081".to_string(),
        ])
        .unwrap();
        assert!(parsed.globals.dry_run);
        assert_eq!(
            parsed.command,
            LauncherCommand::LocalTestnet {
                action: "up".to_string(),
                args: vec!["--ui-port".to_string(), "18081".to_string()]
            }
        );
    }

    #[test]
    fn default_out_dir_is_inserted_for_local_testnet() {
        let mut env = FakeEnv::with_repo("/repo").with_tau();
        env.vars
            .insert("HOME".to_string(), "/home/alice".to_string());
        run(
            vec![
                "--dry-run".to_string(),
                "local-testnet".to_string(),
                "status".to_string(),
            ],
            &env,
        )
        .unwrap();
        let commands = env.commands.borrow();
        assert_eq!(
            commands.len(),
            0,
            "dry-run prints instead of recording commands"
        );
        let args = ensure_out_dir_arg(Vec::new(), &env);
        assert_eq!(
            args,
            vec![
                "--out-dir".to_string(),
                "/home/alice/.zenodex/local-testnet".to_string()
            ]
        );
    }

    #[test]
    fn explicit_out_dir_is_preserved() {
        let env = FakeEnv::default();
        let args = ensure_out_dir_arg(vec!["--out-dir".to_string(), "/tmp/zeno".to_string()], &env);
        assert_eq!(args, vec!["--out-dir".to_string(), "/tmp/zeno".to_string()]);
    }

    #[test]
    fn up_fetches_tau_when_missing_and_auto_tau_enabled() {
        let mut env = FakeEnv::with_repo("/repo");
        env.bins
            .insert("git".to_string(), "/usr/bin/git".to_string());
        run(
            vec![
                "--dry-run".to_string(),
                "local-testnet".to_string(),
                "up".to_string(),
            ],
            &env,
        )
        .unwrap();
    }

    #[test]
    fn tau_lock_parser_rejects_unpinned_commit_text() {
        let err = parse_tau_lock(
            "\
schema=zenodex.tau_testnet_dependency_lock.v0
repo=https://github.com/IDNI/tau-testnet.git
ref=refs/heads/main
commit=not-a-commit
server_path=server.py
",
        )
        .unwrap_err();
        assert!(err.contains("40-character"));
    }

    #[test]
    fn custom_tau_repo_requires_pin_or_explicit_unpinned_escape() {
        let lock = TauLock {
            repo: TAU_TESTNET_REPO.to_string(),
            ref_name: TAU_TESTNET_REF.to_string(),
            commit: TAU_TESTNET_COMMIT.to_string(),
            server_path: PathBuf::from(TAU_TESTNET_SERVER_PATH),
        };
        let globals = GlobalOptions {
            tau_repo: Some("https://example.invalid/tau-testnet.git".to_string()),
            ..GlobalOptions::default()
        };
        let selected = resolve_tau_selection(&globals, &lock).unwrap();
        assert_eq!(selected.commit, None);
        assert!(!selected.pinned);
    }

    #[test]
    fn up_rejects_missing_tau_when_auto_tau_disabled() {
        let env = FakeEnv::with_repo("/repo");
        let err = run(
            vec![
                "--no-auto-tau".to_string(),
                "local-testnet".to_string(),
                "up".to_string(),
            ],
            &env,
        )
        .unwrap_err();
        assert!(err.contains("required dependency missing"));
    }
}
