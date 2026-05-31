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

#[derive(Debug, Clone, PartialEq, Eq)]
struct GlobalOptions {
    repo_root: Option<PathBuf>,
    python: Option<String>,
    dry_run: bool,
    auto_tau: bool,
    tau_repo: String,
}

impl Default for GlobalOptions {
    fn default() -> Self {
        Self {
            repo_root: None,
            python: None,
            dry_run: false,
            auto_tau: true,
            tau_repo: TAU_TESTNET_REPO.to_string(),
        }
    }
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
            "--tau-repo" => {
                index += 1;
                globals.tau_repo = raw_args
                    .get(index)
                    .ok_or_else(|| "--tau-repo requires a value".to_string())?
                    .clone();
            }
            arg if arg.starts_with("--tau-repo=") => {
                globals.tau_repo = arg
                    .strip_prefix("--tau-repo=")
                    .unwrap_or_default()
                    .to_string();
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
    let tau_path = tau_testnet_path(repo_root);
    if env.file_exists(&tau_path.join("server.py")) {
        return Ok(());
    }
    if !globals.auto_tau {
        return Err(format!(
            "required dependency missing: {}. Run `git clone {} {}` or retry without --no-auto-tau.",
            tau_path.display(),
            globals.tau_repo,
            tau_path.display()
        ));
    }
    if env.which("git").is_none() {
        return Err(
            "git not found; install git or clone external/tau-testnet manually".to_string(),
        );
    }
    let external = repo_root.join("external");
    if globals.dry_run {
        println!("mkdir -p {}", external.display());
    } else {
        std::fs::create_dir_all(&external)
            .map_err(|exc| format!("could not create {}: {exc}", external.display()))?;
    }
    run_command(
        vec![
            "git".to_string(),
            "clone".to_string(),
            "--depth".to_string(),
            "1".to_string(),
            globals.tau_repo.clone(),
            tau_path.display().to_string(),
        ],
        Some(repo_root),
        globals.dry_run,
        env,
    )?;
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
  --tau-repo URL        Tau testnet Git URL. Default: {TAU_TESTNET_REPO}
  -h, --help            Show this help.
  -V, --version         Print launcher version.

Convenience:
  local-testnet commands default --out-dir to ~/.zenodex/local-testnet.
  `local-testnet up` clones external/tau-testnet when missing, unless
  --no-auto-tau is set.
"
    );
}

trait HostEnv {
    fn env_var(&self, key: &str) -> Option<String>;
    fn current_exe(&self) -> Option<PathBuf>;
    fn current_dir(&self) -> Option<PathBuf>;
    fn which(&self, name: &str) -> Option<String>;
    fn file_exists(&self, path: &Path) -> bool;
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
            self.files.contains(path)
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
