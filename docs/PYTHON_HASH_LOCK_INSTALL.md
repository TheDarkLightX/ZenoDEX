# Python Hash-Locked Install

Production and release-candidate Python environments should install from the
committed lockfiles with `pip --require-hashes`.

Use:

```bash
tools/install_python_hash_locked_deps.sh core
tools/install_python_hash_locked_deps.sh agents
tools/install_python_hash_locked_deps.sh dev
```

The helper maps profiles to these lockfiles:

| Profile | Lockfile | Purpose |
|---|---|---|
| `core` | `requirements-core.lock.txt` | Runtime integration dependencies |
| `agents` | `requirements-agents.lock.txt` | Agent and OpenAI SDK dependencies |
| `dev` | `requirements-dev.lock.txt` | Full local test and release-gate tooling |

Equivalent direct commands:

```bash
python3 -m pip install --require-hashes -r requirements-core.lock.txt
python3 -m pip install --require-hashes -r requirements-agents.lock.txt
python3 -m pip install --require-hashes -r requirements-dev.lock.txt
```

The unhashed `requirements*.txt` files remain source manifests for lock refresh
and local convenience. Release-candidate environments should use the lockfiles.
